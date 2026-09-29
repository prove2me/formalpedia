-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000022_000025_data
-- name    : GeneralCK_RB2_cells000022_000025_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T01:43:34.167174+00:00
-- url     : https://prove2.me/theorems/70f30651-b7de-4366-8dde-50cda81fde6b
-- title:
--   Exact certificate data for RB2 cells 000022–000025
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000022 through 000025. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000022Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2525295488000,-2525295430144⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-116561173120,-116561173056⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2088440400320,-2088440361600⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2088440400320,-2088440361600⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-178244726784,-178244726720⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-178244726784,-178244726720⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨95102982656,95102982720⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-104114591104,-104114591040⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨95103105472,95103105536⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-104114738304,-104114738240⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-9011632768,-9011632704⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-9011608384,-9011608320⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨199217573696,199217573760⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨199217843712,199217843776⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1910195634880,1910195673472⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1910195634880,1910195673472⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2095228324672,-2095228285888⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2081689110912,-2081689072192⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-179437206144,-179437206080⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-177054426240,-177054426176⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨92511164672,92511164736⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-101015964160,-101015964096⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨97716674560,97716674624⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-107255675008,-107255674944⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-9539000384,-9539000320⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-8504799488,-8504799424⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨193527128832,193527128896⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨204972349568,204972349632⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1902251866112,1902251904704⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1918173859712,1918173898304⟩



end LaneCBRB2Cell000022Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000022
open Set LaneCBRB2Cell000022Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110595407872,110595407872⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨135076721459,135076721460⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110595407872,-110595407872⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439160406016,439160406016⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨53951542067,53951542068⟩,⟨-135076721460,-135076721459⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨164546949939,164546949940⟩,⟨964434906316,964434906317⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨53951542067,53951542068⟩,⟨-135076721460,-135076721459⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2088440400320,-2088440361600⟩,⟨6444406256779,6444406256827⟩,⟨2934493608355,2934493608375⟩,⟨-37771653299415,-37771653298861⟩,⟨-24546513255897,-24546513255617⟩,⟨-7831888740465,-7831888740366⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312544669218,-312544663421⟩,⟨-867437327644,-867437293664⟩,⟨-394992058568,-394992043096⟩,⟨5652700878661,5652700878876⟩,⟨3562915217201,3562915256027⟩,⟨1172078013477,1172078013517⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨312544663421,312544669218⟩,⟨867437293664,867437327644⟩,⟨394992043096,394992058568⟩,⟨-5652700878876,-5652700878661⟩,⟨-3562915256027,-3562915217201⟩,⟨-1172078013517,-1172078013477⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164546949940,-164546949939⟩,⟨-964434906317,-964434906316⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨934964677836,934964677837⟩,⟨-964434906317,-964434906316⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-178244726784,-178244726720⟩,⟨-1134168401082,-1134168401078⟩,⟨-516449427792,-516449427790⟩,⟨-1169917561141,-1169917561131⟩,⟨760289646179,760289646187⟩,⟨-242580437286,-242580437283⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151569587210,-151569587154⟩,⟨-808087822785,-808087822722⟩,⟨-367966955600,-367966955570⟩,⟨994834040859,994834040879⟩,⟨1374269709619,1374269709698⟩,⟨206277164027,206277164033⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151569587154,151569587210⟩,⟨808087822722,808087822785⟩,⟨367966955570,367966955600⟩,⟨-994834040879,-994834040859⟩,⟨-1374269709698,-1374269709619⟩,⟨-206277164033,-206277164027⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨464114250575,464114256428⟩,⟨1675525116386,1675525150429⟩,⟨762958998666,762959014168⟩,⟨-6647534919755,-6647534919520⟩,⟨-4937184965725,-4937184926820⟩,⟨-1378355177550,-1378355177504⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨822960217068,822960228799⟩,⟨4084259373408,4084259465375⟩,⟨762958998666,762959014168⟩,⟨-18801077445369,-18801077445124⟩,⟨-4937184965725,-4937184926820⟩,⟨-1378355177550,-1378355177504⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨107903084134,107903084136⟩,⟨-270153442920,-270153442918⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11203811543430,11203811543638⟩,⟨28050618631503,28050618632754⟩,⟨-91197957239493,-91197957236105⟩,⟨140458843414137,140458843424042⟩,⟨-228329359947459,-228329359910158⟩,⟨1484685345125368,1484685345208075⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8385805976804,8385806096497⟩,⟨62613085458018,62613086696135⟩,⟨-60485256580612,-60485255446950⟩,⟨121945336924162,121945343138024⟩,⟨-540508990881033,-540508979982577⟩,⟨970643245776431,970643264255895⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨99337175040,99337308928⟩,⟨-733001256169,-732999235514⟩,⟨708089142679,708091093935⟩,⟨9326023548540,9326073042800⟩,⟨-4060579473774,-4060518071109⟩,⟨-1328023512585,-1327949743598⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1198848802816,1198848936704⟩,⟨-733001256169,-732999235514⟩,⟨708089142679,708091093935⟩,⟨9326023548540,9326073042800⟩,⟨-4060579473774,-4060518071109⟩,⟨-1328023512585,-1327949743598⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨95102982656,95103105536⟩,⟨-672264427708,-672262499405⟩,⟨649416471117,649418333220⟩,⟨8142227355465,8142276061863⟩,⟨-3327052263691,-3326993255503⟩,⟨-1601556949910,-1601486957763⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨103695217059,103695362622⟩,⟨-796402846542,-796400405462⟩,⟨769335700517,769338057847⟩,⟨10580850329821,10580914793461⟩,⟨-4844747031691,-4844671652557⟩,⟨-1024668110580,-1024580367348⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-99337308928,-99337175040⟩,⟨732999235514,733001256169⟩,⟨-708091093935,-708089142679⟩,⟨-9326073042800,-9326023548540⟩,⟨4060518071109,4060579473774⟩,⟨1327949743598,1328023512585⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1000174318848,1000174452736⟩,⟨732999235514,733001256169⟩,⟨-708091093935,-708089142679⟩,⟨-9326073042800,-9326023548540⟩,⟨4060518071109,4060579473774⟩,⟨1327949743598,1328023512585⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-104114738304,-104114591040⟩,⟨805800608477,805802937693⟩,⟨-778418698256,-778416448997⟩,⟨-10842890197476,-10842831000983⟩,⟨5034287250818,5034358646972⟩,⟨908746229547,908830705494⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-94708322109,-94708175470⟩,⟨663589926941,663592433360⟩,⟨-641041046054,-641038625612⟩,⟨-7905786498279,-7905719326507⟩,⟨3157069736882,3157147513937⟩,⟨1703496575557,1703586353140⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8986894950,8987187152⟩,⟨-132812919601,-132807972102⟩,⟨128294654463,128299432235⟩,⟨2675063831542,2675195466954⟩,⟨-1687677294809,-1687524138620⟩,⟨678828464977,679005985792⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4493447475,4493593576⟩,⟨-66406459801,-66403986051⟩,⟨64147327231,64149716118⟩,⟨1337531915771,1337597733477⟩,⟨-843838647405,-843762069310⟩,⟨339414232488,339502992896⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4493593576,-4493447475⟩,⟨66403986051,66406459801⟩,⟨-64149716118,-64147327231⟩,⟨-1337597733477,-1337531915771⟩,⟨843762069310,843838647405⟩,⟨-339502992896,-339414232488⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757629790040,757629955405⟩,⟨66403986051,66406459801⟩,⟨-64149716118,-64147327231⟩,⟨-1337597733477,-1337531915771⟩,⟨843762069310,843838647405⟩,⟨-339502992896,-339414232488⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8974779434,8974803628⟩,⟨-132448571510,-132448027874⟩,⟨127946941774,127947466804⟩,⟨2662470638701,2662487241622⟩,⟨-1677833459234,-1677816170998⟩,⟨672058289720,672076969180⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8974803628,-8974779434⟩,⟨132448027874,132448571510⟩,⟨-127947466804,-127946941774⟩,⟨-2662487241622,-2662470638701⟩,⟨1677816170998,1677833459234⟩,⟨-672076969180,-672058289720⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090536824148,1090536848342⟩,⟨132448027874,132448571510⟩,⟨-127947466804,-127946941774⟩,⟨-2662487241622,-2662470638701⟩,⟨1677816170998,1677833459234⟩,⟨-672076969180,-672058289720⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9011632768,-9011608320⟩,⟨133538033992,133538585065⟩,⟨-129000437565,-128999905351⟩,⟨-2700617357059,-2700600424082⟩,⟨1707291390632,1707308987971⟩,⟨-692742972864,-692723999758⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4505816384,-4505804160⟩,⟨66769016996,66769292533⟩,⟨-64500218783,-64499952675⟩,⟨-1350308678530,-1350300212041⟩,⟨853645695316,853654493986⟩,⟨-346371486432,-346361999879⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4505804160,4505816384⟩,⟨-66769292533,-66769016996⟩,⟨64499952675,64500218783⟩,⟨1350300212041,1350308678530⟩,⟨-853654493986,-853645695316⟩,⟨346361999879,346371486432⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766629187776,766629219264⟩,⟨-66769292533,-66769016996⟩,⟨64499952675,64500218783⟩,⟨1350300212041,1350308678530⟩,⟨-853654493986,-853645695316⟩,⟨346361999879,346371486432⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272634206037,272634212086⟩,⟨33112006968,33112142878⟩,⟨-31986866701,-31986735443⟩,⟨-665621810406,-665617659675⟩,⟨419454042749,419458364809⟩,⟨-168019242295,-168014572430⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533258375552,1533258438528⟩,⟨-133538585066,-133538033992⟩,⟨128999905350,129000437566⟩,⟨2700600424082,2700617357060⟩,⟨-1707308987972,-1707291390632⟩,⟨692723999758,692742972864⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1208714955983,1208715117788⟩,⟨-885835281904,-885832602767⟩,⟨855728652719,855731239927⟩,⟨12568940698109,12569011209672⟩,⟨-6161513876554,-6161430939599⟩,⟨-393269368266,-393172624022⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1317918284190,1317918607800⟩,⟨-1771670563808,-1771665205535⟩,⟨1711457305438,1711462479854⟩,⟨25137881396227,25138022419337⟩,⟨-12323027753104,-12322861879202⟩,⟨-786538588987,-786345395589⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨199217573696,199217843776⟩,⟨-1478067653256,-1478062820027⟩,⟨1427832642041,1427837309549⟩,⟨18985044409509,18985180206299⟩,⟨-8361422438749,-8361268978259⟩,⟨-2510397151787,-2510223690961⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨68449301642,68449408840⟩,⟨-499082784371,-499081050193⟩,⟨482120384121,482122058791⟩,⟨6216803619110,6216848777933⟩,⟨-2636224800782,-2636171437189⟩,⟨-1028386935676,-1028324539525⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380185774582,380185798634⟩,⟨13062231202,13062560005⟩,⟨-12618644649,-12618327099⟩,⟨-266607187449,-266597081415⟩,⟨169351073973,169361561837⟩,⟨-70039553075,-70028261231⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179828978247,3179829179416⟩,⟨-109253718153,-109250954259⟩,⟨105538192932,105540862237⟩,⟨2237293582512,2237378769698⟩,⟨-1423772639805,-1423684374888⟩,⟨592713683803,592808555508⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨197957954607,197958277153⟩,⟨-1450167795256,-1450162505915⟩,⟨1400880486502,1400885594388⟩,⟨18217691508997,18217831622627⟩,⟨-7808510595589,-7808347393635⟩,⟨-2844680893607,-2844491627062⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨397175528303,397176120929⟩,⟨-2928235448512,-2928225325942⟩,⟨2828713128543,2828722903937⟩,⟨37202735918506,37203011828926⟩,⟨-16169933034338,-16169616371894⟩,⟨-5355078045394,-5354715318023⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522052595220,522052823114⟩,⟨91512698434,91516127538⟩,⟨-88406061990,-88402750518⟩,⟨-1835350525291,-1835258820598⟩,⟨1155057041378,1155163406258⟩,⟨-460391234406,-460268252242⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359725707409,359725942958⟩,⟨94586648402,94590213337⟩,⟨-91375678680,-91372236029⟩,⟨-1888710897841,-1888615077992⟩,⟨1185846790185,1185957588020⟩,⟨-468119729667,-467991933576⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨719451414818,719451885916⟩,⟨189173296804,189180426674⟩,⟨-182751357360,-182744472058⟩,⟨-3777421795682,-3777230155984⟩,⟨2371693580370,2371915176040⟩,⟨-936239459334,-935983867152⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524283571924,1524283659094⟩,⟨-1090557192,-1089462482⟩,⟨1052438546,1053495792⟩,⟨38113182460,38146718359⟩,⟨-29492816974,-29457931398⟩,⟨20647030578,20684683144⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨997395520611,997396230747⟩,⟨261542613894,261553230008⟩,⟨-252664657912,-252654405888⟩,⟨-5212181675025,-5211893349128⟩,⟨3269008708154,3269339317527⟩,⟨-1284774979535,-1284395559777⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67602204855,67602207855⟩,⟨16420864502,16420932270⟩,⟨-15862886722,-15862821276⟩,⟨-328099982330,-328097900207⟩,⟨206088527580,206090691402⟩,⟨-81462790139,-81460457140⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50598760191,50598763159⟩,⟨263406634127,263406701825⟩,⟨35036633231,35036685423⟩,⟨-1279543941897,-1279541822445⟩,⟨-196834338372,-196832409045⟩,⟨-167734428446,-167732586338⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2138114037916,2138114213556⟩,⟨-372436556830,-372435004596⟩,⟨359778251228,359779750346⟩,⟨7564359522376,7564407325208⟩,⟨-4792986963164,-4792937430356⟩,⟨1962263650339,1962316895093⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2981579433726,2981579801119⟩,⟨-779038819350,-779035540489⟩,⟨752560959476,752564126147⟩,⟨15890489291911,15890590495472⟩,⟨-10091205948570,-10091101383655⟩,⟨4167852972311,4167965039901⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137210211285,137210236241⟩,⟨678437029189,678437453778⟩,⟨129642245688,129642546688⟩,⟨-3111773736968,-3111761194874⟩,⟨-842687964881,-842676881619⟩,⟨-215087298882,-215076805747⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8810755325070,8810756927585⟩,⟨-43564888063558,-43564844951887⟩,⟨-8324810199211,-8324787842673⟩,⟨630630606440811,630632258806681⟩,⟨136435217955455,136436236913589⟩,⟨29542092515714,29542852973825⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7992464720177,7992471864420⟩,⟨-37423039584073,-37422886887633⟩,⟨-9576343654256,-9576235476195⟩,⟨509567873311682,509572959341785⟩,⟨157989943679728,157994111980329⟩,⟨20328934030103,20332850750617⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15984929440354,15984943728840⟩,⟨-74846079168146,-74845773775266⟩,⟨-19152687308512,-19152470952390⟩,⟨1019135746623364,1019145918683570⟩,⟨315979887359456,315988223960658⟩,⟨40657868060206,40665701501234⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10931067056724,10931067056725⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603222,2160817149603840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9831555428948,9831555428949⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603232,2160817149603830⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2408734257088,2408734314944⟩,⟨-12153542525660,-12153542525558⟩,⟨0,0⟩,⟨107314718406763,107314718418708⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7346996222387,7346996222433⟩,⟨-43061871496985,-43061871496400⟩,⟨-19608445159501,-19608445159254⟩,⟨504784464465141,504784464475675⟩,⟨278949234445296,278949234450470⟩,⟨104666209135078,104666209137046⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6247484594611,6247484594657⟩,⟨-43061871496985,-43061871496400⟩,⟨-19608445159502,-19608445159253⟩,⟨504784464465148,504784464475672⟩,⟨278949234445299,278949234450469⟩,⟨104666209135079,104666209137046⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1910195634880,1910195673472⟩,⟨-7578574657994,-7578574657773⟩,⟨-3450943036205,-3450943036107⟩,⟨36601735734728,36601735742469⟩,⟨25306802900360,25306802904065⟩,⟨7589308302468,7589308304042⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99471065088,99471065088⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139921745393,139921745395⟩,⟨675770706244,675770706249⟩,⟨307715674520,307715674522⟩,⟨-1691905142294,-1691905142289⟩,⟨-1540835455796,-1540835455792⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4318929891968,4318929988416⟩,⟨-19732117183654,-19732117183331⟩,⟨-3450943036205,-3450943036107⟩,⟨143916454141491,143916454161177⟩,⟨25306802900360,25306802904065⟩,⟨7589308302468,7589308304042⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨794351056606,794352241858⟩,⟨-5856470897024,-5856450651884⟩,⟨5657426257086,5657445807874⟩,⟨74405471837012,74406023657852⟩,⟨-32339866068676,-32339232743788⟩,⟨-10710156090788,-10709430636046⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5113280948574,5113282230274⟩,⟨-25588588080678,-25588567835215⟩,⟨2206483220881,2206502771767⟩,⟨218321925978503,218322477819029⟩,⟨-7033063168316,-7032429839723⟩,⟨-3120847788320,-3120122332004⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨462590380310,462590496264⟩,⟨1769673839967,1769676695402⟩,⟨199617021353,199618790091⟩,⟨-31357095350337,-31357010517512⟩,⟨1126330835282,1126403749309⟩,⟨-282338126892,-282272496014⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨40464604635,40464606904⟩,⟨-814083964069,-814083952693⟩,⟨329378021832,329378040293⟩,⟨10160988778849,10160988807940⟩,⟨-6626565812353,-6626565719884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨503054984945,503055103168⟩,⟨955589875898,955592742709⟩,⟨528995043185,528996830384⟩,⟨-21196106571488,-21196021709572⟩,⟨-5500234977071,-5500161970575⟩,⟨-282338126892,-282272496014⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501892554988,501892567044⟩,⟨2532355881864,2532356003553⟩,⟨0,0⟩,⟨3194096148032,3194099067279⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229628814571,229628874053⟩,⟨1594815052486,1594816699538⟩,⟨241469637148,241470458750⟩,⟨-3812215311958,-3812161246675⟩,⟨-1292322251995,-1292284691749⟩,⟨-128878498145,-128848536612⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-794352241858,-794351056606⟩,⟨5856450651884,5856470897024⟩,⟨-5657445807874,-5657426257086⟩,⟨-74406023657852,-74405471837012⟩,⟨32339232743788,32339866068676⟩,⟨10709430636046,10710156090788⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3524577650110,3524578931810⟩,⟨-13875666531770,-13875646286307⟩,⟨-9108388844079,-9108369293193⟩,⟨69510430483639,69510982324165⟩,⟨57646035644148,57646668972741⟩,⟨18298738938514,18299464394830⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨448531006055,448531169170⟩,⟨400449469618,400452833806⟩,⟨-172707473939,-172704627201⟩,⟨-13634026260263,-13633929175446⟩,⟨-7084786112310,-7084686037606⟩,⟨-3894153507431,-3894049834988⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨329093899878,329093899880⟩,⟨1928869812632,1928869812634⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-329093899880,-329093899878⟩,⟨-1928869812634,-1928869812632⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨770417727896,770417727898⟩,⟨-1928869812634,-1928869812632⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1338456587164,1338456614210⟩,⟨-8661288156420,-8661288088544⟩,⟨-3943962208835,-3943962177930⟩,⟨52236640696820,52236640703115⟩,⟨33660593462155,33660593542338⟩,⟨10831179532204,10831179533479⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1338456614210,-1338456587164⟩,⟨8661288088544,8661288156420⟩,⟨3943962177930,3943962208835⟩,⟨-52236640703115,-52236640696820⟩,⟨-33660593542338,-33660593462155⟩,⟨-10831179533479,-10831179532204⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-238944986434,-238944959388⟩,⟨8661288088544,8661288156420⟩,⟨3943962177930,3943962208835⟩,⟨-52236640703115,-52236640696820⟩,⟨-33660593542338,-33660593462155⟩,⟨-10831179533479,-10831179532204⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11724705917,-11724704589⟩,⟨454352403163,454352409827⟩,⟨98086879092,98086891417⟩,⟨-4691286570929,-4691286553877⟩,⟨1562183698812,1562183760737⟩,⟨2619076644346,2619076669108⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨436806300138,436806464581⟩,⟨854801872781,854805243633⟩,⟨-74620594847,-74617735784⟩,⟨-18325312831192,-18325215729323⟩,⟨-5522602413498,-5522502276869⟩,⟨-1275076863085,-1274973165880⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99471065088,-99471065088⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4880910048,4880910049⟩,⟨30877833420,30877833423⟩,⟨39730142208,39730142208⟩,⟨-323709252407,-323709252402⟩,⟨251342618624,251342618624⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10692761169,10692761429⟩,⟨13693486197,13693487841⟩,⟨87038055949,87038058040⟩,⟨-915393884663,-915393867394⟩,⟨111463671483,111463684713⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1468996650517,1468996671458⟩,⟨-7290466094930,-7290465722908⟩,⟨-1361893599506,-1361893533004⟩,⟨105923740507817,105923747818725⟩,⟨22330800849041,22330802326916⟩,⟨4985583565105,4985583845947⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14286006573,14286007125⟩,⟨-52604745455,-52604737653⟩,⟨103042302094,103042307515⟩,⟨-374490926260,-374490758536⟩,⟨-227991590057,-227991504423⟩,⟨-167131924143,-167131904522⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14286007125,-14286006573⟩,⟨52604737653,52604745455⟩,⟨-103042307515,-103042302094⟩,⟨374490758536,374490926260⟩,⟨227991504423,227991590057⟩,⟨167131904522,167131924143⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113757072213,-113757071661⟩,⟨-825716074379,-825716066577⟩,⟨-103042307515,-103042302094⟩,⟨2573514014088,2573514181812⟩,⟨227991504423,227991590057⟩,⟨167131904522,167131924143⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨93730705113,93730707009⟩,⟨-606540887381,-606540882619⟩,⟨593625911452,593625926876⟩,⟨3658076931446,3658076931929⟩,⟨-3271460778359,-3271460739457⟩,⟨-2384313305535,-2384313305371⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨125228409034,125228413354⟩,⟨-1431860333623,-1431860271421⟩,⟨677012599799,677012639731⟩,⟨21960605112492,21960606462302⟩,⟨-5652008323812,-5652007699323⟩,⟨-4231111913409,-4231111725219⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-125228413354,-125228409034⟩,⟨1431860271421,1431860333623⟩,⟨-677012639731,-677012599799⟩,⟨-21960606462302,-21960605112492⟩,⟨5652007699323,5652008323812⟩,⟨4231111725219,4231111913409⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨974283214422,974283218742⟩,⟨1431860271421,1431860333623⟩,⟨-677012639731,-677012599799⟩,⟨-21960606462302,-21960605112492⟩,⟨5652007699323,5652008323812⟩,⟨4231111725219,4231111913409⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123985417184,123985417737⟩,⟨781019884222,781019894802⟩,⟨186513194687,186513200983⟩,⟨-2533800143517,-2533799888575⟩,⟨-661448944461,-661448816961⟩,⟨-151360063311,-151360015619⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11769472032,11769472148⟩,⟨170859569620,170859572064⟩,⟨21321812788,21321814016⟩,⟨707680708694,707680769424⟩,⟨107589637266,107589664822⟩,⟨-15269910989,-15269904726⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171107039915,171107194551⟩,⟨1682819238728,1682824771539⟩,⟨104965377539,104967990433⟩,⟨-2064027515379,-2063813197597⟩,⟨518825863675,518956602257⟩,⟨-529605222516,-529512643476⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171107194551,-171107039915⟩,⟨-1682824771539,-1682819238728⟩,⟨-104967990433,-104965377539⟩,⟨2063813197597,2064027515379⟩,⟨-518956602257,-518825863675⟩,⟨529512643476,529605222516⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58521620020,58521834138⟩,⟨-88009719053,-88002539190⟩,⟨136501646715,136505081211⟩,⟨-1748402114361,-1748133731296⟩,⟨-1811278854252,-1811110555424⟩,⟨400634145331,400756685904⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27770822672054,27770848056684⟩,⟨-240210052703500,-240209421024414⟩,⟨-83444784356518,-83444362958536⟩,⟨3334456220194182,3334478613755974⟩,⟨1283795239080442,1283812512171981⟩,⟨301194825008640,301209892341953⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13981101505,13981101631⟩,⟨176141977452,176141980626⟩,⟨42063977622,42063979232⟩,⟨538125805712,538125895821⟩,⟨115797756788,115797798746⟩,⟨29141540131,29141555316⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353126498025,353126823993⟩,⟨1394443153265,1394455359850⟩,⟨1365381427,1371761181⟩,⟨-20971657881768,-20971154272182⟩,⟨-3308423164441,-3308107377235⟩,⟨-1818734188227,-1818509017927⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353126823993,-353126498025⟩,⟨-1394455359850,-1394443153265⟩,⟨-1371761181,-1365381427⟩,⟨20971154272182,20971657881768⟩,⟨3308107377235,3308423164441⟩,⟨1818509017927,1818734188227⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83679476145,83679966556⟩,⟨-539653487069,-539637909632⟩,⟨-75992356028,-75983117211⟩,⟨2645841440990,2646442152445⟩,⟨-2214495036263,-2214079112428⟩,⟨543432154842,543761022347⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239392810481,239392810483⟩,⟨1554091518276,1554091518281⟩,⟨307715674520,307715674522⟩,⟨-3890928397846,-3890928397841⟩,⟨-1540835455796,-1540835455792⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1653825527758,-1653824041425⟩,⟨-4260790714463,-4260748236637⟩,⟨483490587883,483514399897⟩,⟨44387979783037,44389528345601⟩,⟨-7980527960628,-7979469471997⟩,⟨1812268196037,1813121873944⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186492114993,-186491946556⟩,⟨-1655231750496,-1655225886672⟩,⟨-226022630893,-226019683908⟩,⟨2763405729703,2763644611796⟩,⟨-284332681261,-284188082661⟩,⟨596057734009,596162359607⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52900695488,52900863927⟩,⟨-101140232220,-101134368391⟩,⟨81693043627,81695990614⟩,⟨-1127522668143,-1127283786045⟩,⟨-1825168137057,-1825023538453⟩,⟨245244050297,245348675895⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4453848765,4453891164⟩,⟨-35421328184,-35419808295⟩,⟨6343884010,6344712818⟩,⟨94143351422,94206586621⟩,⟨-316634032960,-316592992403⟩,⟨40545910465,40575793894⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2545205991,2545222201⟩,⟨-9732331206,-9731735964⟩,⟨7860978846,7861287456⟩,⟨-89892205820,-89866716225⟩,⟨-190658688962,-190642802106⟩,⟨35738292720,35749311430⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4421818970,4421847222⟩,⟨-34451489623,-34450343427⟩,⟨5668508171,5669095478⟩,⟨62712051240,62765083054⟩,⟨-296293423026,-296261447402⟩,⟨30309614254,30330807566⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4421847222,-4421818970⟩,⟨34450343427,34451489623⟩,⟨-5669095478,-5668508171⟩,⟨-62765083054,-62712051240⟩,⟨296261447402,296293423026⟩,⟨-30330807566,-30309614254⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨32001543,32072194⟩,⟨-970984757,-968318672⟩,⟨674788532,676204647⟩,⟨31378268368,31494535381⟩,⟨-20372585558,-20299569377⟩,⟨10215102899,10266179640⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58521620020,58521834138⟩,⟨-88009719053,-88002539190⟩,⟨136501646715,136505081211⟩,⟨-1748402114361,-1748133731296⟩,⟨-1811278854252,-1811110555424⟩,⟨400634145331,400756685904⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨32001543,32072194⟩,⟨-970984757,-968318672⟩,⟨674788532,676204647⟩,⟨31378268368,31494535381⟩,⟨-20372585558,-20299569377⟩,⟨10215102899,10266179640⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110380659507,110810156237⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨133143986176,137009456743⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110810156237,-110380659507⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438945657651,439375154381⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨53153575731,54750263379⟩,⟨-137009456743,-133143986176⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163534235238,165560419616⟩,⟨962502171033,966367641600⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52724079001,55179760109⟩,⟨-137009456743,-133143986176⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2095228324672,-2081689072192⟩,⟨6392121566645,6497309001381⟩,⟨2915104079033,2954109825963⟩,⟨-38394340899156,-37161242401249⟩,⟨-24849120792617,-24249273067696⟩,⟨-7936946407288,-7728732991012⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-315491780043,-309616944309⟩,⟨-890786525614,-843950189624⟩,⟨-403699188985,-386230309631⟩,⟨5409927853780,5893928570223⟩,⟨3443709360441,3681319750019⟩,⟨1132412195623,1211458295655⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309616944309,315491780043⟩,⟨843950189624,890786525614⟩,⟨386230309631,403699188985⟩,⟨-5893928570223,-5409927853780⟩,⟨-3681319750019,-3443709360441⟩,⟨-1211458295655,-1132412195623⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-165560419616,-163534235238⟩,⟨-966367641600,-962502171033⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨933951208160,935977392538⟩,⟨-966367641600,-962502171033⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-179437206144,-177054426176⟩,⟨-1137674483810,-1130670823085⟩,⟨-517262665306,-515638367333⟩,⟨-1177161931184,-1162713042663⟩,⟨756402319554,764169639552⟩,⟨-243345007147,-241819112366⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152748878765,-150394221452⟩,⟨-813472367853,-802710084403⟩,⟨-369644921369,-366290647428⟩,⟨977478784026,1012182442281⟩,⟨1365838817621,1382708351480⟩,⟨204553561380,207999141548⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150394221452,152748878765⟩,⟨802710084403,813472367853⟩,⟨366290647428,369644921369⟩,⟨-1012182442281,-977478784026⟩,⟨-1382708351480,-1365838817621⟩,⟨-207999141548,-204553561380⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨460011165761,468240658808⟩,⟨1646660274027,1704258893467⟩,⟨752520957059,773344110354⟩,⟨-6906111012504,-6387406637806⟩,⟨-5064028101499,-4809548178062⟩,⟨-1419457437203,-1336965757003⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨817912342663,828032811646⟩,⟨4048267155351,4120108302945⟩,⟨752520957059,773344110354⟩,⟨-19166984641162,-18433370426406⟩,⟨-5064028101499,-4809548178062⟩,⟨-1419457437203,-1336965757003⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨105448158002,110359520218⟩,⟨-274018913486,-266287972352⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10954431636043,11464646159033⟩,⟨26432095598713,29792174121623⟩,⟨-95540420458622,-87140650651204⟩,⟨127556718769560,154836638929978⟩,⟨-278267132712483,-181441166518145⟩,⟨1386378271042495,1592368715927308⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8148858652909,8633927057955⟩,⟨59995366455374,65396744988115⟩,⟨-64453309823331,-56759106092543⟩,⟨89672436609732,156229988755195⟩,⟨-602283562632768,-482776038383948⟩,⟨882110797924965,1066598554996768⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨96514523136,102190395136⟩,⟨-810465793738,-662778639870⟩,⟨627027141575,798773745000⟩,⟨7098989990946,11804678709433⟩,⟨-7277409517136,-1083648209951⟩,⟨-5131718632331,2683966651193⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1196026150912,1201702022912⟩,⟨-810465793738,-662778639870⟩,⟨627027141575,798773745000⟩,⟨7098989990946,11804678709433⟩,⟨-7277409517136,-1083648209951⟩,⟨-5131718632331,2683966651193⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨92511164672,97716674624⟩,⟨-745064448174,-606417237621⟩,⟨573705976979,734315900970⟩,⟨5990426097053,10517629108448⟩,⟨-6373733767388,-493900804668⟩,⟨-5208027068812,2168031519777⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨100631743588,106798620953⟩,⟨-886340309837,-715413351328⟩,⟨676822639933,873553670127⟩,⟨7844649083495,13642664837883⟩,⟨-8695432242107,-1320084239113⟩,⟨-5493796112324,3674995863069⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-102190395136,-96514523136⟩,⟨662778639870,810465793738⟩,⟨-798773745000,-627027141575⟩,⟨-11804678709433,-7098989990946⟩,⟨1083648209951,7277409517136⟩,⟨-2683966651193,5131718632331⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨997321232640,1002997104640⟩,⟨662778639870,810465793738⟩,⟨-798773745000,-627027141575⟩,⟨-11804678709433,-7098989990946⟩,⟨1083648209951,7277409517136⟩,⟨-2683966651193,5131718632331⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-107255675008,-101015964096⟩,⟨726555259040,893510069741⟩,⟨-880619996694,-687363532659⟩,⟨-13740348046931,-8262204654973⟩,⟨1642132032994,8738717760687⟩,⟨-3664284439787,5227831826851⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-97840831122,-91627376449⟩,⟨579968337431,754186466683⟩,⟨-745712491837,-545559695150⟩,⟨-11006093133822,-5025535439760⟩,⟨-518625798553,7043402646580⟩,⟨-3059250454803,6310258964834⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2790912466,15171244504⟩,⟨-306371972406,38773115355⟩,⟨-68889851904,327993974977⟩,⟨-3161444050327,8617129398123⟩,⟨-9214058040660,5723318407467⟩,⟨-8553046567127,9985254827903⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1395456233,7585622252⟩,⟨-153185986203,19386557678⟩,⟨-34444925952,163996987489⟩,⟨-1580722025164,4308564699062⟩,⟨-4607029020330,2861659203734⟩,⟨-4276523283564,4992627413952⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7585622252,-1395456233⟩,⟨-19386557678,153185986203⟩,⟨-163996987489,34444925952⟩,⟨-4308564699062,1580722025164⟩,⟨-2861659203734,4607029020330⟩,⟨-4992627413952,4276523283564⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754537761364,760727946647⟩,⟨-19386557678,153185986203⟩,⟨-163996987489,34444925952⟩,⟨-4308564699062,1580722025164⟩,⟨-2861659203734,4607029020330⟩,⟨-4992627413952,4276523283564⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8471991510,9497741174⟩,⟨-150652012430,-116356685560⟩,⟨110080192030,148478656458⟩,⟨2045328363585,3389103921273⟩,⟨-2530323675058,-946180055114⟩,⟨-238741119562,1659491514727⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9497741174,-8471991510⟩,⟨116356685560,150652012430⟩,⟨-148478656458,-110080192030⟩,⟨-3389103921273,-2045328363585⟩,⟨946180055114,2530323675058⟩,⟨-1659491514727,238741119562⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090013886602,1091039636266⟩,⟨116356685560,150652012430⟩,⟨-148478656458,-110080192030⟩,⟨-3389103921273,-2045328363585⟩,⟨946180055114,2530323675058⟩,⟨-1659491514727,238741119562⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9539000384,-8504799424⟩,⟨117260202553,151964705635⟩,⟨-149772412315,-110934971655⟩,⟨-3439637791767,-2073715978495⟩,⟨965358143894,2573071639326⟩,⟨-1694352930633,229628611203⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4769500192,-4252399712⟩,⟨58630101276,75982352818⟩,⟨-74886206158,-55467485827⟩,⟨-1719818895884,-1036857989247⟩,⟨482679071947,1286535819663⟩,⟨-847176465317,114814305602⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4252399712,4769500192⟩,⟨-75982352818,-58630101276⟩,⟨55467485827,74886206158⟩,⟨1036857989247,1719818895884⟩,⟨-1286535819663,-482679071947⟩,⟨-114814305602,847176465317⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766375783328,766892903072⟩,⟨-75982352818,-58630101276⟩,⟨55467485827,74886206158⟩,⟨1036857989247,1719818895884⟩,⟨-1286535819663,-482679071947⟩,⟨-114814305602,847176465317⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272503471650,272759909067⟩,⟨29089171390,37663003108⟩,⟨-37119664115,-27520048007⟩,⟨-847275980319,-511332090896⟩,⟨236545013778,632580918765⟩,⟨-414872878682,59685279891⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532751566656,1533785806144⟩,⟨-151964705636,-117260202552⟩,⟨110934971654,149772412316⟩,⟨2073715978494,3439637791768⟩,⟨-2573071639326,-965358143894⟩,⟨-229628611204,1694352930634⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1205313369322,1212172948945⟩,⟨-985063467078,-796468855034⟩,⟨753505860755,970852614312⟩,⟨9583549732268,15948755698218⟩,⟨-10423085646010,-2298063317911⟩,⟨-5295124980040,4817319405589⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1311115110868,1324834270114⟩,⟨-1970126934157,-1592937710069⟩,⟨1507011721511,1941705228624⟩,⟨19167099464543,31897511396433⟩,⟨-20846171292020,-4596126635822⟩,⟨-10585386604122,9634638811177⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨193527128832,204972349632⟩,⟨-1652164218341,-1322017080968⟩,⟨1250705049207,1628329548558⟩,⟨13424634865103,25159957991253⟩,⟨-15977958982510,-1367651029714⟩,⟨-11288476146312,6656996214815⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨66232907762,70703289984⟩,⟨-562545300534,-440593225673⟩,⟨415054036025,555855377992⟩,⟨4245392194981,8342893022491⟩,⟨-5340520866582,-83295604720⟩,⟨-4252827531558,2304491725759⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379877858986,380491907902⟩,⟨2852715379,23476938898⟩,⟨-24286645426,-1209161503⟩,⟨-678384788905,134267087239⟩,⟨-302690780798,653437333772⟩,⟨-645812738246,498030308272⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177270776349,3182406636812⟩,⟨-196676811754,-23821398086⟩,⟨10097017643,203460085292⟩,⟨-1124458210531,5707442385024⟩,⟨-5499284831433,2535624575276⟩,⟨-4172158346280,5436277533376⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨191393957961,204642328108⟩,⟨-1640868136367,-1274622027858⟩,⟨1199994416407,1621941138584⟩,⟨12214740084858,24715784376310⟩,⟨-16014660976320,-90687113725⟩,⟨-12569971902135,7225372641773⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨384921086793,409614677740⟩,⟨-3293032354708,-2596639108826⟩,⟨2450699465614,3250270687142⟩,⟨25639374949961,49875742367563⟩,⟨-31992619958830,-1458338143439⟩,⟨-23858448048447,13882368856588⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517800102283,526330958392⟩,⟨-26826266940,211972038850⟩,⟨-226931827546,47663375504⟩,⟨-5967404514142,2230018011310⟩,⟨-4005535029726,6384602250786⟩,⟨-6918853732859,5966586810609⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355339334428,364156830287⟩,⟨-27840757365,219988197198⟩,⟨-235513721052,49465864018⟩,⟨-6198680408964,2358649228723⟩,⟨-4204437410670,6636009932094⟩,⟨-7191168210759,6242997372753⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨710678668856,728313660574⟩,⟨-55681514730,439976394396⟩,⟨-471027442104,98931728036⟩,⟨-12397360817928,4717298457446⟩,⟨-8408874821340,13272019864188⟩,⟨-14382336421518,12485994745506⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523253825482,1525313814634⟩,⟨-35608020076,33391809878⟩,⟨-37543684804,39692220286⟩,⟨-1315387942779,1394309428183⟩,⟨-1626891584212,1564965531164⟩,⟨-1889120125931,1933094050196⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨984568033366,1010363928672⟩,⟨-100831667702,632482427838⟩,⟨-678308645570,163536531302⟩,⟨-18098229797797,7494453097691⟩,⟨-12772313393217,19479572998717⟩,⟨-21237465875514,18634025118756⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67537386768,67664557714⟩,⟨14418947450,18686400478⟩,⟨-18416824258,-13641162916⟩,⟨-418834569163,-250877325255⟩,⟨114707835438,312397202812⟩,⟨-204460476420,32119025455⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50240180124,50957600227⟩,⟨259390453445,267626327314⟩,⟨32353968122,37444544133⟩,⟨-1388790043732,-1178848234505⟩,⟨-285456751718,-97244297035⟩,⟨-267238672665,-76606819144⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136700791276,2139585284685⟩,⟨-423972430398,-326928346416⟩,⟨309293230382,417856063292⟩,⟨5806653225478,9638389920019⟩,⟨-7220116238642,-2715137206328⟩,⟨-618264560425,4767946395253⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2978623784022,2984657422244⟩,⟨-887143272768,-683621604121⟩,⟨646745798018,874345049245⟩,⟨12194267372933,20255794650882⟩,⟨-15194397536831,-5726949794090⟩,⟨-1246892255229,10062092518768⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136102785682,138325940259⟩,⟨661584528408,695242880901⟩,⟨117200146944,142166447449⟩,⟨-3644587299690,-2577333851789⟩,⟨-1356711107053,-332417841924⟩,⟨-745153501235,318355976621⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8739689875601,8882447288326⟩,⟨-45373488949861,-41800139539663⟩,⟨-9278178762519,-7404923008276⟩,⟨562683684884114,701411396151104⟩,⟨91835224950597,183332693989985⟩,⟨-8228782576185,68013876989915⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7826037538551,8162264146863⟩,⟨-42509208038878,-32320794484736⟩,⟨-14005652642402,-5309671782450⟩,⟨305451911064269,713407669123772⟩,⟨-33032739945576,354677272649656⟩,⟨-181889280258459,224482802501335⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15652075077102,16324528293726⟩,⟨-85018416077756,-64641588969472⟩,⟨-28011305284804,-10619343564900⟩,⟨610903822128538,1426815338247544⟩,⟨-66065479891152,709354545299312⟩,⟨-363778560516918,448965605002670⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10909882818222,10952333724170⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145760,2173453475298114⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9810371190446,9852822096394⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145775,2173453475298112⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2406362562496,2411110103296⟩,⟨-12227224809080,-12080350374972⟩,⟨0,0⟩,⟨103760055435140,110865974497594⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7302021959225,7392493797126⟩,⟨-43684227867484,-42451039958616⟩,⟨-19861762270426,-19359644282781⟩,⟨493586791064467,516283629516241⟩,⟨273592308238329,284439900593829⟩,⟨102655354598691,106727069731259⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6202510331449,6292982169350⟩,⟨-43684227867485,-42451039958615⟩,⟨-19861762270427,-19359644282781⟩,⟨493586791064471,516283629516240⟩,⟨273592308238330,284439900593830⟩,⟨102655354598690,106727069731260⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1902251866112,1918173898304⟩,⟨-7743851106127,-7417057730278⟩,⟨-3520870969588,-3382522534737⟩,⟨31699746071127,41487184372437⟩,⟨23004661123044,27604587835771⟩,⟨6661392119155,8513434619659⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99256358666,99685855397⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138909851171,140936035550⟩,⟨672060044276,679480043768⟩,⟨306691338074,308739407874⟩,⟨-1698693120000,-1685130754127⟩,⟨-1544782295862,-1536888615726⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4308614428608,4329284001600⟩,⟨-19971075915207,-19497408105250⟩,⟨-3520870969588,-3382522534737⟩,⟨135459801506267,152353158870031⟩,⟨23004661123044,27604587835771⟩,⟨6661392119155,8513434619659⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨769842173586,819229355480⟩,⟨-6586064709416,-5193278217652⟩,⟨4901398931228,6500541374284⟩,⟨51278749899922,99751484735126⟩,⟨-63985239917660,-2916676286878⟩,⟨-47716896096894,27764737713176⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5078456602194,5148513357080⟩,⟨-26557140624623,-24690686322902⟩,⟨1380527961640,3118018839547⟩,⟨186738551406189,252104643605157⟩,⟨-40980578794616,24687911548893⟩,⟨-41055503977739,36278172332835⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458448184851,466783565593⟩,⟨1647060040468,1885882816009⟩,⟨124624583358,282691303405⟩,⟨-35889482220268,-26728098697861⟩,⟨-2613187956514,4730277940958⟩,⟨-3722246249505,3289115412589⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨39408062095,41528303720⟩,⟨-835545915334,-792817236564⟩,⟨328085346598,330673870673⟩,⟨9791349176569,10538499684950⟩,⟨-6659570832821,-6593775017748⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497856246946,508311869313⟩,⟨811514125134,1093065579445⟩,⟨452709929956,613365174078⟩,⟨-26098133043699,-16189599012911⟩,⟨-9272758789335,-1863497076790⟩,⟨-3722246249505,3289115412589⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501398014948,502387228948⟩,⟨2512147284185,2552733193796⟩,⟨0,0⟩,⟨2027158573049,4364694834823⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227031827260,232257108533⟩,⟨1507560036883,1679588212130⟩,⟨206444256243,280257909379⟩,⟨-7298557802945,-289398523925⟩,⟨-3202550553229,574258505935⟩,⟨-1700763258442,1502857756187⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-819229355480,-769842173586⟩,⟨5193278217652,6586064709416⟩,⟨-6500541374284,-4901398931228⟩,⟨-99751484735126,-51278749899922⟩,⟨2916676286878,63985239917660⟩,⟨-27764737713176,47716896096894⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3489385073128,3559441828014⟩,⟨-14777797697555,-12911343395834⟩,⟨-10021412343872,-8283921465965⟩,⟨35708316771141,101074408970109⟩,⟨25921337409922,91589827753431⟩,⟨-21103345594021,56230330716553⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨440841141595,456251309526⟩,⟨238607813197,568485938453⟩,⟨-311241773693,-47092121900⟩,⟨-19252729206256,-8175847717616⟩,⟨-12068696201968,-1802235405278⟩,⟨-9469798999533,1474053382734⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨327068470476,331120839232⟩,⟨1925004342066,1932735283200⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-331120839232,-327068470476⟩,⟨-1932735283200,-1925004342066⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨768390788544,772443157300⟩,⟨-1932735283200,-1925004342066⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1329383677703,1347580384624⟩,⟨-8812100687141,-8513818047516⟩,⟨-4006568445756,-3882696137689⟩,⟨48124574780118,56370590942107⟩,⟨31725364283401,35607542572894⟩,⟨10056761909577,11608860604930⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1347580384624,-1329383677703⟩,⟨8513818047516,8812100687141⟩,⟨3882696137689,4006568445756⟩,⟨-56370590942107,-48124574780118⟩,⟨-35607542572894,-31725364283401⟩,⟨-11608860604930,-10056761909577⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-248068756848,-229872049927⟩,⟨8513818047516,8812100687141⟩,⟨3882696137689,4006568445756⟩,⟨-56370590942107,-48124574780118⟩,⟨-35607542572894,-31725364283401⟩,⟨-11608860604930,-10056761909577⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12449504078,-11022886720⟩,⟨436092974609,473153129482⟩,⟨87053494609,109303207471⟩,⟨-5025138253777,-4369622936285⟩,⟨1342502428435,1777993319394⟩,⟨2517491407992,2719880057494⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428391637517,445228422806⟩,⟨674700787806,1041639067935⟩,⟨-224188279084,62211085571⟩,⟨-24277867460033,-12545470653901⟩,⟨-10726193773533,-24242085884⟩,⟨-6952307591541,4193933440228⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99685855397,-99256358666⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4759567760,5002804380⟩,⟨29675089689,32081374218⟩,⟨39624999436,39835402372⟩,⟨-329360573731,-318062460926⟩,⟨250784818133,251900503000⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10416666256,10970609024⟩,⟨9311962490,18057543759⟩,⟨86722243560,87354729775⟩,⟨-986623437550,-843741670360⟩,⟨105867709348,117030113883⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1459997481514,1478062814994⟩,⟨-7445515318313,-7137953675475⟩,⟨-1397522831100,-1326854065007⟩,⟨102297107129876,109648261263647⟩,⟨21454279878702,23230903215119⟩,⟨4769059346808,5207867804713⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13831874184,14747683287⟩,⟨-61924216204,-43349698195⟩,⟨101210917461,104859629419⟩,⟨-601714444981,-147237390638⟩,⟨-270654842156,-185118511976⟩,⟨-176881038861,-157344439915⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14747683287,-13831874184⟩,⟨43349698195,61924216204⟩,⟨-104859629419,-101210917461⟩,⟨147237390638,601714444981⟩,⟨185118511976,270654842156⟩,⟨157344439915,176881038861⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114433538684,-113088232850⟩,⟨-835400610567,-815967099098⟩,⟨-104859629419,-101210917461⟩,⟨2346260646190,2800737700533⟩,⟨185118511976,270654842156⟩,⟨157344439915,176881038861⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨91217296056,96264898781⟩,⟨-627653034919,-586015570562⟩,⟨582717239841,604320637061⟩,⟨3316393467665,4011976259397⟩,⟨-3499961327628,-3039191301931⟩,⟨-2494517218375,-2273480165096⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨121123796372,129407969578⟩,⟨-1495620736134,-1370323016815⟩,⟨651410399516,702304370773⟩,⟨20499188038952,23493732685767⟩,⟨-6310149466458,-4986887067971⟩,⟨-4493937211639,-3969309477807⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-129407969578,-121123796372⟩,⟨1370323016815,1495620736134⟩,⟨-702304370773,-651410399516⟩,⟨-23493732685767,-20499188038952⟩,⟨4986887067971,6310149466458⟩,⟨3969309477807,4493937211639⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨970103658198,978387831404⟩,⟨1370323016815,1495620736134⟩,⟨-702304370773,-651410399516⟩,⟨-23493732685767,-20499188038952⟩,⟨4986887067971,6310149466458⟩,⟨3969309477807,4493937211639⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122560736400,125410317368⟩,⟨766084916724,796337066042⟩,⟨180573256545,192430487088⟩,⟨-2847823933004,-2228081741340⟩,⟨-796357257963,-525363848544⟩,⟨-205408907928,-96587466021⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11631480819,11909864749⟩,⟨167849570608,173891472672⟩,⟨20819723068,21826887788⟩,⟨628104282100,786821528624⟩,⟨93883113306,121263061472⟩,⟨-18185298160,-12365967952⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165579705059,176826619345⟩,⟨1468503109349,1897950699881⟩,⟨-7038569348,211725779331⟩,⟨-11487921877219,7401051427746⟩,⟨-5496967739626,6638953648745⟩,⟨-5322562267957,4284977866865⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176826619345,-165579705059⟩,⟨-1897950699881,-1468503109349⟩,⟨-211725779331,7038569348⟩,⟨-7401051427746,11487921877219⟩,⟨-6638953648745,5496967739626⟩,⟨-4284977866865,5322562267957⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50205207915,66677403474⟩,⟨-390390662998,211085102781⟩,⟨-5281523088,287296478727⟩,⟨-14699609230691,11198523353294⟩,⟨-9841504201974,6071226245561⟩,⟨-5985741125307,6825420024144⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27079467166861,28479265961460⟩,⟨-263294007781836,-217421009157200⟩,⟨-101142279542123,-66524228511214⟩,⟨2380293640650291,4302708989972326⟩,⟨482724789948408,2116895756499115⟩,⟨-474470282055653,1089047411617560⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13661641884,14304303207⟩,⟨170788428546,181660442076⟩,⟨40256402454,43897250102⟩,⟨417893891398,656795934947⟩,⟨69963847168,161618207768⟩,⟨12453355603,45823365144⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336467549316,370506364039⟩,⟨780912453949,2003824265008⟩,⟨-324369380096,310438985347⟩,⟨-47134697970752,5444540096619⟩,⟨-19501419240531,13432627918122⟩,⟨-13942073951477,10483770851337⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370506364039,-336467549316⟩,⟨-2003824265008,-780912453949⟩,⟨-310438985347,324369380096⟩,⟨-5444540096619,47134697970752⟩,⟨-13432627918122,19501419240531⟩,⟨-10483770851337,13942073951477⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57885273478,108760873490⟩,⟨-1329123477202,260726613986⟩,⟨-534627264431,386580465667⟩,⟨-29722407556652,34589227316851⟩,⟨-24158821691655,19477177154647⟩,⟨-17436078442878,18136007391705⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238166209837,240621890947⟩,⟨1549951359578,1558230352530⟩,⟨306691338074,308739407874⟩,⟨-3897716375552,-3884154009679⟩,⟨-1544782295862,-1536888615726⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1699002987151,-1609865203959⟩,⟨-5754662050662,-2767246851762⟩,⟨-464625545228,1474538210620⟩,⟨-19154741271132,107942070418562⟩,⟨-57360914492036,40285231460821⟩,⟨-42531945774747,45829872473631⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-193788313325,-179449002554⟩,⟨-1886904145162,-1430134273199⟩,⟨-350345371286,-96202982159⟩,⟨-7258306415616,12856270158984⟩,⟨-7117029305581,6438982090541⟩,⟨-4872407095871,6060892166907⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44377896512,61172888393⟩,⟨-336952785584,128096079331⟩,⟨-43654033212,212536425715⟩,⟨-11156022791168,8972116149305⟩,⟨-8661811601443,4902093474815⟩,⟨-5223563957537,5710421493377⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2643120924,6595557938⟩,⟨-119218140632,36691175226⟩,⟨-32943699702,51861932354⟩,⟨-3766828406110,4149147424238⟩,⟨-2923105052053,2039649916356⟩,⟨-1928856301329,1976993134203⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1791156772,3403440382⟩,⟨-37493691974,14253614000⟩,⟨-4857508070,23649530794⟩,⟨-1319874114174,1204875733609⟩,⟨-1094090794250,594991979372⟩,⟨-598117489382,717581695331⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3098858826,5937536576⟩,⟨-89380734483,12783673037⟩,⟨-19372800698,35747948034⟩,⟨-2451747231218,2758544249145⟩,⟨-2083447753004,1277726300357⟩,⟨-1184067197285,1309332913804⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5937536576,-3098858826⟩,⟨-12783673037,89380734483⟩,⟨-35747948034,19372800698⟩,⟨-2758544249145,2451747231218⟩,⟨-1277726300357,2083447753004⟩,⟨-1309332913804,1184067197285⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3294415652,3496699112⟩,⟨-132001813669,126071909709⟩,⟨-68691647736,71234733052⟩,⟨-6525372655255,6600894655456⟩,⟨-4200831352410,4123097669360⟩,⟨-3238189215133,3161060331488⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50205207915,66677403474⟩,⟨-390390662998,211085102781⟩,⟨-5281523088,287296478727⟩,⟨-14699609230691,11198523353294⟩,⟨-9841504201974,6071226245561⟩,⟨-5985741125307,6825420024144⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3294415652,3496699112⟩,⟨-132001813669,126071909709⟩,⟨-68691647736,71234733052⟩,⟨-6525372655255,6600894655456⟩,⟨-4200831352410,4123097669360⟩,⟨-3238189215133,3161060331488⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (103/1024) u, BivariateJet2.affineZ (629/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000022

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000023Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2525295488000,-2525295430144⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-116561173120,-116561173056⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2078171920128,-2078171881472⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2078171920128,-2078171881472⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-180061870016,-180061869952⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-180061870016,-180061869952⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨97376253248,97376253312⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-106845631168,-106845631104⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨97376375744,97376375808⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-106845778752,-106845778688⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-9469402944,-9469402880⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-9469377920,-9469377856⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨204221884352,204221884416⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨204222154496,204222154560⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1898110011456,1898110050048⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1898110011456,1898110050048⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2084901581504,-2084901542784⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2071478230272,-2071478191616⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-181257213184,-181257213120⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-178868713408,-178868713344⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨94785791296,94785791360⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-103734513472,-103734513408⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨99988338112,99988338176⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-109999119360,-109999119296⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-10010781184,-10010781120⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-8948722112,-8948722048⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨198520304704,198520304768⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨209987457408,209987457472⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1890220978496,1890221017088⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1906032829440,1906032868032⟩



end LaneCBRB2Cell000023Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000023
open Set LaneCBRB2Cell000023Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110595407872,110595407872⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨138942192025,138942192026⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110595407872,-110595407872⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439160406016,439160406016⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨55495465369,55495465370⟩,⟨-138942192026,-138942192025⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨166090873241,166090873242⟩,⟨960569435750,960569435751⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨55495465369,55495465370⟩,⟨-138942192026,-138942192025⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2078171920128,-2078171881472⟩,⟨6358912102017,6358912102064⟩,⟨2907215570899,2907215570917⟩,⟨-36776112321396,-36776112320862⟩,⟨-24092282508329,-24092282508056⟩,⟨-7686960430677,-7686960430580⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313926092496,-313926086654⟩,⟨-854989743698,-854989709911⟩,⟨-390890683179,-390890667733⟩,⟨5555354264042,5555354264251⟩,⟨3518499169402,3518499208160⟩,⟨1161182781721,1161182781759⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨313926086654,313926092496⟩,⟨854989709911,854989743698⟩,⟨390890667733,390890683179⟩,⟨-5555354264251,-5555354264042⟩,⟨-3518499208160,-3518499169402⟩,⟨-1161182781759,-1161182781721⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-166090873242,-166090873241⟩,⟨-960569435751,-960569435750⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨933420754534,933420754535⟩,⟨-960569435751,-960569435750⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-180061870016,-180061869952⟩,⟨-1131491086700,-1131491086695⟩,⟨-517303660251,-517303660248⟩,⟨-1164400672934,-1164400672923⟩,⟨762806838304,762806838312⟩,⟨-243383580627,-243383580624⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152861945547,-152861945492⟩,⟨-803261477884,-803261477821⟩,⟨-367241163040,-367241163009⟩,⟨988507740379,988507740403⟩,⟨1371383209373,1371383209452⟩,⟨206618356483,206618356489⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨152861945492,152861945547⟩,⟨803261477821,803261477884⟩,⟨367241163009,367241163040⟩,⟨-988507740403,-988507740379⟩,⟨-1371383209452,-1371383209373⟩,⟨-206618356489,-206618356483⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨466788032146,466788038043⟩,⟨1658251187732,1658251221582⟩,⟨758131830742,758131846219⟩,⟨-6543862004654,-6543862004421⟩,⟨-4889882417612,-4889882378775⟩,⟨-1367801138248,-1367801138204⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨825633998639,825634010414⟩,⟨4066985444754,4066985536528⟩,⟨758131830742,758131846219⟩,⟨-18697404530268,-18697404530025⟩,⟨-4889882417612,-4889882378775⟩,⟨-1367801138248,-1367801138204⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨110990930738,110990930740⟩,⟨-277884384052,-277884384050⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10892113540759,10892113540956⟩,⟨27270230478260,27270230479443⟩,⟨-86194159706802,-86194159703682⟩,⟨136551178530149,136551178539527⟩,⟨-215801514780886,-215801514746547⟩,⟨1364185773352895,1364185773426930⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8178994227170,8178994343966⟩,⟨60766339326116,60766340528922⟩,⟨-57213739431688,-57213738352808⟩,⟨119054951341413,119054957377716⟩,⟨-510508649040298,-510508638727146⟩,⟨891965860116137,891965877212773⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨101818392064,101818525952⟩,⟨-747139803090,-747137792234⟩,⟨703457648304,703459540939⟩,⟨9433105493994,9433154578035⟩,⟨-3983058035149,-3982998686220⟩,⟨-1306953483308,-1306884011798⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1201330019840,1201330153728⟩,⟨-747139803090,-747137792234⟩,⟨703457648304,703459540939⟩,⟨9433105493994,9433154578035⟩,⟨-3983058035149,-3982998686220⟩,⟨-1306953483308,-1306884011798⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨97376253248,97376375808⟩,⟨-683816176659,-683814260020⟩,⟨643836219009,643838022991⟩,⟨8208320423454,8208368693637⟩,⟨-3245056930034,-3244999960655⟩,⟨-1573193477848,-1573127648362⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨106393614484,106393760252⟩,⟨-813309051296,-813306612529⟩,⟨765758020739,765760316209⟩,⟨10733191774958,10733256019182⟩,⟨-4773314252953,-4773241106093⟩,⟨-1010783426963,-1010700486704⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-101818525952,-101818392064⟩,⟨747137792234,747139803090⟩,⟨-703459540939,-703457648304⟩,⟨-9433154578035,-9433105493994⟩,⟨3982998686220,3983058035149⟩,⟨1306884011798,1306953483308⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨997693101824,997693235712⟩,⟨747137792234,747139803090⟩,⟨-703459540939,-703457648304⟩,⟨-9433154578035,-9433105493994⟩,⟨3982998686220,3983058035149⟩,⟨1306884011798,1306953483308⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-106845778752,-106845631104⟩,⟨823386047642,823388374211⟩,⟨-775250368595,-775248178771⟩,⟨-11012453982948,-11012395010007⟩,⟨4970035281531,4970104556631⟩,⟨893638238309,893718080968⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-96951508318,-96951361331⟩,⟨674533881257,674536388380⟩,⟨-635100761741,-635098401916⟩,⟨-7956986401058,-7956919338100⟩,⟨3069140951219,3069216530255⟩,⟨1675873831618,1675958786842⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨9442106166,9442398921⟩,⟨-138775170039,-138770224149⟩,⟨130657258998,130661914293⟩,⟨2776205373900,2776336681082⟩,⟨-1704173301734,-1704024575838⟩,⟨665090404655,665258300138⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4721053083,4721199461⟩,⟨-69387585020,-69385112074⟩,⟨65328629499,65330957147⟩,⟨1388102686950,1388168340541⟩,⟨-852086650867,-852012287919⟩,⟨332545202327,332629150069⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4721199461,-4721053083⟩,⟨69385112074,69387585020⟩,⟨-65330957147,-65328629499⟩,⟨-1388168340541,-1388102686950⟩,⟨852012287919,852086650867⟩,⟨-332629150069,-332545202327⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757402184155,757402349797⟩,⟨69385112074,69387585020⟩,⟨-65330957147,-65328629499⟩,⟨-1388168340541,-1388102686950⟩,⟨852012287919,852086650867⟩,⟨-332629150069,-332545202327⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨9428717896,9428742694⟩,⟨-138375386870,-138374832486⟩,⟨130284982578,130285504430⟩,⟨2762460124636,2762476978343⟩,⟨-1693718733478,-1693701626404⟩,⟨658075051975,658093080426⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9428742694,-9428717896⟩,⟨138374832486,138375386870⟩,⟨-130285504430,-130284982578⟩,⟨-2762476978343,-2762460124636⟩,⟨1693701626404,1693718733478⟩,⟨-658093080426,-658075051975⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090082885082,1090082909880⟩,⟨138374832486,138375386870⟩,⟨-130285504430,-130284982578⟩,⟨-2762476978343,-2762460124636⟩,⟨1693701626404,1693718733478⟩,⟨-658093080426,-658075051975⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9469402944,-9469377856⟩,⟨139571711409,139572273764⟩,⟨-131412417361,-131411888004⟩,⟨-2804088540756,-2804071335111⟩,⟨1725032759580,1725050187899⟩,⟨-679491566476,-679473240449⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4734701472,-4734688928⟩,⟨69785855704,69786136882⟩,⟨-65706208681,-65705944002⟩,⟨-1402044270378,-1402035667555⟩,⟨862516379790,862525093950⟩,⟨-339745783238,-339736620224⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4734688928,4734701472⟩,⟨-69786136882,-69785855704⟩,⟨65705944002,65706208681⟩,⟨1402035667555,1402044270378⟩,⟨-862525093950,-862516379790⟩,⟨339736620224,339745783238⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766858072544,766858104352⟩,⟨-69786136882,-69785855704⟩,⟨65705944002,65706208681⟩,⟨1402035667555,1402044270378⟩,⟨-862525093950,-862516379790⟩,⟨339736620224,339745783238⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272520721270,272520727470⟩,⟨34593708121,34593846718⟩,⟨-32571376108,-32571245644⟩,⟨-690619244586,-690615031159⟩,⟨423425406601,423429683370⟩,⟨-164523270107,-164518762993⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533716145088,1533716208704⟩,⟨-139572273764,-139571711408⟩,⟨131411888004,131412417362⟩,⟨2804071335110,2804088540756⟩,⟨-1725050187900,-1725032759580⟩,⟨679473240448,679491566476⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1211720974285,1211721136896⟩,⟨-907418413505,-907415727725⟩,⟨854365206117,854367734076⟩,⟨12815783939323,12815854490745⟩,⟨-6117131491366,-6117050710484⟩,⟨-382526293810,-382434525035⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1323930320794,1323930646016⟩,⟨-1814836827009,-1814831455450⟩,⟨1708730412234,1708735468152⟩,⟨25631567878652,25631708981481⟩,⟨-12234262982729,-12234101420969⟩,⟨-765052440909,-764869196779⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨204221884352,204222154560⟩,⟨-1507204844903,-1507200013628⟩,⟨1419084120937,1419088668429⟩,⟨19220701225506,19220836884540⟩,⟨-8215172934714,-8215023794147⟩,⟨-2466920761270,-2466756684252⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨70137932685,70138040255⟩,⟨-508244522229,-508242787032⟩,⟨478529234469,478530867698⟩,⟨6275176017051,6275221113265⟩,⟨-2576060085854,-2576008210317⟩,⟨-1014698518094,-1014639447848⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380140982163,380141006580⟩,⟨13661148006,13661483510⟩,⟨-12862788003,-12862472187⟩,⟨-277125828161,-277115559951⟩,⟨171343798873,171354184954⟩,⟨-68868789682,-68857884556⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3180203657824,3180203862094⟩,⟨-114289973087,-114287151627⟩,⟨107605547388,107608203283⟩,⟨2326522236419,2326608841639⟩,⟨-1441258485337,-1441171031424⟩,⟨583336812438,583428476129⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨202865439930,202865764094⟩,⟨-1477326138424,-1477320833991⟩,⟨1390951776986,1390956769754⟩,⟨18404249589231,18404389911691⟩,⟨-7642361960769,-7642202923584⟩,⟨-2804017010557,-2803837432744⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨407087324282,407087918654⟩,⟨-2984530983327,-2984520847619⟩,⟨2810035897923,2810045438183⟩,⟨37624950814737,37625226796231⟩,⟨-15857534895483,-15857226717731⟩,⟨-5270937771827,-5270594116996⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨521738973987,521739202194⟩,⟨95592323182,95595751084⟩,⟨-90006907082,-90003680580⟩,⟨-1903731880272,-1903640386393⟩,⟨1165577142186,1165680436896⟩,⟨-450502320822,-450386012036⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359401600195,359401835998⟩,⟨98773627131,98777190718⟩,⟨-93002349225,-92998995004⟩,⟨-1958039751019,-1957944133723⟩,⟨1195847259059,1195954865138⟩,⟨-457473606330,-457352750450⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨718803200390,718803671996⟩,⟨197547254262,197554381436⟩,⟨-186004698450,-185997990008⟩,⟨-3916079502038,-3915888267446⟩,⟨2391694518118,2391909730276⟩,⟨-914947212660,-914705500900⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524287402394,1524287490808⟩,⟨-1197441278,-1196324538⟩,⟨1126383574,1127434784⟩,⟨41594356767,41628416120⟩,⟨-31348561496,-31314026102⟩,⟨21380160022,21416514501⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨996499387069,996500098673⟩,⟨273083120065,273093747156⟩,⟨-257127782754,-257117779962⟩,⟨-5402222050858,-5401933920564⟩,⟨3295591696921,3295913227894⟩,⟨-1254824273832,-1254464962419⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67545937346,67545940420⟩,⟨17148526764,17148595860⟩,⟨-16146032270,-16145967230⟩,⟨-340171635433,-340169521551⟩,⟨207847602756,207849744002⟩,⟨-79626470712,-79624219162⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50720902748,50720905780⟩,⟨262722779335,262722848414⟩,⟨34449851012,34449903097⟩,⟨-1277208345079,-1277206187789⟩,⟨-192222155234,-192220239257⟩,⟨-166085900718,-166084115178⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2139390938922,2139391116399⟩,⟨-389380617996,-389379032974⟩,⟨366614648170,366616140188⟩,⟨7858270221297,7858318831864⟩,⟨-4845931405550,-4845882315350⟩,⟨1927015843354,1927067301258⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2984250771696,2984251143042⟩,⟨-814724487794,-814721137563⟩,⟨767089847964,767093001622⟩,⟨16516472272386,16516575265734⟩,⟨-10209241269756,-10209137569454⟩,⟨4097736792407,4097845160362⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137664658874,137664684235⟩,⟨675488166043,675488599062⟩,⟨128888572403,128888873001⟩,⟨-3093985975330,-3093973188650⟩,⟨-834912820032,-834901797642⟩,⟨-213684750431,-213674567440⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8781669941950,8781671559737⟩,⟨-43089628578814,-43089585080195⟩,⟨-8221861439656,-8221839235108⟩,⟨620226323324556,620227987558845⟩,⟨133943882093990,133944889330842⟩,⟨29025757706354,29026492624534⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7958923301517,7958930451234⟩,⟨-36871545765683,-36871393175651⟩,⟨-9505217779335,-9505112064468⟩,⟨497565993127207,497571066618110⟩,⟨155750562462565,155754622061845⟩,⟨20129534485282,20133250941358⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15917846603034,15917860902468⟩,⟨-73743091531366,-73742786351302⟩,⟨-19010435558670,-19010224128936⟩,⟨995131986254414,995142133236220⟩,⟨311501124925130,311509244123690⟩,⟨40259068970564,40266501882716⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10931067056724,10931067056725⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603222,2160817149603840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9831555428948,9831555428949⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603232,2160817149603830⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2408734257088,2408734314944⟩,⟨-12153542525660,-12153542525558⟩,⟨0,0⟩,⟨107314718406763,107314718418708⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7278701087043,7278701087088⟩,⟨-42095617054645,-42095617054079⟩,⟨-19245592863111,-19245592862872⟩,⟨486911319471036,486911319481095⟩,⟨270794367904238,270794367909203⟩,⟨101774434810295,101774434812186⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6179189459267,6179189459312⟩,⟨-42095617054646,-42095617054079⟩,⟨-19245592863111,-19245592862872⟩,⟨486911319471045,486911319481094⟩,⟨270794367904241,270794367909204⟩,⟨101774434810296,101774434812187⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1898110011456,1898110050048⟩,⟨-7490403188851,-7490403188634⟩,⟨-3424519231207,-3424519231111⟩,⟨35611711643706,35611711652643⟩,⟨24855089344364,24855089348623⟩,⟨7443576849087,7443576850903⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99471065088,99471065088⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨141001390349,141001390351⟩,⟨670364562307,670364562311⟩,⟨306482345164,306482345166⟩,⟨-1678369955515,-1678369955510⟩,⟨-1534659762588,-1534659762584⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4306844268544,4306844364992⟩,⟨-19643945714511,-19643945714192⟩,⟨-3424519231207,-3424519231111⟩,⟨142926430050469,142926430071351⟩,⟨24855089344364,24855089348623⟩,⟨7443576849087,7443576850903⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨814174648564,814175837308⟩,⟨-5969061966654,-5969041695238⟩,⟨5620071795846,5620090876366⟩,⟨75249901629474,75250453592462⟩,⟨-31715069790966,-31714453435462⟩,⟨-10541875543654,-10541188233992⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5121018917108,5121020202300⟩,⟨-25613007681165,-25612987409430⟩,⟨2195552564639,2195571645255⟩,⟨218176331679943,218176883663813⟩,⟨-6859980446602,-6859364086839⟩,⟨-3098298694567,-3097611383089⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463290421994,463290538265⟩,⟨1773645944514,1773648805116⟩,⟨198628142299,198629868492⟩,⟨-31424757105942,-31424672211190⟩,⟨1133257637707,1133328640928⟩,⟨-280298146308,-280235966333⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨41622574242,41622576577⟩,⟨-837380484497,-837380472796⟩,⟨329378021832,329378040293⟩,⟨10451764292336,10451764322253⟩,⟨-6626565812353,-6626565719884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨504912996236,504913114842⟩,⟨936265460017,936268332320⟩,⟨528006164131,528007908785⟩,⟨-20972992813606,-20972907888937⟩,⟨-5493308174646,-5493237078956⟩,⟨-280298146308,-280235966333⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501892554988,501892567044⟩,⟨2532355881864,2532356003553⟩,⟨0,0⟩,⟨3194096148032,3194099067279⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨230476938420,230476998097⟩,⟨1590273368239,1590275018674⟩,⟨241018244892,241019047062⟩,⟨-3793987940415,-3793933821868⟩,⟨-1291437934870,-1291401345021⟩,⟨-127947311001,-127918924720⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-814175837308,-814174648564⟩,⟨5969041695238,5969061966654⟩,⟨-5620090876366,-5620071795846⟩,⟨-75250453592462,-75249901629474⟩,⟨31714453435462,31715069790966⟩,⟨10541188233992,10541875543654⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3492668431236,3492669716428⟩,⟨-13674904019273,-13674883747538⟩,⟨-9044610107573,-9044591026957⟩,⟨67675976458007,67676528441877⟩,⟨56569542779826,56570159139589⟩,⟨17984765083079,17985452394557⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨447899860621,447900025441⟩,⟨375785625286,375789008547⟩,⟨-186320347590,-186317542427⟩,⟨-13327669182979,-13327571715440⟩,⟨-6946700745388,-6946602625454⟩,⟨-3850278591161,-3850179402982⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨332181746482,332181746484⟩,⟨1921138871500,1921138871502⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-332181746484,-332181746482⟩,⟨-1921138871502,-1921138871500⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨767329881292,767329881294⟩,⟨-1921138871502,-1921138871500⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1324657687082,1324657714019⟩,⟨-8543923458348,-8543923390748⟩,⟨-3906175603021,-3906175572118⟩,⟨51028236999585,51028237006674⟩,⟨33109240425869,33109240506420⟩,⟨10665946286985,10665946288421⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1324657714019,-1324657687082⟩,⟨8543923390748,8543923458348⟩,⟨3906175572118,3906175603021⟩,⟨-51028237006674,-51028236999585⟩,⟨-33109240506420,-33109240425869⟩,⟨-10665946288421,-10665946286985⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-225146086243,-225146059306⟩,⟨8543923390748,8543923458348⟩,⟨3906175572118,3906175603021⟩,⟨-51028237006674,-51028236999585⟩,⟨-33109240506420,-33109240425869⟩,⟨-10665946288421,-10665946286985⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11363760525,-11363759165⟩,⟨459687081868,459687088693⟩,⟨107229229378,107229241703⟩,⟨-4734882775035,-4734882757529⟩,⟨1472979660985,1472979722930⟩,⟨2582022395976,2582022420747⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨436536100096,436536266276⟩,⟨835472707154,835476097240⟩,⟨-79091118212,-79088300724⟩,⟨-18062551958014,-18062454472969⟩,⟨-5473721084403,-5473622902524⟩,⟨-1268256195185,-1268156982235⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99471065088,-99471065088⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨5020586329,5020586330⟩,⟨31761459813,31761459816⟩,⟨39730142208,39730142208⟩,⟨-332972792220,-332972792215⟩,⟨251342618624,251342618624⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10998754334,10998754601⟩,⟨14085350667,14085352359⟩,⟨87038055949,87038058040⟩,⟨-941589576117,-941589558358⟩,⟨111463671483,111463684713⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1464239365585,1464239386469⟩,⟨-7212687966585,-7212687598078⟩,⟨-1344526159534,-1344526093732⟩,⟨104217202319208,104217209512961⟩,⟨21918058304785,21918059757141⟩,⟨4894958635076,4894958910824⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14647238520,14647239086⟩,⟨-53393032462,-53393024502⟩,⟨102460430335,102460435760⟩,⟨-396211944903,-396211774457⟩,⟨-220493933906,-220493848516⟩,⟨-163901353806,-163901334325⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14647239086,-14647238520⟩,⟨53393024502,53393032462⟩,⟨-102460435760,-102460430335⟩,⟨396211774457,396211944903⟩,⟨220493848516,220493933906⟩,⟨163901334325,163901353806⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114118304174,-114118303608⟩,⟨-824927787530,-824927779570⟩,⟨-102460435760,-102460430335⟩,⟨2595235030009,2595235200455⟩,⟨220493848516,220493933906⟩,⟨163901334325,163901353806⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨95802987204,95802989155⟩,⟨-617920688306,-617920683408⟩,⟨585286647846,585286663270⟩,⟨3690506297619,3690506298173⟩,⟨-3202628811696,-3202628772763⟩,⟨-2359903874752,-2359903874575⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨127582557256,127582561675⟩,⟨-1451354252434,-1451354189266⟩,⟨662285060430,662285100209⟩,⟨22102396178308,22102397539338⟩,⟨-5439032408949,-5439031790516⟩,⟨-4147640539850,-4147640354298⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-127582561675,-127582557256⟩,⟨1451354189266,1451354252434⟩,⟨-662285100209,-662285060430⟩,⟨-22102397539338,-22102396178308⟩,⟨5439031790516,5439032408949⟩,⟨4147640354298,4147640539850⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨971929066101,971929070520⟩,⟨1451354189266,1451354252434⟩,⟨-662285100209,-662285060430⟩,⟨-22102397539338,-22102396178308⟩,⟨5439031790516,5439032408949⟩,⟨4147640354298,4147640539850⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124640200411,124640200981⟩,⟨778700051855,778700062658⟩,⟨185988009955,185988016293⟩,⟨-2548270006001,-2548269747633⟩,⟨-658317201432,-658317074074⟩,⟨-147429402455,-147429355060⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11844337876,11844337994⟩,⟨171238496120,171238498624⟩,⟨21268734592,21268735826⟩,⟨699114028060,699114090006⟩,⟨107975322810,107975350390⟩,⟨-14926635712,-14926629475⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171472814531,171472970279⟩,⟨1684666142820,1684671701499⟩,⟨103124357798,103126931908⟩,⟨-2128438811586,-2128224015176⟩,⟨531616407661,531744665148⟩,⟨-517878979022,-517790397874⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171472970279,-171472814531⟩,⟨-1684671701499,-1684666142820⟩,⟨-103126931908,-103124357798⟩,⟨2128224015176,2128438811586⟩,⟨-531744665148,-531616407661⟩,⟨517790397874,517878979022⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨59003968141,59004183566⟩,⟨-94398333260,-94391124146⟩,⟨137891312984,137894689264⟩,⟨-1665763925239,-1665495010282⟩,⟨-1823182600018,-1823017752682⟩,⟨389843086873,389960054302⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27479312846516,27479338090635⟩,⟨-235744391121288,-235743764276429⟩,⟨-82395599356352,-82395189155358⟩,⟨3238217826123841,3238239999365757⟩,⟨1256767733808608,1256784475273670⟩,⟨295680013151585,295694260023028⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14129163499,14129163629⟩,⟨176546255758,176546259016⟩,⟨42167053532,42167055164⟩,⟨525245714118,525245805945⟩,⟨114189032864,114189075058⟩,⟨29496567538,29496582727⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353120143744,353120471391⟩,⟨1382885527239,1382897745141⟩,⟨-4965158764,-4958868856⟩,⟨-20966472459547,-20965970087978⟩,⟨-3267240228344,-3266930769880⟩,⟨-1783067009620,-1782851132239⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353120471391,-353120143744⟩,⟨-1382897745141,-1382885527239⟩,⟨4958868856,4965158764⟩,⟨20965970087978,20966472459547⟩,⟨3266930769880,3267240228344⟩,⟨1782851132239,1783067009620⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83415628705,83416122532⟩,⟨-547425037987,-547409429999⟩,⟨-74132249356,-74123141960⟩,⟨2903418129964,2904017986578⟩,⟨-2206790314523,-2206382674180⟩,⟨514594937054,514910027385⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨240472455437,240472455439⟩,⟨1548685374339,1548685374343⟩,⟨306482345164,306482345166⟩,⟨-3877393211067,-3877393211062⟩,⟨-1534659762588,-1534659762584⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1652114671986,-1652113179653⟩,⟨-4288889699407,-4288847143168⟩,⟨489729758889,489753124032⟩,⟨44939557899540,44941106787340⟩,⟨-8004771928304,-8003737403392⟩,⟨1736591801067,1737405289997⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187283062369,-187282892342⟩,⟨-1656253400792,-1656247501270⟩,⟨-223948077507,-223945166629⟩,⟨2848344759542,2848584573998⟩,⟨-296887779891,-296745641640⟩,⟨584065544190,584165943504⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨53189393068,53189563097⟩,⟨-107568026453,-107562126927⟩,⟨82534267657,82537178537⟩,⟨-1029048451525,-1028808637064⟩,⟨-1831547542479,-1831405404224⟩,⟨233251860478,233352259792⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4476399316,4476442161⟩,⟨-36538686222,-36537152056⟩,⟨6483039865,6483861207⟩,⟨123420983140,123484750761⟩,⟨-319035391646,-318994852254⟩,⟨38596465382,38625263838⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2573061951,2573078403⟩,⟨-10407341198,-10406737142⟩,⟨7985268172,7985575332⟩,⟨-78516725615,-78490896473⟩,⟨-193354162514,-193338388788⟩,⟨34958120937,34968780870⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4441930877,4441959369⟩,⟨-35495462361,-35494307119⟩,⟨5771072198,5771653978⟩,⟨89584380835,89637736109⟩,⟨-297614771502,-297583188374⟩,⟨28024834234,28045262665⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4441959369,-4441930877⟩,⟨35494307119,35495462361⟩,⟨-5771653978,-5771072198⟩,⟨-89637736109,-89584380835⟩,⟨297583188374,297614771502⟩,⟨-28045262665,-28024834234⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨34439947,34511284⟩,⟨-1044379103,-1041689695⟩,⟨711385887,712789009⟩,⟨33783247031,33900369926⟩,⟨-21452203272,-21380080752⟩,⟨10551202717,10600429604⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨59003968141,59004183566⟩,⟨-94398333260,-94391124146⟩,⟨137891312984,137894689264⟩,⟨-1665763925239,-1665495010282⟩,⟨-1823182600018,-1823017752682⟩,⟨389843086873,389960054302⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨34439947,34511284⟩,⟨-1044379103,-1041689695⟩,⟨711385887,712789009⟩,⟨33783247031,33900369926⟩,⟨-21452203272,-21380080752⟩,⟨10551202717,10600429604⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110380659507,110810156237⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨137009456742,140874927309⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110810156237,-110380659507⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438945657651,439375154381⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨54696744058,56294941656⟩,⟨-140874927309,-137009456742⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨165077403565,167105097893⟩,⟨958636700467,962502171034⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨54267247328,56724438386⟩,⟨-140874927309,-137009456742⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2084901581504,-2071478191616⟩,⟨6307600499723,6410824897636⟩,⟨2888157576485,2926494364249⟩,⟨-37379027951964,-36184996191977⟩,⟨-24386638702723,-23803101876114⟩,⟨-7789248469618,-7586508387803⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-316865846685,-311005570814⟩,⟨-878098931364,-831745179861⟩,⟨-399526834763,-382200805603⟩,⟨5317968804572,5791244388826⟩,⟨3401392322999,3634826166806⟩,⟨1122193976326,1199893376354⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨311005570814,316865846685⟩,⟨831745179861,878098931364⟩,⟨382200805603,399526834763⟩,⟨-5791244388826,-5317968804572⟩,⟨-3634826166806,-3401392322999⟩,⟨-1199893376354,-1122193976326⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-167105097893,-165077403565⟩,⟨-962502171034,-958636700467⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨932406529883,934434224211⟩,⟨-962502171034,-958636700467⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-181257213184,-178868713344⟩,⟨-1135000983900,-1127989720052⟩,⟨-518119592383,-516489916619⟩,⟨-1171635843507,-1157205414114⟩,⟨758908514181,766697804273⟩,⟨-244151953676,-242618474630⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-154043794632,-151684031437⟩,⟨-808644154580,-797885622352⟩,⟨-368922914591,-365561077022⟩,⟨971202149500,1005806496072⟩,⟨1362940765534,1379833431949⟩,⟨204889211834,208345865548⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151684031437,154043794632⟩,⟨797885622352,808644154580⟩,⟨365561077022,368922914591⟩,⟨-1005806496072,-971202149500⟩,⟨-1379833431949,-1362940765534⟩,⟨-208345865548,-204889211834⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨462689602251,470909641317⟩,⟨1629630802213,1686743085944⟩,⟨747761882625,768449749354⟩,⟨-6797050884898,-6289170954072⟩,⟨-5014659598755,-4764333088533⟩,⟨-1408239241902,-1327083188160⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨820590779153,830701794155⟩,⟨4031237683537,4102592495422⟩,⟨747761882625,768449749354⟩,⟨-19057924513556,-18335134742672⟩,⟨-5014659598755,-4764333088533⟩,⟨-1408239241902,-1327083188160⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨108534494656,113448876772⟩,⟨-281749854618,-274018913484⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10656128593006,11138632224219⟩,⟨25738296068539,28915304943042⟩,⟨-90184015111899,-82459368595964⟩,⟨124334063488424,150125229582700⟩,⟨-261674101645649,-172656288685936⟩,⟨1276175941365397,1460351040950789⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨7952913497219,8415446948758⟩,⟨58278597470866,63407482836802⟩,⟨-60888647912504,-53756519613469⟩,⟨88459775691124,151506510609218⟩,⟨-567498993043457,-457151017797987⟩,⟨812113815704953,978302264506529⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨98991376384,104675757312⟩,⟨-824262177988,-677073328953⟩,⟨624536403880,791518718261⟩,⟨7220555162465,11889269919565⟩,⟨-7092740352988,-1099788642020⟩,⟨-4898189049787,2476089639868⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1198503004160,1204187385088⟩,⟨-824262177988,-677073328953⟩,⟨624536403880,791518718261⟩,⟨7220555162465,11889269919565⟩,⟨-7092740352988,-1099788642020⟩,⟨-4898189049787,2476089639868⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨94785791296,99988338176⟩,⟨-756181541380,-618217735262⟩,⟨570247659574,726142555597⟩,⟨6072839156933,10559662883043⟩,⟨-6186278691995,-504788362606⟩,⟨-4973180058358,1975823243429⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨103319558202,109507432615⟩,⟨-903129037729,-732245775167⟩,⟨675427791383,867252625995⟩,⟨8003443770665,13779922359783⟩,⟨-8508953916464,-1347356072192⟩,⟨-5244257070394,3434572466112⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-104675757312,-98991376384⟩,⟨677073328953,824262177988⟩,⟨-791518718261,-624536403880⟩,⟨-11889269919565,-7220555162465⟩,⟨1099788642020,7092740352988⟩,⟨-2476089639868,4898189049787⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨994835870464,1000520251392⟩,⟨677073328953,824262177988⟩,⟨-791518718261,-624536403880⟩,⟨-11889269919565,-7220555162465⟩,⟨1099788642020,7092740352988⟩,⟨-2476089639868,4898189049787⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-109999119360,-103734513408⟩,⟨744062898281,910990321059⟩,⟨-874801623232,-686327974950⟩,⟨-13895041181066,-8438479372972⟩,⟨1673054357889,8563841167298⟩,⟨-3432637796237,4985158280983⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-100095664089,-93858775420⟩,⟨590764418475,765092766162⟩,⟨-737118862192,-541801752130⟩,⟨-11046430729303,-5079803503660⟩,⟨-507418450762,6843785508364⟩,⟨-2833936834623,6043558837944⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨3223894113,15648657195⟩,⟨-312364619254,32846990995⟩,⟨-61691070809,325450873865⟩,⟨-3042986958638,8700118856123⟩,⟨-9016372367226,5496429436172⟩,⟨-8078193905017,9478131304056⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1611947056,7824328598⟩,⟨-156182309627,16423495498⟩,⟨-30845535405,162725436933⟩,⟨-1521493479319,4350059428062⟩,⟨-4508186183613,2748214718086⟩,⟨-4039096952509,4739065652028⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7824328598,-1611947056⟩,⟨-16423495498,156182309627⟩,⟨-162725436933,30845535405⟩,⟨-4350059428062,1521493479319⟩,⟨-2748214718086,4508186183613⟩,⟨-4739065652028,4039096952509⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754299055018,760511455824⟩,⟨-16423495498,156182309627⟩,⟨-162725436933,30845535405⟩,⟨-4350059428062,1521493479319⟩,⟨-2748214718086,4508186183613⟩,⟨-4739065652028,4039096952509⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8912404699,9965346334⟩,⟨-156942892690,-121916711114⟩,⟨112456688332,150708403928⟩,⟨2134040162797,3499601863549⟩,⟨-2537229939662,-967204929896⟩,⟨-223146213964,1611057886445⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9965346334,-8912404699⟩,⟨121916711114,156942892690⟩,⟨-150708403928,-112456688332⟩,⟨-3499601863549,-2134040162797⟩,⟨967204929896,2537229939662⟩,⟨-1611057886445,223146213964⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1089546281442,1090599223077⟩,⟨121916711114,156942892690⟩,⟨-150708403928,-112456688332⟩,⟨-3499601863549,-2134040162797⟩,⟨967204929896,2537229939662⟩,⟨-1611057886445,223146213964⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-10010781184,-8948722048⟩,⟨122913017590,158378343673⟩,⟨-152086832240,-113375687260⟩,⟨-3554423857822,-2165219884651⟩,⟨987783078309,2582343509695⟩,⟨-1646830128721,213496495005⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-5005390592,-4474361024⟩,⟨61456508795,79189171837⟩,⟨-76043416120,-56687843630⟩,⟨-1777211928911,-1082609942325⟩,⟨493891539154,1291171754848⟩,⟨-823415064361,106748247503⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4474361024,5005390592⟩,⟨-79189171837,-61456508795⟩,⟨56687843630,76043416120⟩,⟨1082609942325,1777211928911⟩,⟨-1291171754848,-493891539154⟩,⟨-106748247503,823415064361⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766597744640,767128793472⟩,⟨-79189171837,-61456508795⟩,⟨56687843630,76043416120⟩,⟨1082609942325,1777211928911⟩,⟨-1291171754848,-493891539154⟩,⟨-106748247503,823415064361⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272386570360,272649805770⟩,⟨30479177778,39235723173⟩,⟨-37677100982,-28114172083⟩,⟨-874900465888,-533510040699⟩,⟨241801232474,634307484916⟩,⟨-402764471612,55786553491⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533195489280,1534257586944⟩,⟨-158378343674,-122913017590⟩,⟨113375687260,152086832240⟩,⟨2165219884650,3554423857822⟩,⟨-2582343509696,-987783078308⟩,⟨-213496495006,1646830128722⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1208297201313,1215201276419⟩,⟨-1006843923238,-817680409085⟩,⟨754233198054,966847482382⟩,⟨9826723421381,16191276561602⟩,⟨-10265993674642,-2348991836340⟩,⟨-5041581211698,4563067321648⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1317082774850,1330890925062⟩,⟨-2013687846476,-1635360818170⟩,⟨1508466396108,1933694964764⟩,⟨19653446842770,32382553123192⟩,⟨-20531987349277,-4697983672680⟩,⟨-10078294420117,9126134643294⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨198520304704,209987457472⟩,⟨-1681043321037,-1351048535477⟩,⟨1246215081488,1614264599713⟩,⟨13666490246833,25373094097857⟩,⟨-15608959829099,-1413176272478⟩,⟨-10783450746263,6206080324021⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨67911152347,72402247118⟩,⟨-571690153077,-449624413402⟩,⟨412959535356,550415127251⟩,⟨4305222163906,8393057205237⟩,⟨-5202497105354,-90878607742⟩,⟨-4073439986107,2141605097153⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379824869938,380455306260⟩,⟨3227535894,24299743604⟩,⟨-24487565881,-1489821945⟩,⟨-695739833513,130644558473⟩,⟨-296891541407,651258869698⟩,⟨-625381841103,480416866152⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177576445177,3182850611684⟩,⟨-203626618253,-26956496240⟩,⟨12443046639,205200528485⟩,⟨-1094315901792,5856204477245⟩,⟨-5483664965338,2487676061504⟩,⟨-4025692425392,5267023980653⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨196262479278,209588994519⟩,⟨-1668329221639,-1301074545995⟩,⟨1194217033110,1606846220806⟩,⟨12392031027550,24893481430302⟩,⟨-15629840211235,-114038835894⟩,⟨-12047478939828,6751765263543⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨394782783982,419576451991⟩,⟨-3349372542676,-2652123081472⟩,⟨2440432114598,3221110820519⟩,⟨26058521274383,50266575528159⟩,⟨-31238800040334,-1527215108372⟩,⟨-22830929686091,12957845587564⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517472530556,526031430527⟩,⟨-22719644170,216056715852⟩,⟨-225108231356,42670550168⟩,⟨-6022373941990,2149147139472⟩,⟨-3848005891532,6245217745504⟩,⟨-6564974813040,5635700420303⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355002194552,363846019390⟩,⟨-23572124061,224163533194⟩,⟨-233554677034,44271622160⟩,⟨-6253184593299,2275822121255⟩,⟨-4040353568706,6488640826300⟩,⟨-6820776620454,5897134860615⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨710004389104,727692038780⟩,⟨-47144248122,448327066388⟩,⟨-467109354068,88543244320⟩,⟨-12506369186598,4551644242510⟩,⟨-8080707137412,12977281652600⟩,⟨-13641553240908,11794269721230⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523230142946,1525345182245⟩,⟨-36461632560,34029875100⟩,⟨-37332716668,39630143908⟩,⟨-1334381978899,1420383695025⟩,⟨-1615138579800,1549446861354⟩,⟨-1824554381451,1869976342686⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨983618599190,1009522334709⟩,⟨-89534379621,644483225166⟩,⟨-672725694600,149063954598⟩,⟨-18262874257211,7282272737609⟩,⟨-12308941338737,19060419643887⟩,⟨-20166057251033,17631442749002⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67479453457,67609941277⟩,⟨15101465946,19458843422⟩,⟨-18685849254,-13929680630⟩,⟨-432214550193,-261537076339⟩,⟨117115851238,313024276170⟩,⟨-198312133370,30249351608⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50361465845,51080587147⟩,⟨258676517975,266973560285⟩,⟨31774283938,36856613358⟩,⟨-1387699160053,-1175245756494⟩,⟨-280401561843,-93373705746⟩,⟨-262541552542,-77538812547⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137938652912,2140901727303⟩,⟨-442002011168,-342787978556⟩,⟨316189638944,424443671798⟩,⟨6065989455850,9965307018908⟩,⟨-7250614330466,-2780143236834⟩,⟨-572444279510,4638044672796⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2981212582200,2987412442978⟩,⟨-925153843690,-716992393565⟩,⟨661357982861,888402506034⟩,⟨12745405151554,20953873144776⟩,⟨-15267959587043,-5868105599235⟩,⟨-1149288035443,9795950320036⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136549929843,138787783397⟩,⟨658394391001,692535966667⟩,⟨116445201029,141413717742⟩,⟨-3635919422373,-2550459143786⟩,⟨-1346590318005,-326958985186⟩,⟨-728503306028,304417176976⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8710606870609,8853360972098⟩,⟨-44901311235487,-41322186762059⟩,⟨-9168709870565,-7308340426701⟩,⟨552128127141691,691187854746039⟩,⟨89860588348934,180308938289040⟩,⟨-7473581478790,66223874647313⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7792473232405,8128759544501⟩,⟨-41947311485404,-31777225399770⟩,⟨-13835143185408,-5337735797120⟩,⟨294239173896970,700567932817945⟩,⟨-30185402965292,347246765410986⟩,⟨-171726769580558,213993244957011⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15584946464810,16257519089002⟩,⟨-83894622970808,-63554450799540⟩,⟨-27670286370816,-10675471594240⟩,⟨588478347793940,1401135865635890⟩,⟨-60370805930584,694493530821972⟩,⟨-343453539161116,427986489914022⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10909882818222,10952333724170⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145760,2173453475298114⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9810371190446,9852822096394⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145775,2173453475298112⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2406362562496,2411110103296⟩,⟨-12227224809080,-12080350374972⟩,⟨0,0⟩,⟨103760055435140,110865974497594⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7234523870652,7323387656377⟩,⟨-42699826665322,-41502504592958⟩,⟨-19492156483100,-19003386959674⟩,⟨476177262881390,497932181880570⟩,⟨265636010045993,276080400859894⟩,⟨99834826008136,103761860545725⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6135012242876,6223876028601⟩,⟨-42699826665322,-41502504592958⟩,⟨-19492156483100,-19003386959673⟩,⟨476177262881393,497932181880567⟩,⟨265636010045994,276080400859893⟩,⟨99834826008136,103761860545725⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1890220978496,1906032868032⟩,⟨-7652626280759,-7331843721156⟩,⟨-3493367552529,-3357143495976⟩,⟨30859149087244,40348242541953⟩,⟨22613410889944,27092543056801⟩,⟨6537722573895,8345731163925⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99256358666,99685855397⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139988741484,142016435813⟩,⟨666659707155,674068098321⟩,⟨305457405622,307506681612⟩,⟨-1685130754132,-1671622746438⟩,⟨-1538606602654,-1530712922518⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4296583540992,4317142971328⟩,⟨-19879851089839,-19412194096128⟩,⟨-3493367552529,-3357143495976⟩,⟨134619204522384,151214217039547⟩,⟨22613410889944,27092543056801⟩,⟨6537722573895,8345731163925⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨789565567964,839152903982⟩,⟨-6698745085352,-5304246162944⟩,⟨4880864229196,6442221641038⟩,⟨52117042548766,100533151056318⟩,⟨-62477600080668,-3054430216744⟩,⟨-45661859372182,25915691175128⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5086149108956,5156295875310⟩,⟨-26578596175191,-24716440259072⟩,⟨1387496676667,3085078145062⟩,⟨186736247071150,251747368095865⟩,⟨-39864189190724,24038112840057⟩,⟨-39124136798287,34261422339053⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459142611532,467489157937⟩,⟨1651256785506,1889777862013⟩,⟨125253671091,279704776274⟩,⟨-35939550632881,-26817001468279⟩,⟨-2506407796982,4645037927839⟩,⟨-3547141244241,3106269280567⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨40561487141,42690829047⟩,⟨-858958469043,-815998476851⟩,⟨328085346598,330673870673⟩,⟨10077101685192,10834308605811⟩,⟨-6659570832821,-6593775017748⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨499704098673,510179986984⟩,⟨792298316463,1073779385162⟩,⟨453339017689,610378646947⟩,⟨-25862448947689,-15982692862468⟩,⟨-9165978629803,-1948737089909⟩,⟨-3547141244241,3106269280567⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501398014948,502387228948⟩,⟨2512147284185,2552733193796⟩,⟨0,0⟩,⟨2027158573049,4364694834823⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227874482458,233110686100⟩,⟨1503019209392,1675113196506⟩,⟨206731132100,278893309814⟩,⟨-7275270477379,-277183027820⟩,⟨-3152323390460,528453642174⟩,⟨-1620754538073,1419311971614⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-839152903982,-789565567964⟩,⟨5304246162944,6698745085352⟩,⟨-6442221641038,-4880864229196⟩,⟨-100533151056318,-52117042548766⟩,⟨3054430216744,62477600080668⟩,⟨-25915691175128,45661859372182⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3457430637010,3527577403364⟩,⟨-14575604926895,-12713449010776⟩,⟨-9935589193567,-8238007725172⟩,⟨34086053466066,99097174490781⟩,⟨25667841106688,89570143137469⟩,⟨-19377968601233,54007590536107⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨440196675884,455633171333⟩,⟨213689631383,543957562538⟩,⟨-322797106923,-62277388082⟩,⟨-18938104433820,-7873659856745⟩,⟨-11835895500570,-1771028328293⟩,⟨-9187027144291,1296499737055⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨330154807130,334210195786⟩,⟨1917273400934,1925004342068⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-334210195786,-330154807130⟩,⟨-1925004342068,-1917273400934⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨765301431990,769356820646⟩,⟨-1925004342068,-1917273400934⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1315664868907,1333700663414⟩,⟨-8691787817992,-8399311721300⟩,⟨-3967737143154,-3845921406436⟩,⟨47048932973862,55028861641496⟩,⟨31228264089807,35001666043318⟩,⟨9911439234597,11423654382318⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1333700663414,-1315664868907⟩,⟨8399311721300,8691787817992⟩,⟨3845921406436,3967737143154⟩,⟨-55028861641496,-47048932973862⟩,⟨-35001666043318,-31228264089807⟩,⟨-11423654382318,-9911439234597⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-234189035638,-216153241131⟩,⟨8399311721300,8691787817992⟩,⟨3845921406436,3967737143154⟩,⟨-55028861641496,-47048932973862⟩,⟨-35001666043318,-31228264089807⟩,⟨-11423654382318,-9911439234597⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12081947282,-10668410502⟩,⟨441489250719,478419811697⟩,⟨96234293303,118405418587⟩,⟨-5066241306600,-4415402467288⟩,⟨1255193527705,1686975927993⟩,⟨2481374961362,2681903165752⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428114728602,444964760831⟩,⟨655178882102,1022377374235⟩,⟨-226562813620,56128030505⟩,⟨-24004345740420,-12289062324033⟩,⟨-10580701972865,-84052400300⟩,⟨-6705652182929,3978402902807⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99685855397,-99256358666⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4898874398,5142850717⟩,⟨30556755065,32966961924⟩,⟨39624999436,39835402372⟩,⟨-338628643393,-327321470890⟩,⟨250784818133,251900503000⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10721549142,11277715497⟩,⟨9684153649,18468977760⟩,⟨86722243560,87354729775⟩,⟨-1013497579770,-869258285119⟩,⟨105867709348,117030113883⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1455306619199,1473238367195⟩,⟨-7365542999962,-7062326006385⟩,⟨-1379627559524,-1310004173609⟩,⟨100665573379022,107864371272331⟩,⟨21061037767577,22798072728747⟩,⟨4683335644075,5112196106233⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14190974465,15111039070⟩,⟨-62730655853,-44119468561⟩,⟨100634140813,104272717488⟩,⟨-623823077513,-168582978388⟩,⟨-262860703100,-177918632941⟩,⟨-173551026864,-154213111059⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-15111039070,-14190974465⟩,⟨44119468561,62730655853⟩,⟨-104272717488,-100634140813⟩,⟨168582978388,623823077513⟩,⟨177918632941,262860703100⟩,⟨154213111059,173551026864⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114796894467,-113447333131⟩,⟨-834630840201,-815160659449⟩,⟨-104272717488,-100634140813⟩,⟨2367606233940,2822846333065⟩,⟨177918632941,262860703100⟩,⟨154213111059,173551026864⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨93293319282,98333333867⟩,⟨-639013860279,-597408075892⟩,⟨574386811438,595974187706⟩,⟨3350310113232,4042574564760⟩,⟨-3429660124832,-2971922840084⟩,⟨-2469290491286,-2249908180734⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨123482445886,131757078841⟩,⟨-1514943628590,-1389962346543⟩,⟨636869618795,687393732331⟩,⟨20650382015176,23624768177471⟩,⟨-6088993536772,-4782263447255⟩,⟨-4406842337825,-3889458841515⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-131757078841,-123482445886⟩,⟨1389962346543,1514943628590⟩,⟨-687393732331,-636869618795⟩,⟨-23624768177471,-20650382015176⟩,⟨4782263447255,6088993536772⟩,⟨3889458841515,4406842337825⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨967754548935,976029181890⟩,⟨1389962346543,1514943628590⟩,⟨-687393732331,-636869618795⟩,⟨-23624768177471,-20650382015176⟩,⟨4782263447255,6088993536772⟩,⟨3889458841515,4406842337825⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123213559500,126067048461⟩,⟨763740939685,794040742343⟩,⟨180067750925,191886027511⟩,⟨-2861796368054,-2242987798000⟩,⟨-792204260395,-523266189342⟩,⟨-201012178251,-93131011018⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11705467290,11985618566⟩,⟨168216143516,174282883530⟩,⟨20766810660,21773638120⟩,⟨619243852486,778545702398⟩,⟨94328061448,121590039974⟩,⟨-17818617597,-12045832720⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165918282673,177220883989⟩,⟨1469844065055,1900364405545⟩,⟨-7272197465,208296072580⟩,⟨-11553763458685,7338651293594⟩,⟨-5368412641655,6534789504027⟩,⟨-5103315957496,4091414818358⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177220883989,-165918282673⟩,⟨-1900364405545,-1469844065055⟩,⟨-208296072580,7272197465⟩,⟨-7338651293594,11553763458685⟩,⟨-6534789504027,5368412641655⟩,⟨-4091414818358,5103315957496⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50653598469,67192403427⟩,⟨-397345196153,205269131451⟩,⟨-1564940480,286165507279⟩,⟨-14613921770973,11276580430865⟩,⟨-9687112894487,5896866283829⟩,⟨-5712169356431,6522627929110⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26792797831622,28182844959061⟩,⟨-258586284575314,-213184055665489⟩,⟨-99620560796006,-65938276768284⟩,⟨2296687768609725,4193317844451945⟩,⟨481115747110254,2063652706686420⟩,⟨-437526521553911,1041155120868053⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13807567706,14454508990⟩,⟨171172795878,182085155294⟩,⟨40357533256,44002272498⟩,⟨404765162845,644166339033⟩,⟨68492700686,159874314662⟩,⟨12884598447,46102730607⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336461535055,370500116173⟩,⟨771670183119,1990087565498⟩,⟨-326213068643,299825844890⟩,⟨-46941735968703,5260670924715⟩,⟨-19135459393581,13137085095987⟩,⟨-13411480470433,10028524928586⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370500116173,-336461535055⟩,⟨-1990087565498,-771670183119⟩,⟨-299825844890,326213068643⟩,⟨-5260670924715,46941735968703⟩,⟨-13137085095987,19135459393581⟩,⟨-10028524928586,13411480470433⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57614612429,108503225776⟩,⟨-1334908683396,250707191116⟩,⟨-526388658510,382341099148⟩,⟨-29265016665135,34652673644670⟩,⟨-23717787068852,19051406993281⟩,⟨-16734177111515,17389883373240⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239245100150,241702291210⟩,⟨1544551022457,1552818407083⟩,⟨305457405622,307506681612⟩,⟨-3884154009684,-3870646001990⟩,⟨-1538606602654,-1530712922518⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1697401515372,-1608050855267⟩,⟨-5783425754112,-2795234702901⟩,⟨-440297219704,1462545012401⟩,⟨-18492622663220,108387447016420⟩,⟨-56256682165044,39150325954119⟩,⟨-40544803607752,43673408734929⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-194619496230,-180201522866⟩,⟨-1888934433860,-1430221426421⟩,⟨-346712663314,-95660077864⟩,⟨-7193214759073,12962148202985⟩,⟨-7012247586319,6310295659660⟩,⟨-4666233588222,5828278532488⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44625603920,61500768344⟩,⟨-344383411403,122596980662⟩,⟨-41255257692,211846603748⟩,⟨-11077368768757,9091502200995⟩,⟨-8550854188973,4779582737142⟩,⟨-5017390449888,5477807858958⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2654257917,6630755270⟩,⟨-120789043943,35577597048⟩,⟨-32322641521,51605000433⟩,⟨-3728996990927,4195299775466⟩,⟨-2890978370697,2001652859331⟩,⟨-1860341340786,1905409498424⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1811208244,3440022290⟩,⟨-38525912544,13714831780⟩,⟨-4615194570,23699119814⟩,⟨-1316015290171,1232791518874⟩,⟨-1089284630712,581930661942⟩,⟨-577189264694,694432629984⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3113731344,5963370815⟩,⟨-90728336148,11697397314⟩,⟨-18930199796,35552889434⟩,⟨-2421425066952,2799596431726⟩,⟨-2059574551823,1248082710533⟩,⟨-1140397221137,1259255496311⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5963370815,-3113731344⟩,⟨-11697397314,90728336148⟩,⟨-35552889434,18930199796⟩,⟨-2799596431726,2421425066952⟩,⟨-1248082710533,2059574551823⟩,⟨-1259255496311,1140397221137⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3309112898,3517023926⟩,⟨-132486441257,126305933196⟩,⟨-67875530955,70535200229⟩,⟨-6528593422653,6616724842418⟩,⟨-4139061081230,4061227411154⟩,⟨-3119596837097,3045806719561⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50653598469,67192403427⟩,⟨-397345196153,205269131451⟩,⟨-1564940480,286165507279⟩,⟨-14613921770973,11276580430865⟩,⟨-9687112894487,5896866283829⟩,⟨-5712169356431,6522627929110⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3309112898,3517023926⟩,⟨-132486441257,126305933196⟩,⟨-67875530955,70535200229⟩,⟨-6528593422653,6616724842418⟩,⟨-4139061081230,4061227411154⟩,⟨-3119596837097,3045806719561⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (103/1024) u, BivariateJet2.affineZ (647/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000023

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000024Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2521033809728,-2521033751872⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2521033809728,-2521033751872⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-117038806336,-117038806272⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-117038806336,-117038806272⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2106686595456,-2106686556608⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2106686595392,-2106686556608⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-175064630976,-175064630912⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-175064630976,-175064630912⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨90244075328,90244075392⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-98318664768,-98318664704⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨90244198144,90244198208⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-98318810624,-98318810560⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8074612416,-8074612352⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8074589440,-8074589376⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨188562740032,188562740096⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨188563008768,188563008832⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1931621925696,1931621964288⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1931621925696,1931621964288⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2518909148864,-2518909091008⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2113572976896,-2113572937984⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2099837978624,-2099837939840⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-176251005696,-176251005632⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-173880419200,-173880419136⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨87657520128,87657520192⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-95256093824,-95256093760⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨92852918464,92852918528⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-101423628224,-101423628160⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8570709696,-8570709632⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7598573632,-7598573568⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨182913613952,182913614016⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨194276546624,194276546688⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1923586934144,1923586972736⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1939692518784,1939692557376⟩



end LaneCBRB2Cell000024Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000024
open Set LaneCBRB2Cell000024Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111024904601,111024904602⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨127345780326,127345780327⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111024904602,-111024904601⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438730909286,438730909287⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50813951016,50813951018⟩,⟨-127345780327,-127345780326⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161838855617,161838855620⟩,⟨972165847449,972165847450⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨50813951015,50813951019⟩,⟨-127345780327,-127345780326⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2521033809728,-2521033751872⟩,⟨10888780530353,10888780530452⟩,⟨0,0⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-254565328054,-254565322209⟩,⟨-1421522181962,-1421522124086⟩,⟨0,0⟩,⟨10888780530155,10888780530650⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨254565322209,254565328054⟩,⟨1421522124086,1421522181962⟩,⟨0,0⟩,⟨-10888780530650,-10888780530155⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988486723174,988486723175⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117038806336,-117038806272⟩,⟨-1223006633547,-1223006633545⟩,⟨0,0⟩,⟨-1360372357977,-1360372357971⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105220629994,-105220629935⟩,⟨-982472821506,-982472821438⟩,⟨0,0⟩,⟨1223006633540,1223006633552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105220629935,105220629994⟩,⟨982472821438,982472821506⟩,⟨0,0⟩,⟨-1223006633552,-1223006633540⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨359785952144,359785958048⟩,⟨2403994945524,2403995003468⟩,⟨0,0⟩,⟨-12111787164202,-12111787163695⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2106686595456,-2106686556608⟩,⟨6604765272850,6604765272981⟩,⟨2980679357726,2980679357790⟩,⟨-39674818536853,-39674818535282⟩,⟨-25374873529604,-25374873528732⟩,⟨-8080359688349,-8080359688008⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310086532190,-310086526465⟩,⟨-890523648202,-890523613811⟩,⟨-401886417779,-401886402255⟩,⟨5839799294724,5839799295310⟩,⟨3642631071753,3642631110919⟩,⟨1189360923353,1189360923483⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨310086526465,310086532190⟩,⟨890523613811,890523648202⟩,⟨401886402255,401886417779⟩,⟨-5839799295310,-5839799294724⟩,⟨-3642631110919,-3642631071753⟩,⟨-1189360923483,-1189360923353⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161838855620,-161838855617⟩,⟨-972165847450,-972165847449⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937672772156,937672772159⟩,⟨-972165847450,-972165847449⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175064630976,-175064630912⟩,⟨-1139958080409,-1139958080402⟩,⟨-514454243048,-514454243044⟩,⟨-1181892389549,-1181892389535⟩,⟨755904400224,755904400236⟩,⟨-240709749224,-240709749219⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149296591039,-149296590983⟩,⟨-817377256803,-817377256735⟩,⟨-368876018478,-368876018446⟩,⟨1007927779281,1007927779313⟩,⟨1379316988638,1379316988725⟩,⟨205279300491,205279300502⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149296590983,149296591039⟩,⟨817377256735,817377256803⟩,⟨368876018446,368876018478⟩,⟨-1007927779313,-1007927779281⟩,⟨-1379316988725,-1379316988638⟩,⟨-205279300502,-205279300491⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨459383117448,459383123229⟩,⟨1707900870546,1707900905005⟩,⟨770762420701,770762436257⟩,⟨-6847727074623,-6847727074005⟩,⟨-5021948099644,-5021948060391⟩,⟨-1394640223985,-1394640223844⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨819169069592,819169081277⟩,⟨4111895816070,4111895908473⟩,⟨770762420701,770762436257⟩,⟨-18959514238825,-18959514237700⟩,⟨-5021948099644,-5021948060391⟩,⟨-1394640223985,-1394640223844⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨101627902030,101627902038⟩,⟨-254691560654,-254691560652⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11895609329439,11895609330377⟩,⟨29811806051926,29811806056863⟩,⟨-102707453244464,-102707453228031⟩,⟨149423834536708,149423834574405⟩,⟨-257397043926042,-257397043758444⟩,⟨1773565465449887,1773565465877547⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8862584969962,8862585097082⟩,⟨66697262498324,66697263822044⟩,⟨-68181253911550,-68181252638829⟩,⟨129179616289848,129179622981973⟩,⟨-609302669213003,-609302656805463⟩,⟨1162274005003583,1162274027102661⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨94050970624,94051104000⟩,⟨-700351604622,-700349576115⟩,⟨715932102697,715934175493⟩,⟨9018681579654,9018731632899⟩,⟨-4208079694623,-4208014066366⟩,⟨-1362457681159,-1362374213491⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1193562598400,1193562731776⟩,⟨-700351604622,-700349576115⟩,⟨715932102697,715934175493⟩,⟨9018681579654,9018731632899⟩,⟨-4208079694623,-4208014066366⟩,⟨-1362457681159,-1362374213491⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨90244075328,90244198208⟩,⟨-645164932151,-645162991391⟩,⟨659517636280,659519619442⟩,⟨7929455793229,7929505108319⟩,⟨-3489502532198,-3489439314381⟩,⟨-1650697416622,-1650618006721⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨97963450606,97963594945⟩,⟨-757834175500,-757831745702⟩,⟨774693229917,774695712862⟩,⟨10169845786901,10169910251296⟩,⟨-4973559226002,-4973479360555⟩,⟨-1044850362390,-1044751887348⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-94051104000,-94050970624⟩,⟨700349576115,700351604622⟩,⟨-715934175493,-715932102697⟩,⟨-9018731632899,-9018681579654⟩,⟨4208014066366,4208079694623⟩,⟨1362374213491,1362457681159⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1005460523776,1005460657152⟩,⟨700349576115,700351604622⟩,⟨-715934175493,-715932102697⟩,⟨-9018731632899,-9018681579654⟩,⟨4208014066366,4208079694623⟩,⟨1362374213491,1362457681159⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-98318810624,-98318664704⟩,⟨765860401367,765862721216⟩,⟨-782902890828,-782900520287⟩,⟨-10395806932961,-10395747657693⟩,⟨5146958666678,5147034347273⟩,⟨932348046099,932442894852⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-89908731698,-89908586333⟩,⟨637723736428,637726225080⟩,⟨-651915403744,-651912860641⟩,⟨-7724456850355,-7724389930458⟩,⟨3333039580460,3333121747426⟩,⟨1750314520374,1750415052438⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8054718908,8055008612⟩,⟨-120110439072,-120105520622⟩,⟨122777826173,122782852221⟩,⟨2445388936546,2445520320838⟩,⟨-1640519645542,-1640357613129⟩,⟨705464157984,705663165090⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4027359454,4027504306⟩,⟨-60055219536,-60052760311⟩,⟨61388913086,61391426111⟩,⟨1222694468273,1222760160419⟩,⟨-820259822771,-820178806564⟩,⟨352732078992,352831582545⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4027504306,-4027359454⟩,⟨60052760311,60055219536⟩,⟨-61391426111,-61388913086⟩,⟨-1222760160419,-1222694468273⟩,⟨820178806564,820259822771⟩,⟨-352831582545,-352732078992⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758095879310,758096043426⟩,⟨60052760311,60055219536⟩,⟨-61391426111,-61388913086⟩,⟨-1222760160419,-1222694468273⟩,⟨820178806564,820259822771⟩,⟨-352831582545,-352732078992⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8045012760,8045035578⟩,⟨-119814724900,-119814207954⟩,⟨122480031058,122480559362⟩,⟨2435090728030,2435106647410⟩,⟨-1631961257974,-1631943727246⟩,⟨699252498826,699272507533⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8045035578,-8045012760⟩,⟨119814207954,119814724900⟩,⟨-122480559362,-122480031058⟩,⟨-2435106647410,-2435090728030⟩,⟨1631943727246,1631961257974⟩,⟨-699272507533,-699252498826⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091466592198,1091466615016⟩,⟨119814207954,119814724900⟩,⟨-122480559362,-122480031058⟩,⟨-2435106647410,-2435090728030⟩,⟨1631943727246,1631961257974⟩,⟨-699272507533,-699252498826⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8074612416,-8074589376⟩,⟨120697337880,120697861161⟩,⟨-123383345087,-123382810308⟩,⟨-2466304946003,-2466288743111⟩,⟨1657516677820,1657534489563⟩,⟨-718272386662,-718252095723⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4037306208,-4037294688⟩,⟨60348668940,60348930581⟩,⟨-61691672544,-61691405154⟩,⟨-1233152473002,-1233144371555⟩,⟨828758338910,828767244782⟩,⟨-359136193331,-359126047861⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4037294688,4037306208⟩,⟨-60348930581,-60348668940⟩,⟨61691405154,61691672544⟩,⟨1233144371555,1233152473002⟩,⟨-828767244782,-828758338910⟩,⟨359126047861,359136193331⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766160678304,766160709088⟩,⟨-60348930581,-60348668940⟩,⟨61691405154,61691672544⟩,⟨1233144371555,1233152473002⟩,⟨-828767244782,-828758338910⟩,⟨359126047861,359136193331⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272866648049,272866653754⟩,⟨29953551988,29953681225⟩,⟨-30620139841,-30620007764⟩,⟨-608776661853,-608772682007⟩,⟨407985931811,407990314494⟩,⟨-174818126884,-174813124706⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532321356608,1532321418176⟩,⟨-120697861162,-120697337880⟩,⟨123382810308,123383345088⟩,⟨2466288743110,2466304946004⟩,⟨-1657534489564,-1657516677820⟩,⟨718252095722,718272386662⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1202360143099,1202360302595⟩,⟨-837501768936,-837499120991⟩,⟨856133175697,856135881548⟩,⟨11951524406201,11951594345574⟩,⟨-6224829422744,-6224742225234⟩,⟨-410059602865,-409951812441⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1305208658422,1305208977414⟩,⟨-1675003537872,-1674998241982⟩,⟨1712266351395,1712271763097⟩,⟨23903048812415,23903188691143⟩,⟨-12449658845487,-12449484450474⟩,⟨-820119057833,-819903772780⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨188562740032,188563008832⟩,⟨-1411027926129,-1411023119999⟩,⟨1442417877738,1442422789101⟩,⟨18325190200554,18325325291678⟩,⟨-8636548471238,-8636386389321⟩,⟨-2583150388043,-2582955976294⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨64846656892,64846762891⟩,⟨-477744615706,-477742894900⟩,⟨488372502802,488374261235⟩,⟨6037138392087,6037183371199⟩,⟨-2753042786803,-2752986451034⟩,⟨-1049522704633,-1049452893293⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380277372015,380277395246⟩,⟨11790731083,11791043361⟩,⟨-12053389793,-12053070651⟩,⟨-242929914664,-242920243340⟩,⟨163955677367,163966295188⟩,⟨-72256215261,-72244135470⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179063059566,3179063253774⟩,⟨-98571399277,-98568776634⟩,⟨100761896815,100764577107⟩,⟨2036889853520,2036971277394⟩,⟨-1376982964069,-1376893701089⟩,⟨610337731789,610439130295⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨187493798386,187494116320⟩,⟨-1387136206756,-1387130982752⟩,⟨1417994149155,1417999487441⟩,⟨17661214051823,17661352754341⟩,⟨-8128763070853,-8128591656533⟩,⟨-2909020643848,-2908809867652⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨376056538418,376057125152⟩,⟨-2798164132885,-2798154102751⟩,⟨2860412026893,2860422276542⟩,⟨35986404252377,35986678046019⟩,⟨-16765311542091,-16764978045854⟩,⟨-5492171031891,-5491765843946⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522695120004,522695346316⟩,⟨82810857080,82814266202⟩,⟨-84656853206,-84653369496⟩,⟨-1679588068605,-1679496578906⟩,⟨1124294245492,1124406758284⟩,⟨-479688657058,-479550778224⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360390019168,360390253227⟩,⟨85645164537,85648708884⟩,⟨-87554361196,-87550739296⟩,⟨-1730290090387,-1730194535166⟩,⟨1155838729164,1155955915033⟩,⟨-489017058988,-488873770656⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720780038336,720780506454⟩,⟨171290329074,171297417768⟩,⟨-175108722392,-175101478592⟩,⟨-3460580180774,-3460389070332⟩,⟨2311677458328,2311911830066⟩,⟨-978034117976,-977747541312⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524276321030,1524276405416⟩,⟨-883653208,-882612980⟩,⟨902250946,903314030⟩,⟨31182095700,31214217974⟩,⟨-25590762318,-25555419846⟩,⟨18979588189,19019887836⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨999232675082,999233379364⟩,⟨236884145689,236894668338⟩,⟨-242165487593,-242154734633⟩,⟨-4777310115512,-4777023503041⟩,⟨3188232751800,3188581366179⟩,⟨-1343715282704,-1343291143465⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67717526342,67717529174⟩,⟨14867192162,14867256622⟩,⟨-15198047724,-15197981850⟩,⟨-300529127939,-300527132173⟩,⟨200832014808,200834208748⟩,⟨-85064043421,-85061544103⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50451583818,50451586649⟩,⟨264322950179,264323014646⟩,⟨36147279148,36147331332⟩,⟨-1280396588963,-1280394565331⟩,⟨-206084459450,-206082514381⟩,⟨-170577180083,-170575220723⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135501508671,2135501680279⟩,⟨-336418302662,-336416830612⟩,⟨343901984294,343903488692⟩,⟨6900726948514,6900772616436⟩,⟨-4647095384972,-4647045318234⟩,⟨2029658105279,2029714982222⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2976116383074,2976116741814⟩,⟨-703268102328,-703264996812⟩,⟨718912390465,718915564233⟩,⟨14481069086107,14481165615121⟩,⟨-9771182075699,-9771076529775⟩,⟨4300800430370,4300920003800⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136560434068,136560458193⟩,⟨683189565141,683189970190⟩,⟨130829701811,130830002338⟩,⟨-3139390849926,-3139378912509⟩,⟨-856470496998,-856459356134⟩,⟨-217098162738,-217087028883⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8852678407874,8852679971804⟩,⟨-44288539409789,-44288497503870⟩,⟨-8481198447510,-8481175968916⟩,⟨646649782684016,646651388755091⟩,⟨140380761364696,140381793417032⟩,⟨30323427103689,30324237110711⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8045286019424,8045293111222⟩,⟨-38342048119222,-38341896606954⟩,⟨-9657478720000,-9657365937446⟩,⟨530124595483848,530129649493383⟩,⟨161174249675823,161178617284568⟩,⟨20474719025267,20479067223606⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16090572038848,16090586222444⟩,⟨-76684096238444,-76683793213908⟩,⟨-19314957440000,-19314731874892⟩,⟨1060249190967696,1060259298986766⟩,⟨322348499351646,322357234569136⟩,⟨40949438050534,40958134447212⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10888780530353,10888780530452⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239700,2135836853297982⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9789268902577,9789268902676⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239713,2135836853297977⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2403994945600,2403995003456⟩,⟨-12111787164150,-12111787163733⟩,⟨0,0⟩,⟨106474359377039,106474359411671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7469935541642,7469935541782⟩,⟨-44871895495604,-44871895493875⟩,⟨-20250338523881,-20250338523074⟩,⟨539090864703946,539090864735376⟩,⟨294037274468438,294037274484830⟩,⟨109793774795810,109793774802487⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6370423913866,6370423914006⟩,⟨-44871895495604,-44871895493875⟩,⟨-20250338523882,-20250338523073⟩,⟨539090864703954,539090864735369⟩,⟨294037274468440,294037274484828⟩,⟨109793774795810,109793774802487⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1931621925696,1931621964288⟩,⟨-7744723353596,-7744723353052⟩,⟨-3495133600931,-3495133600680⟩,⟨38492926137051,38492926154661⟩,⟨26130777924779,26130777933420⟩,⟨7839649936989,7839649940660⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99813991382,99813991384⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138017538473,138017538477⟩,⟨685976589873,685976589882⟩,⟨309575916304,309575916309⟩,⟨-1719138590394,-1719138590390⟩,⟨-1551667833084,-1551667833072⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4335616871296,4335616967744⟩,⟨-19856510517746,-19856510516785⟩,⟨-3495133600931,-3495133600680⟩,⟨144967285514090,144967285566332⟩,⟨26130777924779,26130777933420⟩,⟨7839649936989,7839649940660⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨752113076836,752114250304⟩,⟨-5596328265770,-5596308205502⟩,⟨5720824053786,5720844553084⟩,⟨71972808504754,71973356092038⟩,⟨-33530623084182,-33529956091708⟩,⟨-10984342063782,-10983531687892⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5087729948132,5087731218048⟩,⟨-25452838783516,-25452818722287⟩,⟨2225690452855,2225710952404⟩,⟨216940094018844,216940641658370⟩,⟨-7399845159403,-7399178158288⟩,⟨-3144692126793,-3143881747232⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461865632311,461865747605⟩,⟨1749630738826,1749633573500⟩,⟨202048838837,202050699797⟩,⟨-31106693318533,-31106609043731⟩,⟨1104445174274,1104522084454⟩,⟨-285476083127,-285402516623⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨222049809202,222049809204⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-222049809204,-222049809202⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨877461818572,877461818574⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1918500653850,1918500700027⟩,⟨-14473763903941,-14473763787873⟩,⟨0,0⟩,⟨133418678423327,133418678452828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨818989026074,818989072251⟩,⟨-14473763903941,-14473763787873⟩,⟨0,0⟩,⟨133418678423327,133418678452828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37849593584,37849595722⟩,⟨-763760847405,-763760836637⟩,⟨326795816458,326795834885⟩,⟨9518658478127,9518658506891⟩,⟨-6594360098773,-6594360006268⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨499715225895,499715343327⟩,⟨985869891421,985872736863⟩,⟨528844655295,528846534682⟩,⟨-21588034840406,-21587950536840⟩,⟨-5489914924499,-5489837921814⟩,⟨-285476083127,-285402516623⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502882001783,502882013886⟩,⟨2533615820870,2533615942923⟩,⟨0,0⟩,⟨3256741201878,3256744126778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228554011409,228554070620⟩,⟨1602404724282,1602406362624⟩,⟨241876895312,241877760707⟩,⟨-3850036739606,-3849982934568⟩,⟨-1292292188608,-1292252520175⟩,⟨-130567775704,-130534125558⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-752114250304,-752113076836⟩,⟨5596308205502,5596328265770⟩,⟨-5720844553084,-5720824053786⟩,⟨-71973356092038,-71972808504754⟩,⟨33529956091708,33530623084182⟩,⟨10983531687892,10984342063782⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3583502620992,3583503890908⟩,⟨-14260202312244,-14260182251015⟩,⟨-9215978154015,-9215957654466⟩,⟨72993929422052,72994477061578⟩,⟨59660734016487,59661401017602⟩,⟨18823181624881,18823992004442⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449823538347,449823697769⟩,⟨445689589858,445692900442⟩,⟨-147884304174,-147881373337⟩,⟨-14233980684136,-14233884922844⟩,⟨-7333019792796,-7332915836219⟩,⟨-3967984425322,-3967870753275⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨323677711234,323677711240⟩,⟨1944331694898,1944331694900⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-323677711240,-323677711234⟩,⟨-1944331694900,-1944331694898⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨775833916536,775833916542⟩,⟨-1944331694900,-1944331694898⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1362984952611,1362984979853⟩,⟨-8880609002232,-8880608933555⟩,⟨-4007749987095,-4007749956095⟩,⟨54552165066479,54552165081070⟩,⟨34662865246413,34662865330738⟩,⟨11110349883615,11110349886663⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1362984979853,-1362984952611⟩,⟨8880608933555,8880609002232⟩,⟨4007749956095,4007749987095⟩,⟨-54552165081070,-54552165066479⟩,⟨-34662865330738,-34662865246413⟩,⟨-11110349886663,-11110349883615⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-263473352077,-263473324835⟩,⟨8880608933555,8880609002232⟩,⟨4007749956095,4007749987095⟩,⟨-54552165081070,-54552165066479⟩,⟨-34662865330738,-34662865246413⟩,⟨-11110349886663,-11110349883615⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12176426033,-12176424772⟩,⟨440933075404,440933081768⟩,⟨80086198631,80086210950⟩,⟨-4578239177815,-4578239161016⟩,⟨1740920584906,1740920647179⟩,⟨2684907294598,2684907319528⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437647112314,437647272997⟩,⟨886622665262,886625982210⟩,⟨-67798105543,-67795162387⟩,⟨-18812219861951,-18812124083860⟩,⟨-5592099207890,-5591995189040⟩,⟨-1283077130724,-1282963433747⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99813991384,-99813991382⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4612905530,4612905532⟩,⟨28991427138,28991427145⟩,⟨39828121951,39828121953⟩,⟨-304883706108,-304883706097⟩,⟨250313839737,250313839741⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10085751981,10085752229⟩,⟨12573504402,12573505969⟩,⟨87081028926,87081031027⟩,⟨-858616417897,-858616401312⟩,⟨108560442911,108560456131⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1475795226218,1475795247271⟩,⟨-7407892539235,-7407892161404⟩,⟨-1388587023642,-1388586955997⟩,⟨108526217851771,108526225353639⟩,⟨22987704484284,22987706004369⟩,⟨5125614195800,5125614485053⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13537378096,13537378623⟩,⟨-51075631670,-51075624188⟩,⟨104145167019,104145172441⟩,⟨-326381154258,-326380992504⟩,⟨-246004727014,-246004641227⟩,⟨-172934511148,-172934491315⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13537378623,-13537378096⟩,⟨51075624188,51075631670⟩,⟨-104145172441,-104145167019⟩,⟨326380992504,326381154258⟩,⟨246004641227,246004727014⟩,⟨172934491315,172934511148⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113351370007,-113351369478⟩,⟨-826386194386,-826386186902⟩,⟨-104145172441,-104145167019⟩,⟨2525404248056,2525404409810⟩,⟨246004641227,246004727014⟩,⟨172934491315,172934511148⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨89269944430,89269946221⟩,⟨-581643598239,-581643593713⟩,⟨609234754168,609234769596⟩,⟨3572943879370,3572943880465⟩,⟨-3409506229334,-3409506189989⟩,⟨-2426970875386,-2426970874979⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨119820613540,119820617654⟩,⟨-1382149117923,-1382149057966⟩,⟨704991773930,704991814059⟩,⟨21444583576101,21444584892580⟩,⟨-6080067563718,-6080066929960⟩,⟨-4380217232717,-4380217039931⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-119820617654,-119820613540⟩,⟨1382149057966,1382149117923⟩,⟨-704991814059,-704991773930⟩,⟨-21444584892580,-21444583576101⟩,⟨6080066929960,6080067563718⟩,⟨4380217039931,4380217232717⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨979691010122,979691014236⟩,⟨1382149057966,1382149117923⟩,⟨-704991814059,-704991773930⟩,⟨-21444584892580,-21444583576101⟩,⟨6080066929960,6080067563718⟩,⟨4380217039931,4380217232717⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122976909261,122976909782⟩,⟨784717402926,784717413034⟩,⟨187344546547,187344552752⟩,⟨-2499027373063,-2499027126457⟩,⟨-670049286004,-670049158679⟩,⟨-159131823069,-159131774935⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11685672654,11685672765⟩,⟨170388386328,170388388668⟩,⟨21473165008,21473166228⟩,⟨721513206786,721513265070⟩,⟨105827265762,105827293258⟩,⟨-15927340333,-15927334020⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171011522672,171011675041⟩,⟨1678510079610,1678515540154⟩,⟨108964046693,108966740820⟩,⟨-1939837585246,-1939625644991⟩,⟨483837963095,483973600986⟩,⟨-552304389286,-552202808184⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171011675041,-171011522672⟩,⟨-1678515540154,-1678510079610⟩,⟨-108966740820,-108964046693⟩,⟨1939625644991,1939837585246⟩,⟨-483973600986,-483837963095⟩,⟨552202808184,552304389286⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57542336368,57542547948⟩,⟨-76110815872,-76103716986⟩,⟨132910154492,132913714014⟩,⟨-1910411094615,-1910145349322⟩,⟨-1776265789594,-1776090483270⟩,⟨421635032480,421770263728⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28267915465430,28267940947938⟩,⟨-248057243421287,-248056608462096⟩,⟨-85081359971023,-85080917929754⟩,⟨3506250607804438,3506273168553652⟩,⟨1328518875190253,1328537121860253⟩,⟨309463231298589,309480045813559⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13754579605,13754579723⟩,⟨175536335254,175536338262⟩,⟨41907793822,41907795390⟩,⟨561083177044,561083263435⟩,⟨117528425878,117528467300⟩,⟨28246066488,28246081638⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353623630450,353623952264⟩,⟨1409828797082,1409840912466⟩,⟨13085468198,13092018720⟩,⟨-20916982485867,-20916480557207⟩,⟨-3396872082630,-3396544531022⟩,⟨-1888247771521,-1888002409940⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353623952264,-353623630450⟩,⟨-1409840912466,-1409828797082⟩,⟨-13092018720,-13085468198⟩,⟨20916480557207,20916982485867⟩,⟨3396544531022,3396872082630⟩,⟨1888002409940,1888247771521⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84023160050,84023642547⟩,⟨-523218247204,-523202814872⟩,⟨-80890124263,-80880630585⟩,⟨2104260695256,2104858402007⟩,⟨-2195554676868,-2195123106410⟩,⟨604925279216,605284337774⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237831529855,237831529861⟩,⟨1563438408445,1563438408456⟩,⟨309575916304,309575916309⟩,⟨-3918161845946,-3918161845942⟩,⟨-1551667833084,-1551667833072⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1658818284823,-1658816814859⟩,⟨-4188064245902,-4188022199631⟩,⟨467111415041,467136101210⟩,⟨42922883785824,42924417847913⟩,⟨-7852217724111,-7851113859700⟩,⟨1967260861473,1968202856588⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185533596375,-185533431178⟩,⟨-1652314305911,-1652308536824⟩,⟨-230399247417,-230396226297⟩,⟨2593022073938,2593257480892⟩,⟨-247576486806,-247427120855⟩,⟨619292838536,619406901791⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52297933480,52298098683⟩,⟨-88875897466,-88870128368⟩,⟨79176668887,79179690012⟩,⟨-1325139772008,-1324904365050⟩,⟨-1799244319890,-1799094953927⟩,⟨269165007413,269279070670⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4397305873,4397347294⟩,⟨-33198756742,-33197272527⟩,⟨5923454708,5924297463⟩,⟨36561446630,36623171096⟩,⟨-308294780459,-308252857118⟩,⟨44322503548,44354749383⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2487535172,2487550888⟩,⟨-8454736338,-8454160818⟩,⟨7532027962,7532339154⟩,⟨-111693936287,-111669278704⟩,⟨-183962079988,-183946010932⟩,⟨37008646447,37020448366⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4370101559,4370129257⟩,⟨-32375053588,-32373931514⟩,⟨5324825600,5325422527⟩,⟨9961077434,10013057726⟩,⟨-290248341623,-290215710081⟩,⟨34865528986,34888354405⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4370129257,-4370101559⟩,⟨32373931514,32375053588⟩,⟨-5325422527,-5324825600⟩,⟨-10013057726,-9961077434⟩,⟨290215710081,290248341623⟩,⟨-34888354405,-34865528986⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨27176616,27245735⟩,⟨-824825228,-822218939⟩,⟨598032181,599471863⟩,⟨26548388904,26662093662⟩,⟨-18079070378,-18004515495⟩,⟨9434149143,9489220397⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57542336368,57542547948⟩,⟨-76110815872,-76103716986⟩,⟨132910154492,132913714014⟩,⟨-1910411094615,-1910145349322⟩,⟨-1776265789594,-1776090483270⟩,⟨421635032480,421770263728⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨27176616,27245735⟩,⟨-824825228,-822218939⟩,⟨598032181,599471863⟩,⟨26548388904,26662093662⟩,⟨-18079070378,-18004515495⟩,⟨9434149143,9489220397⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110810156236,111239652967⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨125413045043,129278515610⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111239652967,-110810156236⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438516160921,438945657652⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50018249604,51610407404⟩,⟨-129278515610,-125413045043⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160828405840,162850060371⟩,⟨970233112166,974098582733⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49588752873,52039904135⟩,⟨-129278515610,-125413045043⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2523162584128,-2518909091008⟩,⟨10867759718499,10909882818322⟩,⟨0,0⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-255273089568,-253858806826⟩,⟨-1427896175006,-1415135790242⟩,⟨0,0⟩,⟨10783350251024,10993966380516⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨253858806826,255273089568⟩,⟨1415135790242,1427896175006⟩,⟨0,0⟩,⟨-10993966380516,-10783350251024⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988271974809,988701471540⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117277700736,-116799963712⟩,⟨-1223272389009,-1222740993529⟩,⟨0,0⟩,⟨-1360963631407,-1359781469778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105458307459,-104983092383⟩,⟨-983189504844,-981756293837⟩,⟨0,0⟩,⟨1221677971627,1224334949129⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104983092383,105458307459⟩,⟨981756293837,983189504844⟩,⟨0,0⟩,⟨-1224334949129,-1221677971627⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨358841899209,360731397027⟩,⟨2396892084079,2411085679850⟩,⟨0,0⟩,⟨-12218301329645,-12005028222651⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2113572976896,-2099837939840⟩,⟨6550704286196,6659474815542⟩,⟨2960721149269,3000874453922⟩,⟨-40334821113750,-39027988027735⟩,⟨-25692435055601,-25063027334639⟩,⟨-8190224878672,-7972512070167⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313043971697,-307148719354⟩,⟨-914305122770,-866599678978⟩,⟨-410705631808,-393011110598⟩,⟨5586928054546,6091032320445⟩,⟨3519709044884,3764713653753⟩,⟨1148573144679,1229850763258⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307148719354,313043971697⟩,⟨866599678978,914305122770⟩,⟨393011110598,410705631808⟩,⟨-6091032320445,-5586928054546⟩,⟨-3764713653753,-3519709044884⟩,⟨-1229850763258,-1148573144679⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162850060371,-160828405840⟩,⟨-974098582733,-970233112166⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨936661567405,938683221936⟩,⟨-974098582733,-970233112166⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-176251005696,-173880419136⟩,⟨-1143457525735,-1136467088736⟩,⟨-515261724561,-513648914386⟩,⟨-1189159878013,-1174664652153⟩,⟨752039422657,759762098089⟩,⟨-241465972793,-239956723135⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150470315836,-148126769935⟩,⟨-822765154410,-811996132857⟩,⟨-370544659648,-367209016655⟩,⟨990468447586,1025380221298⟩,⟨1370912981417,1387728682603⟩,⟨203569145620,206987854381⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148126769935,150470315836⟩,⟨811996132857,822765154410⟩,⟨367209016655,370544659648⟩,⟨-1025380221298,-990468447586⟩,⟨-1387728682603,-1370912981417⟩,⟨-206987854381,-203569145620⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨455275489289,463514287533⟩,⟨1678595811835,1737070277180⟩,⟨760220127253,781250291456⟩,⟨-7116412541743,-6577396502132⟩,⟨-5152442336356,-4890622026301⟩,⟨-1436838617639,-1352142290299⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨814117388498,824245684560⟩,⟨4075487895914,4148155957030⟩,⟨760220127253,781250291456⟩,⟨-19334713871388,-18582424724783⟩,⟨-5152442336356,-4890622026301⟩,⟨-1436838617639,-1352142290299⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨99177505746,104079808270⟩,⟨-258557031220,-250826090086⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11615373238183,12189516267034⟩,⟨27992352240550,31778225458545⟩,⟨-107898160859107,-97877368621948⟩,⟨134919777073243,165692483798588⟩,⟨-317171378993918,-201483886078802⟩,⟨1649534473307292,1910168190720231⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8600434127492,9137835313574⟩,⟨63780474868263,69810157323075⟩,⟨-72854484586840,-63810698156182⟩,⟨93063784136495,167684980957013⟩,⟨-682603940016192,-541066782318452⟩,⟨1052112011808326,1282319826126740⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨91246464512,96886333696⟩,⟨-778142094788,-630172656555⟩,⟨630471272858,812075827142⟩,⟨6776572944720,11527914316711⟩,⟨-7644308323992,-1041102219443⟩,⟨-5639559369899,3161495208793⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1190758092288,1196397961472⟩,⟨-778142094788,-630172656555⟩,⟨630471272858,812075827142⟩,⟨6776572944720,11527914316711⟩,⟨-7644308323992,-1041102219443⟩,⟨-5639559369899,3161495208793⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨87657520128,92852918528⟩,⟨-718513933958,-579140207273⟩,⟨579414641122,749847362249⟩,⟨5758256785414,10339495503393⟩,⟨-6753341355198,-466778282375⟩,⟨-5718788781510,2613896589502⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨94932057838,101034895528⟩,⟨-847541169067,-677441913198⟩,⟨677762928713,884501301904⟩,⟨7440235176430,13241118456031⟩,⟨-9055343764849,-1252686145637⟩,⟨-6034486627318,4218855285295⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-96886333696,-91246464512⟩,⟨630172656555,778142094788⟩,⟨-812075827142,-630471272858⟩,⟨-11527914316711,-6776572944720⟩,⟨1041102219443,7644308323992⟩,⟨-3161495208793,5639559369899⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1002625294080,1008265163264⟩,⟨630172656555,778142094788⟩,⟨-812075827142,-630471272858⟩,⟨-11527914316711,-6776572944720⟩,⟨1041102219443,7644308323992⟩,⟨-3161495208793,5639559369899⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-101423628224,-95256093760⟩,⟨687202323985,853336023272⟩,⟨-890548861924,-687527964609⟩,⟨-13304165169886,-7819348669909⟩,⟨1565030090680,9074157114516⟩,⟨-4188298431809,5754611578983⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-93006666312,-86862354709⟩,⟨554868563677,727924270147⟩,⟨-762023012597,-552035317852⟩,⟨-10825264481465,-4859103230420⟩,⟨-538531680313,7442815809643⟩,⟨-3572464914290,6884157396789⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1925391526,14172540819⟩,⟨-292672605390,50482356949⟩,⟨-84260083884,332465984052⟩,⟨-3385029305035,8382015225611⟩,⟨-9593875445162,6190129664006⟩,⟨-9606951541608,11103012682084⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨962695763,7086270410⟩,⟨-146336302695,25241178475⟩,⟨-42130041942,166232992026⟩,⟨-1692514652518,4191007612806⟩,⟨-4796937722581,3095064832003⟩,⟨-4803475770804,5551506341042⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7086270410,-962695763⟩,⟨-25241178475,146336302695⟩,⟨-166232992026,42130041942⟩,⟨-4191007612806,1692514652518⟩,⟨-3095064832003,4796937722581⟩,⟨-5551506341042,4803475770804⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755037113206,761160707117⟩,⟨-25241178475,146336302695⟩,⟨-166232992026,42130041942⟩,⟨-4191007612806,1692514652518⟩,⟨-3095064832003,4796937722581⟩,⟨-5551506341042,4803475770804⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7572377658,8537391893⟩,⟨-137136038864,-104593758700⟩,⟨104643321946,143116357458⟩,⟨1847103521471,3133031847009⟩,⟨-2496634610750,-895493310268⟩,⟨-270851533263,1756730541832⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8537391893,-7572377658⟩,⟨104593758700,137136038864⟩,⟨-143116357458,-104643321946⟩,⟨-3133031847009,-1847103521471⟩,⟨895493310268,2496634610750⟩,⟨-1756730541832,270851533263⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090974235883,1091939250118⟩,⟨104593758700,137136038864⟩,⟨-143116357458,-104643321946⟩,⟨-3133031847009,-1847103521471⟩,⟨895493310268,2496634610750⟩,⟨-1756730541832,270851533263⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8570709696,-7598573568⟩,⟨105319095243,138209193544⟩,⟨-144236310973,-105369002200⟩,⟨-3174922279000,-1870001027416⟩,⟨911796372479,2534302543763⟩,⟨-1789399024145,262873295147⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4285354848,-3799286784⟩,⟨52659547621,69104596772⟩,⟨-72118155487,-52684501100⟩,⟨-1587461139500,-935000513708⟩,⟨455898186239,1267151271882⟩,⟨-894699512073,131436647574⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3799286784,4285354848⟩,⟨-69104596772,-52659547621⟩,⟨52684501100,72118155487⟩,⟨935000513708,1587461139500⟩,⟨-1267151271882,-455898186239⟩,⟨-131436647574,894699512073⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765922670400,766408757728⟩,⟨-69104596772,-52659547621⟩,⟨52684501100,72118155487⟩,⟨935000513708,1587461139500⟩,⟨-1267151271882,-455898186239⟩,⟨-131436647574,894699512073⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272743558970,272984812530⟩,⟨26148439675,34284009716⟩,⟨-35779089365,-26160830486⟩,⟨-783257961753,-461775880367⟩,⟨223873327567,624158652688⟩,⟨-439182635458,67712883316⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531845340800,1532817515456⟩,⟨-138209193544,-105319095242⟩,⟨105369002200,144236310974⟩,⟨1870001027416,3174922279000⟩,⟨-2534302543764,-911796372478⟩,⟨-262873295148,1789399024146⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1199015758613,1205760344122⟩,⟨-935796139923,-749393089621⟩,⟨749748200227,976604953586⟩,⟨8995363668937,15316057515645⟩,⟨-10708964502937,-2175260712672⟩,⟨-5844512243941,5384025451705⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1298519889450,1312009060468⟩,⟨-1871592279845,-1498786179242⟩,⟨1499496400453,1953209907172⟩,⟨17990727337883,30632115031278⟩,⟨-21417929005866,-4350521425345⟩,⟨-11684214929807,10768050903405⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨182913613952,194276546688⟩,⟨-1584756221962,-1256037691566⟩,⟨1256632882944,1653865313788⟩,⟨12792735638093,24502658664859⟩,⟨-16699938313191,-1262134863194⟩,⟨-12381232219401,7681556527440⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62659152859,67071660184⟩,⟨-540909888831,-419846178894⟩,⟨418297990727,565889455286⟩,⟨4077057235252,8165315556917⟩,⟨-5613126198491,-66505929425⟩,⟨-4638844695993,2674116933503⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379987750458,380565235992⟩,⟨2115807269,21669644166⟩,⟨-23741539009,-636668101⟩,⟨-636680413727,139906180521⟩,⟨-312298944707,652948734344⟩,⟨-686912736483,533652536895⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176658573301,3181486293065⟩,⟨-181431311422,-17661091095⟩,⟨5314403392,198778462839⟩,⟨-1171182422546,5351364907957⟩,⟨-5489551605259,2614695753601⟩,⟨-4468042647669,5776086377171⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨181031951001,194074862092⟩,⟨-1576214614367,-1214006799871⟩,⟨1208830230508,1649552311296⟩,⟨11721290824393,24131659695280⟩,⟨-16767870605511,-41394265906⟩,⟨-13691218414889,8294638377989⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨363945564953,388351408780⟩,⟨-3160970836329,-2470044491437⟩,⟨2465463113452,3303417625084⟩,⟨24514026462486,48634318360139⟩,⟨-33467808918702,-1303529129100⟩,⟨-26072450634290,15976194905429⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518485687569,526929963652⟩,⟨-34947503550,202608941684⟩,⟨-230156768806,58330865642⟩,⟨-5809350148103,2382312164999⟩,⟨-4329499747728,6652782146352⟩,⟨-7699039806610,6700884881800⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356045290373,364778665003⟩,⟨-36289747888,210390633567⟩,⟨-238996502357,60571205185⟩,⟨-6039449301732,2514259161449⟩,⟨-4541732842016,6919943579340⟩,⟨-8007968650844,7010444173722⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712090580746,729557330006⟩,⟨-72579495776,420781267134⟩,⟨-477993004714,121142410370⟩,⟨-12078898603464,5028518322898⟩,⟨-9083465684032,13839887158680⟩,⟨-16015937301688,14020888347444⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523307948907,1525245137798⟩,⟨-33615434844,31816943622⟩,⟨-37747355258,39592989028⟩,⟨-1263030819593,1327818757529⟩,⟨-1638809233496,1584838238272⟩,⟨-2019603836980,2060250557409⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨986559136428,1012043658499⟩,⟨-122987248623,604820221462⟩,⟨-688119476817,194320116644⟩,⟨-17619662910771,7880970749749⟩,⟨-13716279512814,20280075551323⟩,⟨-23591835654986,20849664559933⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67656445898,67776188982⟩,⟨12972702276,17023947232⟩,⟨-17766338720,-12978849576⟩,⟨-387688100009,-226957133663⟩,⟨108836243218,308685717566⟩,⟨-216834087690,35951838061⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50095231062,50808222372⟩,⟨260383175224,268462933592⟩,⟨33460277235,38547896360⟩,⟨-1386291189595,-1183029404053⟩,⟨-295079063862,-105541780205⟩,⟨-276366264496,-74197996298⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134174927169,2136884664368⟩,⟨-385351945918,-293462226806⟩,⟨293601288076,402156627072⟩,⟨5230766824680,8886996985246⟩,⟨-7102349832652,-2560824928724⟩,⟨-712742193217,5027006918235⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2973343651898,2979008279047⟩,⟨-805822599867,-613279660001⟩,⟨613570271332,840963441896⟩,⟨10973462347572,18656560978979⟩,⟨-14927792973356,-5393816842606⟩,⟨-1448243602957,10591279319095⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135469542573,137659403745⟩,⟨666901766877,699429543161⟩,⟨118439718264,143302131583⟩,⟨-3649549214382,-2627549911244⟩,⟨-1372242868206,-344488833441⟩,⟨-778363401194,347738638789⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8782006798852,8923967680508⟩,⟨-46074464557950,-42545119995787⟩,⟨-9439934368314,-7555883454029⟩,⟨579851360732975,716176793611000⟩,⟨95186866807130,187872406503205⟩,⟨-9905158628970,71245647446628⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7879833941460,8214051285639⟩,⟨-43407366234931,-33265569739728⟩,⟨-14273956990603,-5202509250696⟩,⟨326587559928878,733475511747630⟩,⟨-39252718556854,367417255245677⟩,⟨-203932331879472,246615894660603⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15759667882920,16428102571278⟩,⟨-86814732469862,-66531139479456⟩,⟨-28547913981206,-10405018501392⟩,⟨653175119857756,1466951023495260⟩,⟨-78505437113708,734834510491354⟩,⟨-407864663758944,493231789321206⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10867759718499,10909882818322⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108414,2148278590204846⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9768248090723,9810371190546⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108424,2148278590204831⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2401631390336,2406362620352⟩,⟨-12184942684160,-12039116462039⟩,⟨0,0⟩,⟨102958094106835,109987257462969⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7423551559394,7516867516659⟩,⟨-45527840410572,-44228264431626⟩,⟨-20515631789982,-19989844172044⟩,⟨527009035764984,551502137787228⟩,⟨288313670854602,299905844916445⟩,⟨107655713528912,111985783122910⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6324039931618,6417355888883⟩,⟨-45527840410572,-44228264431625⟩,⟨-20515631789982,-19989844172043⟩,⟨527009035764987,551502137787222⟩,⟨288313670854603,299905844916442⟩,⟨107655713528912,111985783122909⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1923586934144,1939692557376⟩,⟨-7915571448074,-7577808035071⟩,⟨-3566893306854,-3424941126073⟩,⟨33309050014318,43659313453105⟩,⟨23719278945735,28537683339092⟩,⟨6873836711226,8801522464515⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99599284960,100028781692⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137007906866,139029561398⟩,⟨682255681189,689696163501⟩,⟨308554179148,310597050961⟩,⟨-1725980926281,-1712309844048⟩,⟨-1555611653250,-1547724012908⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4325218324480,4346055177728⟩,⟨-20100514132234,-19616924497110⟩,⟨-3566893306854,-3424941126073⟩,⟨136267144121153,153646570916074⟩,⟨23719278945735,28537683339092⟩,⟨6873836711226,8801522464515⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨727891129906,776702817560⟩,⟨-6321941672658,-4940088982874⟩,⟨4930926226904,6606835250168⟩,⟨49028052924972,97268636720278⟩,⟨-66935617837404,-2607058258200⟩,⟨-52144901268580,31952389810858⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5053109454386,5122757995288⟩,⟨-26422455804892,-24557013479984⟩,⟨1364032920050,3181894124095⟩,⟨185295197046125,250915207636352⟩,⟨-43216338891669,25930625080892⟩,⟨-45271064557354,40753912275373⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457736030949,466046222911⟩,⟨1626844326735,1865704481233⟩,⟨123560952032,289474876542⟩,⟨-35653905608455,-26455156125753⟩,⟨-2843605006622,4899598982878⟩,⟨-4118564387293,3707613535961⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨221620312472,222479305934⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-222479305934,-221620312472⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨877032321842,877891315304⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1915676288695,1921330154691⟩,⟨-14541640415106,-14406339271082⟩,⟨0,0⟩,⟨130281633100448,136557721617390⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨816164660919,821818526915⟩,⟨-14541640415106,-14406339271082⟩,⟨0,0⟩,⟨130281633100448,136557721617390⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36809604056,38896684926⟩,⟨-784883970873,-742829882528⟩,⟨325509421405,328085365043⟩,⟨9162240039155,9882836927011⟩,⟨-6627114036394,-6561817940510⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨494545635005,504942907837⟩,⟨841960355862,1122874598705⟩,⟨449070373437,617560241585⟩,⟨-26491665569300,-16572319198742⟩,⟨-9470719043016,-1662218957632⟩,⟨-4118564387293,3707613535961⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502387216868,503376923070⟩,⟨2513460839922,2553938535635⟩,⟨0,0⟩,⟨2096765778922,4420352332343⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225967055652,231172277630⟩,⟨1515228365891,1686951064686⟩,⟨205188566805,282730592717⟩,⟨-7335873279980,-325772218556⟩,⟨-3309306169405,674966343569⟩,⟨-1885555565188,1697414603464⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-776702817560,-727891129906⟩,⟨4940088982874,6321941672658⟩,⟨-6606835250168,-4930926226904⟩,⟨-97268636720278,-49028052924972⟩,⟨2607058258200,66935617837404⟩,⟨-31952389810858,52144901268580⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3548515506920,3618164047822⟩,⟨-15160425149360,-13294982824452⟩,⟨-10173728557022,-8355867352977⟩,⟨38998507400875,104618517991102⟩,⟨26326337203935,95473301176496⟩,⟨-25078553099632,60946423733095⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442173297492,457504721121⟩,⟨284897037327,612923117027⟩,⟨-290619691108,-19125593948⟩,⟨-19839674123360,-8796856937285⟩,⟨-12502920705983,-1838608984566⟩,⟨-10072272564604,1887802613221⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨321656811680,325700120742⟩,⟨1940466224332,1948197165466⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-325700120742,-321656811680⟩,⟨-1948197165466,-1940466224332⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨773811507034,777854816096⟩,⟨-1948197165466,-1940466224332⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1353777137793,1372244876166⟩,⟨-9036802034819,-8727920913684⟩,⟨-4072139188536,-3944757526720⟩,⟨50189453106671,58937798670109⟩,⟨32629239776686,36708685299976⟩,⟨10301502771255,11922562363367⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1372244876166,-1353777137793⟩,⟨8727920913684,9036802034819⟩,⟨3944757526720,4072139188536⟩,⟨-58937798670109,-50189453106671⟩,⟨-36708685299976,-32629239776686⟩,⟨-11922562363367,-10301502771255⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-272733248390,-254265510017⟩,⟨8727920913684,9036802034819⟩,⟨3944757526720,4072139188536⟩,⟨-58937798670109,-50189453106671⟩,⟨-36708685299976,-32629239776686⟩,⟨-11922562363367,-10301502771255⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12908469308,-11467554523⟩,⟨422637572359,459779458732⟩,⟨69031130859,91326180781⟩,⟨-4914587496902,-4254636827950⟩,⟨1518988649979,1958843339735⟩,⟨2582265415484,2786743564849⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429264828184,446037166598⟩,⟨707534609686,1072702575759⟩,⟨-221588560249,72200586833⟩,⟨-24754261620262,-13051493765235⟩,⟨-10983932056004,120234355169⟩,⟨-7490007149120,4674546178070⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100028781692,-99599284960⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4491998268,4734363948⟩,⟨27793582060,30190067518⟩,⟨39722996071,39933365192⟩,⟨-310521437886,-299250504165⟩,⟨249756374792,250871388573⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9811741661,10361506098⟩,⟨8241828047,16888006654⟩,⟨86765789348,87397126939⟩,⟨-928110316835,-788704747299⟩,⟨102988436616,114103164432⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1466705670724,1484952706692⟩,⟨-7566249662768,-7252135279410⟩,⟨-1425003017124,-1352775261704⟩,⟨104782989391348,112370899099985⟩,⟨22080238708176,23919649644036⟩,⟨4901461789461,5355745376348⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13088481076,13993800645⟩,⟨-60308053514,-41907866634⟩,⟨102313331635,105962971077⟩,⟨-550839153239,-101870385169⟩,⟨-288887004576,-202912983289⟩,⟨-182799760582,-163032053394⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13993800645,-13088481076⟩,⟨41907866634,60308053514⟩,⟨-105962971077,-102313331635⟩,⟨101870385169,550839153239⟩,⟨202912983289,288887004576⟩,⟨163032053394,182799760582⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114022582337,-112687766036⟩,⟨-835983448670,-816724268328⟩,⟨-105962971077,-102313331635⟩,⟨2300893640721,2749862408791⟩,⟨202912983289,288887004576⟩,⟨163032053394,182799760582⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86755132640,91805681893⟩,⟨-602709545901,-561173642186⟩,⟨598359449040,619894368479⟩,⟨3230949196634,3927792150283⟩,⟨-3639323475393,-3175752237087⟩,⟨-2537926472307,-2315349486412⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨115727966665,123988771354⟩,⟨-1445750859784,-1320801421882⟩,⟨679205025654,730463964897⟩,⟨19980441710076,22982362132582⟩,⟨-6748253275191,-5404631172067⟩,⟨-4647678458720,-4113771943268⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-123988771354,-115727966665⟩,⟨1320801421882,1445750859784⟩,⟨-730463964897,-679205025654⟩,⟨-22982362132582,-19980441710076⟩,⟨5404631172067,6748253275191⟩,⟨4113771943268,4647678458720⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨975522856422,983783661111⟩,⟨1320801421882,1445750859784⟩,⟨-730463964897,-679205025654⟩,⟨-22982362132582,-19980441710076⟩,⟨5404631172067,6748253275191⟩,⟨4113771943268,4647678458720⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121557918335,124396147762⟩,⟨769902043540,799913254660⟩,⟨181394688793,193271121159⟩,⟨-2811221760791,-2195173005345⟩,⟨-805964663282,-532944787611⟩,⟨-213665721922,-103865946292⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11549248132,11824476390⟩,⟨167410386466,173387873672⟩,⟨20971966982,21977342102⟩,⟨642998416066,799601843377⟩,⟨92081133796,119539398304⟩,⟨-18872529695,-12994072038⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165539236020,176672720943⟩,⟨1465917499864,1891793667662⟩,⟨-6414575516,219075345564⟩,⟨-11303309941811,7463187373314⟩,⟨-5761591436284,6835436386217⟩,⟨-5809525177274,4721185158765⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176672720943,-165539236020⟩,⟨-1891793667662,-1465917499864⟩,⟨-219075345564,6414575516⟩,⟨-7463187373314,11303309941811⟩,⟨-6835436386217,5761591436284⟩,⟨-4721185158765,5809525177274⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49294334709,65633041610⟩,⟨-376565301771,221033564822⟩,⟨-13886778759,289145168233⟩,⟨-14799060653294,10977537723255⟩,⟨-10144742555622,6436557779853⟩,⟨-6606740723953,7506939780738⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27571414853840,28981474578648⟩,⟨-271422059178458,-225010961484835⟩,⟨-103656443919825,-67294324530183⟩,⟨2537216549760382,4490220905726614⟩,⟨480435132973715,2209894738315735⟩,⟨-556182856138193,1186858818297393⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13438991581,14073886249⟩,⟨170235015928,181000591372⟩,⟨40108644982,43732476018⟩,⟨442094458957,678520435152⟩,⟨71663166170,163375211904⟩,⟨11504817677,44979966438⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336996901839,370966496620⟩,⟨794586467648,2020664051580⟩,⟨-321048820006,330204585378⟩,⟨-47264897931676,5684243458600⟩,⟨-20190252827273,13966133829295⟩,⟨-15076471796068,11467940032565⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370966496620,-336996901839⟩,⟨-2020664051580,-794586467648⟩,⟨-330204585378,321048820006⟩,⟨-5684243458600,47264897931676⟩,⟨-13966133829295,20190252827273⟩,⟨-11467940032565,15076471796068⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58298331564,109040264759⟩,⟨-1313129441894,278116108111⟩,⟨-551793145627,393249406839⟩,⟨-30438505078862,34213404166441⟩,⟨-24950065885299,20310487182442⟩,⟨-18957947181685,19751017974138⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236607191826,239058343090⟩,⟨1559288003031,1567587478805⟩,⟨308554179148,310597050961⟩,⟨-3925004181833,-3911333099600⟩,⟨-1555611653250,-1547724012908⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1703642445204,-1615191438027⟩,⟨-5671951260295,-2703439567685⟩,⟨-516822426221,1494011254099⟩,⟨-20308136139990,106157618131413⟩,⟨-59376210256869,42529780856049⟩,⟨-46876345619368,50530506077533⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192746081073,-178569561211⟩,⟨-1881139778740,-1429874532765⟩,⟨-357936736999,-97441355608⟩,⟨-7325768134808,12580265474943⟩,⟨-7307791252105,6701435576426⟩,⟨-5332592198619,6573199019540⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43861110753,60488781879⟩,⟨-321851775709,137712946040⟩,⟨-49382557851,213155695353⟩,⟨-11250772316641,8668932375343⟩,⟨-8863402905355,5153711563518⟩,⟨-5683062872152,6223413863056⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2613685382,6508930014⟩,⟨-115729071244,38521797729⟩,⟨-34315308331,52149171444⟩,⟨-3812562249948,4030408825315⟩,⟨-2975414865019,2112833586657⟩,⟨-2077072292919,2130300724781⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1749683211,3327743556⟩,⟨-35412853064,15152342450⟩,⟨-5433486460,23453191466⟩,⟨-1318528427606,1142255723797⟩,⟨-1100017441970,620450070358⟩,⟨-644445615647,767399022456⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3061056998,5870605863⟩,⟨-86430226841,14672079836⟩,⟨-20380866285,35924512256⟩,⟨-2491231853738,2657123206781⟩,⟨-2120838528416,1334930397562⟩,⟨-1278121445417,1415690999270⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5870605863,-3061056998⟩,⟨-14672079836,86430226841⟩,⟨-35924512256,20380866285⟩,⟨-2657123206781,2491231853738⟩,⟨-1334930397562,2120838528416⟩,⟨-1415690999270,1278121445417⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3256920481,3447873016⟩,⟨-130401151080,124952024570⟩,⟨-70239820587,72530037729⟩,⟨-6469685456729,6521640679053⟩,⟨-4310345262581,4233672115073⟩,⟨-3492763292189,3408422170198⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49294334709,65633041610⟩,⟨-376565301771,221033564822⟩,⟨-13886778759,289145168233⟩,⟨-14799060653294,10977537723255⟩,⟨-10144742555622,6436557779853⟩,⟨-6606740723953,7506939780738⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3256920481,3447873016⟩,⟨-130401151080,124952024570⟩,⟨-70239820587,72530037729⟩,⟨-6469685456729,6521640679053⟩,⟨-4310345262581,4233672115073⟩,⟨-3492763292189,3408422170198⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (517/5120) u, BivariateJet2.affineZ (593/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000024

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000025Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2521033809728,-2521033751872⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2521033809728,-2521033751872⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-117038806336,-117038806272⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-117038806336,-117038806272⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2096257264576,-2096257225792⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2096257264576,-2096257225792⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-176874748352,-176874748288⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-176874748288,-176874748224⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨92552556288,92552556352⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-101065323776,-101065323712⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨92552682176,92552682240⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-101065473920,-101065473856⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8512791680,-8512791616⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8512767424,-8512767360⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨193617880000,193617880064⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨193618156032,193618156096⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1919382477504,1919382516096⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1919382477504,1919382516096⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2518909148864,-2518909091008⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2103083544896,-2103083506112⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2089468054080,-2089468015360⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-178063966592,-178063966528⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-175687700672,-175687700608⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨89967104320,89967104384⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-97989968512,-97989968448⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨95160026368,95160026432⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-104182969856,-104182969792⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9022943424,-9022943360⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8022864128,-8022864064⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨187957072768,187957072832⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨199342996224,199342996288⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1911404048832,1911404087424⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1927395805440,1927395844032⟩



end LaneCBRB2Cell000025Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000025
open Set LaneCBRB2Cell000025Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111024904601,111024904602⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨131211250892,131211250893⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111024904602,-111024904601⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438730909286,438730909287⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨52356364369,52356364371⟩,⟨-131211250893,-131211250892⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163381268970,163381268973⟩,⟨968300376883,968300376884⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52356364368,52356364372⟩,⟨-131211250893,-131211250892⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2521033809728,-2521033751872⟩,⟨10888780530353,10888780530452⟩,⟨0,0⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-254565328054,-254565322209⟩,⟨-1421522181962,-1421522124086⟩,⟨0,0⟩,⟨10888780530155,10888780530650⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨254565322209,254565328054⟩,⟨1421522124086,1421522181962⟩,⟨0,0⟩,⟨-10888780530650,-10888780530155⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988486723174,988486723175⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117038806336,-117038806272⟩,⟨-1223006633547,-1223006633545⟩,⟨0,0⟩,⟨-1360372357977,-1360372357971⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105220629994,-105220629935⟩,⟨-982472821506,-982472821438⟩,⟨0,0⟩,⟨1223006633540,1223006633552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105220629935,105220629994⟩,⟨982472821438,982472821506⟩,⟨0,0⟩,⟨-1223006633552,-1223006633540⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨359785952144,359785958048⟩,⟨2403994945524,2403995003468⟩,⟨0,0⟩,⟨-12111787164202,-12111787163695⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2096257264576,-2096257225792⟩,⟨6516398913137,6516398913266⟩,⟨2952540026509,2952540026571⟩,⟨-38620287156667,-38620287155154⟩,⟨-24898028187404,-24898028186559⟩,⟨-7928513340179,-7928513339847⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311492087331,-311492081561⟩,⟨-877798061804,-877798027607⟩,⟨-397724870320,-397724854822⟩,⟨5738758339487,5738758340058⟩,⟨3596941492327,3596941531424⟩,⟨1178132670682,1178132670810⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨311492081561,311492087331⟩,⟨877798027607,877798061804⟩,⟨397724854822,397724870320⟩,⟨-5738758340058,-5738758339487⟩,⟨-3596941531424,-3596941492327⟩,⟨-1178132670810,-1178132670682⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-163381268973,-163381268970⟩,⟨-968300376884,-968300376883⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨936130358803,936130358806⟩,⟨-968300376884,-968300376883⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-176874748352,-176874748224⟩,⟨-1137296225417,-1137296225410⟩,⟨-515301882575,-515301882570⟩,⟨-1176379286650,-1176379286636⟩,⟨758397381121,758397381133⟩,⟨-241503612583,-241503612579⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150592151512,-150592151401⟩,⟨-812533142565,-812533142441⟩,⟨-368153739247,-368153739188⟩,⟨1001575914124,1001575914155⟩,⟨1376444728732,1376444728884⟩,⟨205617528529,205617528540⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150592151401,150592151512⟩,⟨812533142441,812533142565⟩,⟨368153739188,368153739247⟩,⟨-1001575914155,-1001575914124⟩,⟨-1376444728884,-1376444728732⟩,⟨-205617528540,-205617528529⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨462084232962,462084238843⟩,⟨1690331170048,1690331204369⟩,⟨765878594010,765878609567⟩,⟨-6740334254213,-6740334253611⟩,⟨-4973386260308,-4973386221059⟩,⟨-1383750199350,-1383750199211⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨821870185106,821870196891⟩,⟨4094326115572,4094326207837⟩,⟨765878594010,765878609567⟩,⟨-18852121418415,-18852121417306⟩,⟨-4973386260308,-4973386221059⟩,⟨-1383750199350,-1383750199211⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨104712728736,104712728744⟩,⟨-262422501786,-262422501784⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11545165846744,11545165847627⟩,⟨28933553173088,28933553177735⟩,⟨-96745088612279,-96745088597259⟩,⟨145021823043972,145021823079460⟩,⟨-242454651888994,-242454651735839⟩,⟨1621390682807934,1621390683187358⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8629856521604,8629856646011⟩,⟨64618960766050,64618962051741⟩,⟨-64273726493135,-64273725280985⟩,⟨125933228391737,125933234889952⟩,⟨-573555721026025,-573555709309828⟩,⟨1062660018913175,1062660039336687⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨96559548928,96559685888⟩,⟨-715002909871,-715000837851⟩,⟨711180849752,711182909965⟩,⟨9136349844339,9136400749945⟩,⟨-4127256081869,-4127191124993⟩,⟨-1340659716907,-1340579347686⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1196071176704,1196071313664⟩,⟨-715002909871,-715000837851⟩,⟨711180849752,711182909965⟩,⟨9136349844339,9136400749945⟩,⟨-4127256081869,-4127191124993⟩,⟨-1340659716907,-1340579347686⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨92552556288,92552682240⟩,⟨-657280292854,-657278312843⟩,⟨653766715094,653768683849⟩,⟨8005848316963,8005898441937⟩,⟨-3403244252168,-3403181750633⟩,⟨-1621157754172,-1621081390854⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨100680558631,100680707174⟩,⟨-775189201193,-775186709101⟩,⟨771045169894,771047647873⟩,⟨10332829368950,10332895277243⟩,⟨-4899815818818,-4899736439279⟩,⟨-1030647764766,-1030552577665⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-96559685888,-96559548928⟩,⟨715000837851,715002909871⟩,⟨-711182909965,-711180849752⟩,⟨-9136400749945,-9136349844339⟩,⟨4127191124993,4127256081869⟩,⟨1340579347686,1340659716907⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1002951941888,1002952078848⟩,⟨715000837851,715002909871⟩,⟨-711182909965,-711180849752⟩,⟨-9136400749945,-9136349844339⟩,⟨4127191124993,4127256081869⟩,⟨1340579347686,1340659716907⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-101065473920,-101065323712⟩,⟨783837784143,783840162688⟩,⟨-779652390433,-779650025404⟩,⟨-10574810631324,-10574750065684⟩,⟨5080347467077,5080422668191⟩,⟨916800581623,916892243153⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-92189863761,-92189714154⟩,⟨649278735900,649281291337⟩,⟨-645812418013,-645809877034⟩,⟨-7786885186529,-7786816647466⟩,⟨3240815030922,3240896809650⟩,⟨1721634224994,1721731502762⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8490694870,8490993020⟩,⟨-125910465293,-125905417764⟩,⟨125232751881,125237770839⟩,⟨2545944182421,2546078629777⟩,⟨-1659000787896,-1658839629629⟩,⟨690986460228,691178925097⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4245347435,4245496510⟩,⟨-62955232647,-62952708882⟩,⟨62616375940,62618885420⟩,⟨1272972091210,1273039314889⟩,⟨-829500393948,-829419814814⟩,⟨345493230114,345589462549⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4245496510,-4245347435⟩,⟨62952708882,62955232647⟩,⟨-62618885420,-62616375940⟩,⟨-1273039314889,-1272972091210⟩,⟨829419814814,829500393948⟩,⟨-345589462549,-345493230114⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757877887106,757878055445⟩,⟨62952708882,62955232647⟩,⟨-62618885420,-62616375940⟩,⟨-1273039314889,-1272972091210⟩,⟨829419814814,829500393948⟩,⟨-345589462549,-345493230114⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8479898032,8479922089⟩,⟨-125583858584,-125583316522⟩,⟨124912370770,124912909806⟩,⟨2534630799245,2534647406149⟩,⟨-1649867774034,-1649849976828⟩,⟨684530314003,684550094434⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8479922089,-8479898032⟩,⟨125583316522,125583858584⟩,⟨-124912909806,-124912370770⟩,⟨-2534647406149,-2534630799245⟩,⟨1649849976828,1649867774034⟩,⟨-684550094434,-684530314003⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091031705687,1091031729744⟩,⟨125583316522,125583858584⟩,⟨-124912909806,-124912370770⟩,⟨-2534647406149,-2534630799245⟩,⟨1649849976828,1649867774034⟩,⟨-684550094434,-684530314003⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8512791680,-8512767360⟩,⟨126559396034,126559945101⟩,⟨-125883781448,-125883235446⟩,⟨-2568915428410,-2568898509704⟩,⟨1677163017283,1677181115191⟩,⟨-704283197325,-704263122917⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4256395840,-4256383680⟩,⟨63279698017,63279972551⟩,⟨-62941890724,-62941617723⟩,⟨-1284457714205,-1284449254852⟩,⟨838581508641,838590557596⟩,⟨-352141598663,-352131561458⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4256383680,4256395840⟩,⟨-63279972551,-63279698017⟩,⟨62941617723,62941890724⟩,⟨1284449254852,1284457714205⟩,⟨-838590557596,-838581508641⟩,⟨352131561458,352141598663⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766379767296,766379798720⟩,⟨-63279972551,-63279698017⟩,⟨62941617723,62941890724⟩,⟨1284449254852,1284457714205⟩,⟨-838590557596,-838581508641⟩,⟨352131561458,352141598663⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272757926421,272757932436⟩,⟨31395829130,31395964646⟩,⟨-31228227452,-31228092692⟩,⟨-633661851538,-633657699811⟩,⟨412462494207,412466943509⟩,⟨-171137523609,-171132578500⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532759534592,1532759597440⟩,⟨-126559945102,-126559396034⟩,⟨125883235446,125883781448⟩,⟨2568898509704,2568915428410⟩,⟨-1677181115192,-1677163017282⟩,⟨704263122916,704283197326⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1205367479773,1205367644375⟩,⟨-859304755491,-859302030607⟩,⟨854711093986,854713803427⟩,⟨12205430935395,12205502716588⟩,⟨-6178866997942,-6178780015721⟩,⟨-399101562048,-398997013280⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1311223331770,1311223660974⟩,⟨-1718609510982,-1718604061213⟩,⟨1709422187971,1709427606853⟩,⟨24410861870795,24411005433169⟩,⟨-12357733995882,-12357560031443⟩,⟨-798202973106,-797994177549⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨193617880000,193618156096⟩,⟨-1441120742096,-1441115810435⟩,⟨1433416455477,1433421359305⟩,⟨18580584503182,18580722952772⟩,⟨-8483678736206,-8483517401900⟩,⟨-2538060003569,-2537871966277⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨66557137798,66557246988⟩,⟨-487313018128,-487311250962⟩,⟨484707725129,484709482275⟩,⟨6103879868943,6103925938096⟩,⟨-2690582630934,-2690526545091⟩,⟨-1035453853109,-1035386275249⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380234553046,380234577023⟩,⟨12370971935,12371299546⟩,⟨-12305204171,-12304878387⟩,⟨-253304094175,-253293996630⟩,⟨166115373262,166126160304⟩,⟨-71014790095,-71002841024⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179421053918,3179421254408⟩,⟨-103445550664,-103442798220⟩,⟨102890141438,102892878535⟩,⟨2124708510069,2124793567983⟩,⟨-1395798666837,-1395707937420⟩,⟨600366307509,600466651263⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨192461052577,192461380456⟩,⟨-1415408786172,-1415403410368⟩,⟨1407841427492,1407846772863⟩,⟨17870694465996,17870836927824⟩,⟨-7955966974476,-7955795914354⟩,⟨-2867129326375,-2866924849038⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨386078932577,386079536552⟩,⟨-2856529528268,-2856519220803⟩,⟨2841257882969,2841268132168⟩,⟨36451278969178,36451559880596⟩,⟨-16439645710682,-16439313316254⟩,⟨-5405189329944,-5404796815315⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522394558869,522394790938⟩,⟨86784832082,86788330554⟩,⟨-86324651632,-86321172958⟩,⟨-1747767813719,-1747674173226⟩,⟨1136244009604,1136355922558⟩,⟨-469288096290,-469154755476⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360079215635,360079455578⟩,⟨89729344614,89732981718⟩,⟨-89253570581,-89249954053⟩,⟨-1799614709171,-1799516889796⟩,⟨1167381406464,1167497974548⟩,⟨-477836735504,-477698169018⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720158431270,720158911156⟩,⟨179458689228,179465963436⟩,⟨-178507141162,-178499908106⟩,⟨-3599229418342,-3599033779592⟩,⟨2334762812928,2334995949096⟩,⟨-955673471008,-955396338036⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524279612503,1524279699408⟩,⟨-976628580,-975537450⟩,⟨970325640,971410678⟩,⟨34251103555,34284629165⟩,⟨-27331138364,-27295243248⟩,⟨19713028482,19752883323⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨998373083854,998373806054⟩,⟨248148256561,248159070254⟩,⟨-246833245258,-246822492684⟩,⟨-4967584262035,-4967290416130⟩,⟨3219153640786,3219500917276⟩,⟨-1312277140589,-1311866391057⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67663574032,67663577017⟩,⟨15576845274,15576912854⟩,⟨-15493691088,-15493623884⟩,⟨-312594417488,-312592335220⟩,⟨202857289550,202859516954⟩,⟨-83134952237,-83132481566⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50577613469,50577616426⟩,⟨263606928401,263606995880⟩,⟨35550583561,35550637000⟩,⟨-1277804254797,-1277802137808⟩,⟨-201272086333,-201270104436⟩,⟨-168882434924,-168880489410⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136723006408,2136723181634⟩,⟨-352858424790,-352856879476⟩,⟨350971694160,350973230846⟩,⟨7191412741797,7191460458875⟩,⟨-4705084021090,-4705033119630⟩,⟨1992362022932,1992418322425⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2978670236965,2978670603372⟩,⟨-737846408539,-737843146949⟩,⟨733901120741,733904364130⟩,⟨15098563109033,15098664035790⟩,⟨-9899188411851,-9899081042458⟩,⟨4226412792493,4226531213997⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137019043810,137019068677⟩,⟨680192533084,680192955756⟩,⟨130069049527,130069357317⟩,⟨-3120941648480,-3120929149816⟩,⟨-848531354594,-848519988809⟩,⟨-215643054180,-215631987494⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8823047998264,8823049599522⟩,⟨-43799577190183,-43799534075129⟩,⟨-8375539334352,-8375516474794⟩,⟨635826389641429,635828044620374⟩,⟨137794398289265,137795443721545⟩,⟨29786527885327,29787329455367⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8011460194228,8011467443501⟩,⟨-37779433664215,-37779278609861⟩,⟨-9585838641866,-9585725740009⟩,⟨517706381635671,517711548220932⟩,⟨158893462475163,158897819211940⟩,⟨20276559653293,20280779112276⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16022920388456,16022934887002⟩,⟨-75558867328430,-75558557219722⟩,⟨-19171677283732,-19171451480018⟩,⟨1035412763271342,1035423096441864⟩,⟨317786924950326,317795638423880⟩,⟨40553119306586,40561558224552⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10888780530353,10888780530452⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239700,2135836853297982⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9789268902577,9789268902676⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239713,2135836853297977⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2403994945600,2403995003456⟩,⟨-12111787164150,-12111787163733⟩,⟨0,0⟩,⟨106474359377039,106474359411671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7399415044416,7399415044553⟩,⟨-43853597303608,-43853597301937⟩,⟨-19869793588672,-19869793587889⟩,⟨519808115851483,519808115881443⟩,⟨285317897287601,285317897303315⟩,⟨106713488797547,106713488803965⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6299903416640,6299903416777⟩,⟨-43853597303609,-43853597301936⟩,⟨-19869793588672,-19869793587888⟩,⟨519808115851484,519808115881435⟩,⟨285317897287601,285317897303312⟩,⟨106713488797546,106713488803965⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1919382477504,1919382516096⟩,⟨-7653695138852,-7653695138359⟩,⟨-3467841909222,-3467841908994⟩,⟨37443907862004,37443907876894⟩,⟨25656425564492,25656425571871⟩,⟨7687009725902,7687009729044⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99813991382,99813991384⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139103727581,139103727585⟩,⟨680532352741,680532352750⟩,⟨308344998148,308344998153⟩,⟨-1705494687256,-1705494687251⟩,⟨-1545498179672,-1545498179662⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4323377423104,4323377519552⟩,⟨-19765482303002,-19765482302092⟩,⟨-3467841909222,-3467841908994⟩,⟨143918267239043,143918267288565⟩,⟨25656425564492,25656425571871⟩,⟨7687009725902,7687009729044⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨772157865154,772159073104⟩,⟨-5713059056536,-5713038441606⟩,⟨5682515765938,5682536264336⟩,⟨72902557938356,72903119761192⟩,⟨-32879291421364,-32878626632508⟩,⟨-10810378659888,-10809593630630⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5095535288258,5095536592656⟩,⟨-25478541359538,-25478520743698⟩,⟨2214673856716,2214694355342⟩,⟨216820825177399,216821387049757⟩,⟨-7222865856872,-7222201060637⟩,⟨-3123368933986,-3122583901586⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨462574203401,462574321825⟩,⟨1753526478654,1753529391195⟩,⟨201048748975,201050609851⟩,⟨-31174155049465,-31174068528428⟩,⟨1111719647680,1111796356963⟩,⟨-283540357365,-283469091884⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨222049809202,222049809204⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-222049809204,-222049809202⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨877461818572,877461818574⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1918500653850,1918500700027⟩,⟨-14473763903941,-14473763787873⟩,⟨0,0⟩,⟨133418678423327,133418678452828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨818989026074,818989072251⟩,⟨-14473763903941,-14473763787873⟩,⟨0,0⟩,⟨133418678423327,133418678452828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38998485126,38998487329⟩,⟨-786944144627,-786944133535⟩,⟨326795816458,326795834885⟩,⟨9807589089607,9807589119228⟩,⟨-6594360098773,-6594360006268⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨501572688527,501572809154⟩,⟨966582334027,966585257660⟩,⟨527844565433,527846444736⟩,⟨-21366565959858,-21366479409200⟩,⟨-5482640451093,-5482563649305⟩,⟨-283540357365,-283469091884⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502882001783,502882013886⟩,⟨2533615820870,2533615942923⟩,⟨0,0⟩,⟨3256741201878,3256744126778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229403556337,229403617030⟩,⟨1597863372800,1597865054259⟩,⟨241419485696,241420351042⟩,⟨-3832131089378,-3832075888553⟩,⟨-1291269590654,-1291230014491⟩,⟨-129682435663,-129649837954⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-772159073104,-772157865154⟩,⟨5713038441606,5713059056536⟩,⟨-5682536264336,-5682515765938⟩,⟨-72903119761192,-72902557938356⟩,⟨32878626632508,32879291421364⟩,⟨10809593630630,10810378659888⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3551218350000,3551219654398⟩,⟨-14052443861396,-14052423245556⟩,⟨-9150378173558,-9150357674932⟩,⟨71015147477851,71015709350209⟩,⟨58535052197000,58535716993235⟩,⟨18496603356532,18497388388932⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449279204930,449279369969⟩,⟨420160773522,420164189144⟩,⟨-161754812508,-161751853289⟩,⟨-13919270614441,-13919171985894⟩,⟨-7190545802795,-7190441393918⟩,⟨-3922997205342,-3922885974947⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨326762537940,326762537946⟩,⟨1936600753766,1936600753768⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-326762537946,-326762537940⟩,⟨-1936600753768,-1936600753766⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨772749089830,772749089836⟩,⟨-1936600753768,-1936600753766⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1348963508032,1348963535166⟩,⟨-8759765096212,-8759765027846⟩,⟨-3968995362957,-3968995331974⟩,⟨53277334944254,53277334956689⟩,⟨34086403245401,34086403328729⟩,⟨10937517349863,10937517352491⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1348963535166,-1348963508032⟩,⟨8759765027846,8759765096212⟩,⟨3968995331974,3968995362957⟩,⟨-53277334956689,-53277334944254⟩,⟨-34086403328729,-34086403245401⟩,⟨-10937517352491,-10937517349863⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-249451907390,-249451880256⟩,⟨8759765027846,8759765096212⟩,⟨3968995331974,3968995362957⟩,⟨-53277334956689,-53277334944254⟩,⟨-34086403328729,-34086403245401⟩,⟨-10937517352491,-10937517349863⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11878360017,-11878358723⟩,⟨446889628457,446889634984⟩,⟨89457811211,89457823530⟩,⟨-4627660958584,-4627660941463⟩,⟨1648038887231,1648038949448⟩,⟨2646623414025,2646623438925⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437400844913,437401011246⟩,⟨867050401979,867053824128⟩,⟨-72297001297,-72294029759⟩,⟨-18546931573025,-18546832927357⟩,⟨-5542506915564,-5542402444470⟩,⟨-1276373791317,-1276262536022⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99813991384,-99813991382⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4752926271,4752926273⟩,⟨29871436732,29871436737⟩,⟨39828121951,39828121953⟩,⟨-314138186225,-314138186214⟩,⟨250313839737,250313839741⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10391896223,10391896478⟩,⟨12955162215,12955163824⟩,⟨87081028926,87081031027⟩,⟨-884678973582,-884678956549⟩,⟨108560442911,108560456131⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1470944954796,1470944975889⟩,⟨-7327834339549,-7327833964254⟩,⟨-1370733861989,-1370733794833⟩,⟨106751062587075,106751069988221⟩,⟨22558355063368,22558356561613⟩,⟨5031271036428,5031271321396⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13902451719,13902452260⟩,⟨-51926477106,-51926469456⟩,⟨103543130320,103543135756⟩,⟨-347276651204,-347276486444⟩,⟨-238071998552,-238071912866⟩,⟨-169571093876,-169571074138⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13902452260,-13902451719⟩,⟨51926469456,51926477106⟩,⟨-103543135756,-103543130320⟩,⟨347276486444,347276651204⟩,⟨238071912866,238071998552⟩,⟨169571074138,169571093876⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113716443644,-113716443101⟩,⟨-825535349118,-825535341466⟩,⟨-103543135756,-103543130320⟩,⟨2546299741996,2546299906756⟩,⟨238071912866,238071998552⟩,⟨169571074138,169571093876⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨91396840028,91396841874⟩,⟨-593503711900,-593503707239⟩,⟨600747466741,600747482167⟩,⟨3609719632990,3609719633969⟩,⟨-3337844629880,-3337844590607⟩,⟨-2401461630220,-2401461629852⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨122272213705,122272217929⟩,⟨-1403124969877,-1403124908754⟩,⟨689747784484,689747824532⟩,⟨21613779536070,21613780868365⟩,⟨-5854113496707,-5854112867793⟩,⟨-4292365227531,-4292365036984⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-122272217929,-122272213705⟩,⟨1403124908754,1403124969877⟩,⟨-689747824532,-689747784484⟩,⟨-21613780868365,-21613779536070⟩,⟨5854112867793,5854113496707⟩,⟨4292365036984,4292365227531⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨977239409847,977239414071⟩,⟨1403124908754,1403124969877⟩,⟨-689747824532,-689747784484⟩,⟨-21613780868365,-21613779536070⟩,⟨5854112867793,5854113496707⟩,⟨4292365036984,4292365227531⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123634567579,123634568118⟩,⟨782368206131,782368216493⟩,⟨186792377037,186792383297⟩,⟨-2513379808246,-2513379557368⟩,⟨-666424945307,-666424817828⟩,⟨-155010023371,-155009975431⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11761066554,11761066667⟩,⟨170761163982,170761166382⟩,⟨21417793482,21417794710⟩,⟨712957317158,712957376736⟩,⟨106239553928,106239581496⟩,⟨-15573899700,-15573893398⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171391214351,171391371084⟩,⟨1680236582606,1680242194182⟩,⟨107044093243,107046810871⟩,⟨-2004366140797,-2004148581205⟩,⟨498129161855,498265437669⟩,⟨-540077728432,-539978319242⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171391371084,-171391214351⟩,⟨-1680242194182,-1680236582606⟩,⟨-107046810871,-107044093243⟩,⟨2004148581205,2004366140797⟩,⟨-498265437669,-498129161855⟩,⟨539978319242,540077728432⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58012185253,58012402679⟩,⟨-82378821382,-82371528347⟩,⟨134372674825,134376257799⟩,⟨-1827982508173,-1827709747756⟩,⟨-1789535028323,-1789359176346⟩,⟨410295883579,410427890478⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27970702496571,27970728368616⟩,⟨-243436286601533,-243435641671072⟩,⟨-84003465683520,-84003025100742⟩,⟨3405073760969202,3405096646962563⟩,⟨1300398340298951,1300416450629818⟩,⟨303746144041639,303762402795882⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13902086994,13902087116⟩,⟨175946761104,175946764204⟩,⟨42007731756,42007733350⟩,⟨548169524071,548169612451⟩,⟨115955584342,115955626096⟩,⟨28606873139,28606888328⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353658051054,353658381281⟩,⟨1397967977522,1397980377930⟩,⟨6514046184,6520655193⟩,⟨-20912316825433,-20911804153300⟩,⟨-3351246576199,-3350917923399⟩,⟨-1850576806949,-1850336230854⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353658381281,-353658051054⟩,⟨-1397980377930,-1397967977522⟩,⟨-6520655193,-6514046184⟩,⟨20911804153300,20912316825433⟩,⟨3350917923399,3351246576199⟩,⟨1850336230854,1850576806949⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83742463632,83742960192⟩,⟨-530929975951,-530914153394⟩,⟨-78817656490,-78808075943⟩,⟨2364872580275,2365483898076⟩,⟨-2191588992165,-2191155868271⟩,⟨573962439537,574314270927⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238917718963,238917718969⟩,⟨1557994171313,1557994171324⟩,⟨308344998148,308344998153⟩,⟨-3904517942808,-3904517942803⟩,⟨-1545498179672,-1545498179662⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1657164077269,-1657162569850⟩,⟨-4215734200413,-4215691092948⟩,⟨473887074964,473911882645⟩,⟨43480253704768,43481825619902⟩,⟨-7888686213493,-7887581233422⟩,⟨1886884883042,1887802935942⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186339789247,-186339618932⟩,⟨-1653209420273,-1653203482750⟩,⟨-228243883533,-228240828275⟩,⟨2677759763298,2678001789058⟩,⟨-261618795044,-261468431912⟩,⟨606812966163,606924916691⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52577929716,52578100037⟩,⟨-95215248960,-95209311426⟩,⟨80101114615,80104169878⟩,⟨-1226758179510,-1226516153745⟩,⟨-1807116974716,-1806966611574⟩,⟨256685135040,256797085570⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4418401034,4418443795⟩,⟨-34287195303,-34285662819⟩,⟨6075694916,6076549568⟩,⟨65097247246,65160983155⟩,⟨-310913624545,-310871232745⟩,⟨42267456613,42299228262⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2514242344,2514258635⟩,⟨-9106291846,-9105694488⟩,⟨7660766230,7661083250⟩,⟨-100837135145,-100811551405⟩,⟨-186704556754,-186688222072⟩,⟨36220010864,36231687566⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4389032891,4389061419⟩,⟨-33398306595,-33397150082⟩,⟨5443224837,5443829901⟩,⟨36363820771,36417356279⟩,⟨-291865469112,-291832476624⟩,⟨32480064336,32502562915⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4389061419,-4389032891⟩,⟨33397150082,33398306595⟩,⟨-5443829901,-5443224837⟩,⟨-36417356279,-36363820771⟩,⟨291832476624,291865469112⟩,⟨-32502562915,-32480064336⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨29339615,29410904⟩,⟨-890045221,-887356224⟩,⟨631865015,633324731⟩,⟨28679890967,28797162384⟩,⟨-19081147921,-19005763633⟩,⟨9764893698,9819163926⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58012185253,58012402679⟩,⟨-82378821382,-82371528347⟩,⟨134372674825,134376257799⟩,⟨-1827982508173,-1827709747756⟩,⟨-1789535028323,-1789359176346⟩,⟨410295883579,410427890478⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨29339615,29410904⟩,⟨-890045221,-887356224⟩,⟨631865015,633324731⟩,⟨28679890967,28797162384⟩,⟨-19081147921,-19005763633⟩,⟨9764893698,9819163926⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110810156236,111239652967⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨129278515609,133143986176⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111239652967,-110810156236⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438516160921,438945657652⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨51559907983,53153575732⟩,⟨-133143986176,-129278515609⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨162370064219,164393228699⟩,⟨966367641600,970233112167⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨51130411252,53583072463⟩,⟨-133143986176,-129278515609⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2523162584128,-2518909091008⟩,⟨10867759718499,10909882818322⟩,⟨0,0⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-255273089568,-253858806826⟩,⟨-1427896175006,-1415135790242⟩,⟨0,0⟩,⟨10783350251024,10993966380516⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨253858806826,255273089568⟩,⟨1415135790242,1427896175006⟩,⟨0,0⟩,⟨-10993966380516,-10783350251024⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988271974809,988701471540⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117277700736,-116799963712⟩,⟨-1223272389009,-1222740993529⟩,⟨0,0⟩,⟨-1360963631407,-1359781469778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105458307459,-104983092383⟩,⟨-983189504844,-981756293837⟩,⟨0,0⟩,⟨1221677971627,1224334949129⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104983092383,105458307459⟩,⟨981756293837,983189504844⟩,⟨0,0⟩,⟨-1224334949129,-1221677971627⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨358841899209,360731397027⟩,⟨2396892084079,2411085679850⟩,⟨0,0⟩,⟨-12218301329645,-12005028222651⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2103083544896,-2089468015360⟩,⟨6463359026733,6570069388174⟩,⟨2932928696127,2972381989696⟩,⟨-39259077098370,-37994150178254⟩,⟨-25206797002344,-24594767306837⟩,⟨-8035435432852,-7823537759182⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-314442053577,-308561589770⟩,⟨-901332234818,-854124081073⟩,⟨-406470980099,-388923599757⟩,⟨5491561386417,5984370668461⟩,⟨3476218269945,3716848115400⟩,⟨1138052620582,1217922550626⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨308561589770,314442053577⟩,⟨854124081073,901332234818⟩,⟨388923599757,406470980099⟩,⟨-5984370668461,-5491561386417⟩,⟨-3716848115400,-3476218269945⟩,⟨-1217922550626,-1138052620582⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164393228699,-162370064219⟩,⟨-970233112167,-966367641600⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨935118399077,937141563557⟩,⟨-970233112167,-966367641600⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-178063966592,-175687700608⟩,⟨-1140799485428,-1133801444695⟩,⟨-516112029265,-514493900014⟩,⟨-1183637747047,-1169160637794⟩,⟨754521490806,762265967005⟩,⟨-242263583234,-240746861119⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151768421407,-149419794370⟩,⟨-817919230563,-807153842617⟩,⟨-369826137181,-366482988461⟩,⟨984165969704,1018978988518⟩,⟨1368029225289,1384867947538⟩,⟨203901896854,207331548940⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149419794370,151768421407⟩,⟨807153842617,817919230563⟩,⟨366482988461,369826137181⟩,⟨-1018978988518,-984165969704⟩,⟨-1384867947538,-1368029225289⟩,⟨-207331548940,-203901896854⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨457981384140,466210474984⟩,⟨1661277923690,1719251465381⟩,⟨755406588218,776297117280⟩,⟨-7003349656979,-6475727356121⟩,⟨-5101716062938,-4844247495234⟩,⟨-1425254099566,-1341954517436⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨816823283349,826941872011⟩,⟨4058170007769,4130337145231⟩,⟨755406588218,776297117280⟩,⟨-19221650986624,-18480755578772⟩,⟨-5101716062938,-4844247495234⟩,⟨-1425254099566,-1341954517436⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨102260822504,107166144926⟩,⟨-266287972352,-258557031218⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11280855725932,11821984118770⟩,⟨27217033589379,30784538037935⟩,⟨-101489670563957,-92320901311786⟩,⟨131331688907710,160326350075937⟩,⟨-297079354908557,-191259878103147⟩,⟨1511081965072563,1742542220950306⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8380507654730,8891305404232⟩,⟨61855768861680,67562544836776⟩,⟨-68579925418666,-60238098321224⟩,⟨91803874480931,162256471037715⟩,⟨-640835782051757,-510798366447151⟩,⟨963941896229475,1169940421083630⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨93750345728,99399374080⟩,⟨-792443438450,-644967108188⟩,⟨628099735755,804376330683⟩,⟨6908528222534,11622387258324⟩,⟨-7442980342592,-1064810195740⟩,⟨-5365494503787,2910355541414⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1193261973504,1198911001856⟩,⟨-792443438450,-644967108188⟩,⟨628099735755,804376330683⟩,⟨6908528222534,11622387258324⟩,⟨-7442980342592,-1064810195740⟩,⟨-5365494503787,2910355541414⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨89967104320,95160026432⟩,⟨-730183978270,-591494142507⟩,⟨576025211042,741179345637⟩,⟨5850841559498,10391057007006⟩,⟨-6548332894214,-484312796393⟩,⟨-5443574724027,2379924336899⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨97638189300,103762797723⟩,⟨-864778979555,-694702331119⟩,⟨676534268282,877801125828⟩,⟨7608937774825,13388851812307⟩,⟨-8852864971372,-1288521673263⟩,⟨-5741948970514,3931419292881⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-99399374080,-93750345728⟩,⟨644967108188,792443438450⟩,⟨-804376330683,-628099735755⟩,⟨-11622387258324,-6908528222534⟩,⟨1064810195740,7442980342592⟩,⟨-2910355541414,5365494503787⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1000112253696,1005761282048⟩,⟨644967108188,792443438450⟩,⟨-804376330683,-628099735755⟩,⟨-11622387258324,-6908528222534⟩,⟨1064810195740,7442980342592⟩,⟨-2910355541414,5365494503787⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-104182969856,-97989968448⟩,⟨705086632030,871202979177⟩,⟨-884321860298,-686646995854⟩,⟨-13467817205204,-8004647764109⟩,⟨1604392560793,8883421290795⟩,⟨-3910858323580,5469949149799⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-95299762807,-89131361332⟩,⟨566257467425,739439127465⟩,⟨-752942664502,-548354145852⟩,⟨-10876580985481,-4923943675023⟩,⟨-520603178508,7225508865665⟩,⟨-3301299730336,6573216250710⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2338426493,14631436391⟩,⟨-298521512130,44736796346⟩,⟨-76408396220,329446979976⟩,⟨-3267643210656,8464908137284⟩,⟨-9373468149880,5936987192402⟩,⟨-9043248700850,10504635543591⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1169213246,7315718196⟩,⟨-149260756065,22368398173⟩,⟨-38204198110,164723489988⟩,⟨-1633821605328,4232454068642⟩,⟨-4686734074940,2968493596201⟩,⟨-4521624350425,5252317771796⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7315718196,-1169213246⟩,⟨-22368398173,149260756065⟩,⟨-164723489988,38204198110⟩,⟨-4232454068642,1633821605328⟩,⟨-2968493596201,4686734074940⟩,⟨-5252317771796,4521624350425⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754807665420,760954189634⟩,⟨-22368398173,149260756065⟩,⟨-164723489988,38204198110⟩,⟨-4232454068642,1633821605328⟩,⟨-2968493596201,4686734074940⟩,⟨-5252317771796,4521624350425⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7993664734,8986021901⟩,⟨-143278851786,-109986812050⟩,⟨107110404094,145436395170⟩,⟨1934785323061,3243666691443⟩,⟨-2505203761100,-918462308998⟩,⟨-252507592907,1703135786613⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8986021901,-7993664734⟩,⟨109986812050,143278851786⟩,⟨-145436395170,-107110404094⟩,⟨-3243666691443,-1934785323061⟩,⟨918462308998,2505203761100⟩,⟨-1703135786613,252507592907⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090525605875,1091517963042⟩,⟨109986812050,143278851786⟩,⟨-145436395170,-107110404094⟩,⟨-3243666691443,-1934785323061⟩,⟨918462308998,2505203761100⟩,⟨-1703135786613,252507592907⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9022943424,-8022864064⟩,⟨110792293709,144459481469⟩,⟨-146634803191,-107894820556⟩,⟨-3289374603570,-1960118590422⟩,⟨936060633320,2545112482055⟩,⟨-1736725509281,244000582852⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4511471712,-4011432032⟩,⟨55396146854,72229740735⟩,⟨-73317401596,-53947410278⟩,⟨-1644687301785,-980059295211⟩,⟨468030316660,1272556241028⟩,⟨-868362754641,122000291426⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4011432032,4511471712⟩,⟨-72229740735,-55396146854⟩,⟨53947410278,73317401596⟩,⟨980059295211,1644687301785⟩,⟨-1272556241028,-468030316660⟩,⟨-122000291426,868362754641⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766134815648,766634874592⟩,⟨-72229740735,-55396146854⟩,⟨53947410278,73317401596⟩,⟨980059295211,1644687301785⟩,⟨-1272556241028,-468030316660⟩,⟨-122000291426,868362754641⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272631401468,272879490761⟩,⟨27496703012,35819712947⟩,⟨-36359098793,-26777601023⟩,⟨-810916672861,-483696330765⟩,⟨229615577249,626300940275⟩,⟨-425783946654,63126898227⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532269631296,1533269749184⟩,⟨-144459481470,-110792293708⟩,⟨107894820556,146634803192⟩,⟨1960118590422,3289374603570⟩,⟨-2545112482056,-936060633320⟩,⟨-244000582852,1736725509282⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1202000754247,1208790128456⟩,⟨-957790290260,-770810096136⟩,⟨750651640299,972213033589⟩,⟨9245086898368,15565268989858⟩,⟨-10536666063209,-2235315610111⟩,⟨-5547462213855,5081488938053⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1304489880718,1318068629136⟩,⟨-1915580580519,-1541620192273⟩,⟨1501303280598,1944426067177⟩,⟨18490173796743,31130537979698⟩,⟨-21073332126407,-4470631220223⟩,⟨-11090107434214,10162977876101⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨187957072768,199342996288⟩,⟨-1614579885483,-1285994742268⟩,⟨1252363023704,1638892797724⟩,⟨13053272442836,24734800465012⟩,⟨-16297248180123,-1322693417704⟩,⟨-11790362027147,7139576440969⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨64359009767,68792696906⟩,⟨-550459444017,-429272123688⟩,⟨416294900236,560149612516⟩,⟨4144881459404,8223611533523⟩,⟨-5463426311184,-79373963992⟩,⟨-4429213708144,2478877812070⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379936697761,380530644504⟩,⟨2466852716,22478910961⟩,⟨-23949533123,-924841899⟩,⟨-654211471170,136748733670⟩,⟨-306265536410,650828584556⟩,⟨-664010638938,513799938802⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176947342021,3181913794427⟩,⟨-188257563147,-20595085553⟩,⟨7721254661,200573806804⟩,⟨-1144983448849,5501201034029⟩,⟨-5474327235964,2564828577673⟩,⟨-4302961158785,5586277720080⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨185960002467,199081506472⟩,⟨-1604771790583,-1241551591797⟩,⟨1203301425543,1633585081534⟩,⟨11920733803264,24331276782472⟩,⟨-16349627390746,-79684084485⟩,⟨-13081225789690,7727588395283⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨373917075235,398424502760⟩,⟨-3219351676066,-2527546334065⟩,⟨2455664449247,3272477879258⟩,⟨24974006246100,49066077247484⟩,⟨-32646875570869,-1402377502189⟩,⟨-24871587816837,14867164836252⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518170610827,526644070053⟩,⟨-30961612184,206601903622⟩,⟨-228004919042,52881013496⟩,⟨-5864498925786,2302007795135⟩,⟨-4153615721568,6497598074058⟩,⟨-7281535258850,6308042105160⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355720793820,364481831233⟩,⟨-32142045497,214478746986⟩,⟨-236697767472,54897139452⟩,⟨-6094391730578,2431843357889⟩,⟨-4358403392046,6756091630094⟩,⟨-7571032493556,6599778545449⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711441587640,728963662466⟩,⟨-64284090994,428957493972⟩,⟨-473395534944,109794278904⟩,⟨-12188783461156,4863686715778⟩,⟨-8716806784092,13512183260188⟩,⟨-15142064987112,13199557090898⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523283609395,1525276084450⟩,⟨-34472669420,32486558078⟩,⟨-37541574614,39524399098⟩,⟨-1283548101021,1354589280509⟩,⟨-1626650173058,1569143127780⟩,⟨-1947136369465,1989233102189⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨985644246151,1011240638757⟩,⟨-112031839271,616601143665⟩,⟨-681598368521,178514199930⟩,⟨-17786528093242,7670480134015⟩,⟨-13199304266490,19815099032531⟩,⟨-22330498360449,19661994366602⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67600814023,67723900864⟩,⟨13635989812,17779648312⟩,⟨-18047380516,-13279377334⟩,⟨-401135294058,-237537745678⟩,⟨111500492752,309534490778⟩,⟨-210039919004,33738651668⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50220404652,50935095133⟩,⟨259636899443,267778231336⟩,⟨32870926272,37950453059⟩,⟨-1384984377271,-1179131321372⟩,⟨-289831372246,-101495719570⟩,⟨-271242997863,-75378895635⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135357338367,2138145758875⟩,⟨-402897699898,-308798311434⟩,⟨300722525774,408964675284⟩,⟨5485535661476,9212030118170⟩,⟨-7136853609414,-2630715600636⟩,⟨-659342586310,4882841406518⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2975815006306,2981645785830⟩,⟨-842761694826,-645507873022⟩,⟨628626358352,855452297080⟩,⟨11513564702937,19348676007543⟩,⟨-15009118990657,-5544666276134⟩,⟨-1334925443567,10295500223970⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135920921626,138125334847⟩,⟨663663044590,696674913717⟩,⟨117677396485,142542696784⟩,⟨-3640401178673,-2599831853182⟩,⟨-1361908273666,-338909383586⟩,⟨-759808276256,331982154468⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8752382906102,8894332124536⟩,⟨-45588699600507,-42053350265645⟩,⟨-9327644868482,-7456688771619⟩,⟨568854605149527,705556898259257⟩,⟨93130794979277,184739307066327⟩,⟨-9018483041773,69284127533349⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7845970550542,8180277381083⟩,⟨-42835012292123,-32710329251658⟩,⟨-14092489273090,-5240397331327⟩,⟨314929722330543,720252845052639⟩,⟨-35920339066085,359410608542535⟩,⟨-191962462484188,234339175730258⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15691941101084,16360554762166⟩,⟨-85670024584246,-65420658503316⟩,⟨-28184978546180,-10480794662654⟩,⟨629859444661086,1440505690105278⟩,⟨-71840678132170,718821217085070⟩,⟨-383924924968376,468678351460516⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10867759718499,10909882818322⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108414,2148278590204846⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9768248090723,9810371190546⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108424,2148278590204831⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2401631390336,2406362620352⟩,⟨-12184942684160,-12039116462039⟩,⟨0,0⟩,⟨102958094106835,109987257462969⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7353866270417,7445496960475⟩,⟨-44490144918886,-43228899758370⟩,⟨-20127900888516,-19616314068104⟩,⟨508232732443555,531696676638537⟩,⟨279809601424706,290964486284868⟩,⟨104652372906615,108826152593593⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6254354642641,6345985332699⟩,⟨-44490144918887,-43228899758370⟩,⟨-20127900888517,-19616314068104⟩,⟨508232732443560,531696676638533⟩,⟨279809601424708,290964486284867⟩,⟨104652372906615,108826152593593⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1911404048832,1927395844032⟩,⟨-7821339603342,-7489881468090⟩,⟨-3538472365926,-3398741768404⟩,⟨32420059870622,42450813817041⟩,⟨23309279155923,27999119939997⟩,⟨6744583372077,8625590867329⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99599284960,100028781692⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138093341329,140116505810⟩,⟨676817224332,684246151401⟩,⟨307322658486,309366735309⟩,⟨-1712309844053,-1698693120000⟩,⟨-1549441999836,-1541554359496⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4313035439168,4333758464384⟩,⟨-20006282287502,-19528997930129⟩,⟨-3538472365926,-3398741768404⟩,⟨135378153977457,152438071280010⟩,⟨23309279155923,27999119939997⟩,⟨6744583372077,8625590867329⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨747834150470,796849005520⟩,⟨-6438703352132,-5055092668130⟩,⟨4911328898494,6544955758516⟩,⟨49948012492200,98132154494968⟩,⟨-65293751141738,-2804755004378⟩,⟨-49743175633674,29734329672504⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5060869589638,5130607469904⟩,⟨-26444985639634,-24584090598259⟩,⟨1372856532568,3146213990112⟩,⟨185326166469657,250570225774978⟩,⟨-41984471985815,25194364935619⟩,⟨-42998592261597,38359920539833⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458438982972,466760333943⟩,⟨1630984580828,1869519014767⟩,⟨124360239166,286228853269⟩,⟨-35702776521630,-26545257809538⟩,⟨-2724496908204,4804128882844⟩,⟨-3911824749957,3489818588971⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨221620312472,222479305934⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-222479305934,-221620312472⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨877032321842,877891315304⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1915676288695,1921330154691⟩,⟨-14541640415106,-14406339271082⟩,⟨0,0⟩,⟨130281633100448,136557721617390⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨816164660919,821818526915⟩,⟨-14541640415106,-14406339271082⟩,⟨0,0⟩,⟨130281633100448,136557721617390⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37953973116,40050110037⟩,⟨-808182418660,-765898773735⟩,⟨325509421405,328085365043⟩,⟨9446206414993,10176742065249⟩,⟨-6627114036394,-6561817940510⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨496392956088,506810443980⟩,⟨822802162168,1103620241032⟩,⟨449869660571,614314218312⟩,⟨-26256570106637,-16368515744289⟩,⟨-9351610944598,-1757689057666⟩,⟨-3911824749957,3489818588971⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502387216868,503376923070⟩,⟨2513460839922,2553938535635⟩,⟨0,0⟩,⟨2096765778922,4420352332343⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226811130853,232027270496⟩,⟨1510697570323,1682473961693⟩,⟨205553775893,281244502742⟩,⟨-7312309826560,-314590412355⟩,⟨-3252949107379,623804445546⟩,⟨-1790906304653,1597704016048⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-796849005520,-747834150470⟩,⟨5055092668130,6438703352132⟩,⟨-6544955758516,-4911328898494⟩,⟨-98132154494968,-49948012492200⟩,⟨2804755004378,65293751141738⟩,⟨-29734329672504,49743175633674⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3516186433648,3585924313914⟩,⟨-14951189619372,-13090294577997⟩,⟨-10083428124442,-8310070666898⟩,⟨37245999482489,102490058787810⟩,⟨26114034160301,93292871081735⟩,⟨-22989746300427,58368766501003⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441616005771,456973052647⟩,⟨259121493478,587508469612⟩,⟨-302180481288,-34742449325⟩,⟨-19515370599870,-8487264922042⟩,⟨-12255400284673,-1815228193191⟩,⟨-9747017165660,1674172171557⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨324740128438,328786457398⟩,⟨1932735283200,1940466224334⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-328786457398,-324740128438⟩,⟨-1940466224334,-1932735283200⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨770725170378,774771499338⟩,⟨-1940466224334,-1932735283200⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1339837773409,1358140587307⟩,⟨-8912863947971,-8610075579993⟩,⟨-4032291702010,-3907060963182⟩,⟨49057118783981,57519874942782⟩,⟨32110625735670,36074089296903⟩,⟨10149808929365,11728525612795⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1358140587307,-1339837773409⟩,⟨8610075579993,8912863947971⟩,⟨3907060963182,4032291702010⟩,⟨-57519874942782,-49057118783981⟩,⟨-36074089296903,-32110625735670⟩,⟨-11728525612795,-10149808929365⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-258628959531,-240326145633⟩,⟨8610075579993,8912863947971⟩,⟨3907060963182,4032291702010⟩,⟨-57519874942782,-49057118783981⟩,⟨-36074089296903,-32110625735670⟩,⟨-11728525612795,-10149808929365⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12603899704,-11175847849⟩,⟨428650048601,465673588579⟩,⟨78439893609,100658944311⟩,⟨-4961730242646,-4306008339688⟩,⟨1427963751390,1864191230518⟩,⟨2544919252906,2747537984106⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429012106067,445797204798⟩,⟨687771542079,1053182058191⟩,⟨-223740587679,65916494986⟩,⟨-24477100842516,-12793273261730⟩,⟨-10827436533283,48963037327⟩,⟨-7202097912754,4421710155663⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100028781692,-99599284960⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4631649426,4874754685⟩,⟨28671631816,31072037244⟩,⟨39722996071,39933365192⟩,⟨-319780447852,-308500454436⟩,⟨249756374792,250871388573⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10116777639,10668761623⟩,⟨8603896771,17289150594⟩,⟨86765789348,87397126939⟩,⟨-954845658958,-814093897021⟩,⟨102988436616,114103164432⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1461923577136,1480033495934⟩,⟨-7483916593788,-7174306459956⟩,⟨-1406602578298,-1335458680974⟩,⟨103086523725296,110514583197944⟩,⟨21671361633509,23469209076354⟩,⟨4812265111941,5256102450165⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13451386398,14361034630⟩,⟨-61177963837,-42739285321⟩,⟨101716291765,105355990670⟩,⟨-572146057171,-122366420712⟩,⟨-280657515678,-195278161469⟩,⟨-179335467783,-159769250863⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14361034630,-13451386398⟩,⟨42739285321,61177963837⟩,⟨-105355990670,-101716291765⟩,⟨122366420712,572146057171⟩,⟨195278161469,280657515678⟩,⟨159769250863,179335467783⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114389816322,-113050671358⟩,⟨-835152029983,-815854358005⟩,⟨-105355990670,-101716291765⟩,⟨2321389676264,2771169312723⟩,⟨195278161469,280657515678⟩,⟨159769250863,179335467783⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨88885713089,93928784896⟩,⟨-614557004463,-573040049725⟩,⟨589879477293,611401421300⟩,⟨3268917235403,3963008290997⟩,⟨-3566255943736,-3105596857303⟩,⟨-2511606760848,-2290672204256⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨118183488334,126435905148⟩,⟨-1466578527183,-1341899501265⟩,⟨664147814415,715036899990⟩,⟨20158182642663,23141612705759⟩,⟨-6514082772612,-5187075342570⟩,⟨-4556130215655,-4029614250445⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-126435905148,-118183488334⟩,⟨1341899501265,1466578527183⟩,⟨-715036899990,-664147814415⟩,⟨-23141612705759,-20158182642663⟩,⟨5187075342570,6514082772612⟩,⟨4029614250445,4556130215655⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨973075722628,981328139442⟩,⟨1341899501265,1466578527183⟩,⟨-715036899990,-664147814415⟩,⟨-23141612705759,-20158182642663⟩,⟨5187075342570,6514082772612⟩,⟨4029614250445,4556130215655⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122213603302,125055767014⟩,⟨767524211833,797592166601⟩,⟨180861885414,192700001151⟩,⟨-2825271033540,-2209768722975⟩,⟨-801333584488,-530339707393⟩,⟨-209075643059,-100220624503⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11623755467,11900765529⟩,⟨167770636658,173773309710⟩,⟨20916732086,21921828050⟩,⟨634144789356,791340884098⟩,⟨92552578732,119893124474⟩,⟨-18495388231,-12664052158⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165891184371,177081461652⟩,⟨1467113246224,1894108220569⟩,⟨-6547173324,215392969077⟩,⟨-11370532395112,7401981998179⟩,⟨-5619285735276,6720515384883⟩,⟨-5554582304608,4493321885705⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177081461652,-165891184371⟩,⟨-1894108220569,-1467113246224⟩,⟨-215392969077,6547173324⟩,⟨-7401981998179,11370532395112⟩,⟨-6720515384883,5619285735276⟩,⟨-4493321885705,5554582304608⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49729669201,66136086125⟩,⟨-383410650246,215360715469⟩,⟨-9839193184,287791676066⟩,⟨-14714291824739,11055941982757⟩,⟨-9973464492262,6243090180822⟩,⟨-6284228190358,7152286320656⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27279056443735,28679337678711⟩,⟨-266556075290074,-220621668988189⟩,⟨-102058931071209,-66725887337054⟩,⟨2448937737619556,4375626537481064⟩,⟨480349849972722,2152882611867155⟩,⟨-511951539562059,1131331095142282⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13584362779,14223537495⟩,⟨170624661312,181432369862⟩,⟨40206546538,43834454934⟩,⟨428875827541,665912859632⟩,⟨70221158258,161674115240⟩,⟨11941495701,45265490914⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337030177434,371002565594⟩,⟨784993458377,2006668558059⟩,⟨-322727264915,318972956555⟩,⟨-47072912206325,5500471877501⟩,⟨-19790896146323,13644963262787⟩,⟨-14464062053449,10935836654535⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371002565594,-337030177434⟩,⟨-2006668558059,-784993458377⟩,⟨-318972956555,322727264915⟩,⟨-5500471877501,47072912206325⟩,⟨-13644963262787,19790896146323⟩,⟨-10935836654535,14464062053449⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58009540473,108767027364⟩,⟨-1318897015980,268188599814⟩,⟨-542713544234,388643759901⟩,⟨-29977572720017,34279638944595⟩,⟨-24472399796070,19839859183650⟩,⟨-18137934567289,18885772209112⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237692626289,240145287502⟩,⟨1553849546174,1562137466705⟩,⟨307322658486,309366735309⟩,⟨-3911333099605,-3897716375552⟩,⟨-1549441999836,-1541554359496⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1702101921338,-1613429482302⟩,⟨-5700440994396,-2730812553985⟩,⟨-490055373941,1480610498712⟩,⟨-19649280641139,106617175421325⟩,⟨-58167993114654,41267546284251⟩,⟨-44540507340289,48012263563146⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-193592915193,-179336921706⟩,⟨-1883068926044,-1429806283264⟩,⟨-354047454375,-96996715534⟩,⟨-7262500750346,12687507839790⟩,⟨-7192208239498,6559020690009⟩,⟨-5090638060729,6303440194950⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44099711096,60808365796⟩,⟨-329219379870,132331183441⟩,⟨-46724795889,212370019775⟩,⟨-11173833849951,8789791464238⟩,⟨-8741650239334,5017466330513⟩,⟨-5441108734262,5953655038466⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2623706003,6542382371⟩,⟨-117260354570,37435792518⟩,⟨-33617770439,51846311438⟩,⟨-3775409207044,4075447052635⟩,⟨-2939369156073,2070407932249⟩,⟨-1996764425034,2046964125314⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1768771215,3362999770⟩,⟨-36414880886,14637122166⟩,⟨-5168219070,23490199686⟩,⟨-1315181300456,1169388733089⟩,⟨-1094089005398,606100191436⟩,⟨-619889535440,740570719613⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3074852849,5895191662⟩,⟨-87756282818,13609352835⟩,⟨-19882541628,35709778462⟩,⟨-2461542963386,2697800811227⟩,⟨-2094595130429,1302061237016⟩,⟨-1226982689658,1357835561083⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5895191662,-3074852849⟩,⟨-13609352835,87756282818⟩,⟨-35709778462,19882541628⟩,⟨-2697800811227,2461542963386⟩,⟨-1302061237016,2094595130429⟩,⟨-1357835561083,1226982689658⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3271485659,3467529522⟩,⟨-130869707405,125192075336⟩,⟨-69327548901,71728853066⟩,⟨-6473210018271,6536990016021⟩,⟨-4241430393089,4165003062678⟩,⟨-3354599986117,3273946814972⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49729669201,66136086125⟩,⟨-383410650246,215360715469⟩,⟨-9839193184,287791676066⟩,⟨-14714291824739,11055941982757⟩,⟨-9973464492262,6243090180822⟩,⟨-6284228190358,7152286320656⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3271485659,3467529522⟩,⟨-130869707405,125192075336⟩,⟨-69327548901,71728853066⟩,⟨-6473210018271,6536990016021⟩,⟨-4241430393089,4165003062678⟩,⟨-3354599986117,3273946814972⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (517/5120) u, BivariateJet2.affineZ (611/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000025

end


