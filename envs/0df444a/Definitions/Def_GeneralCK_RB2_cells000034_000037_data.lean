-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000034_000037_data
-- name    : GeneralCK_RB2_cells000034_000037_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T03:05:56.504693+00:00
-- url     : https://prove2.me/theorems/8be1f2ac-9cb8-485c-beb6-095e99be9bd0
-- title:
--   Exact certificate data for RB2 cells 000034–000037
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000034 through 000037. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000034Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2508346996352,-2508346938496⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2508346996352,-2508346938496⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-118472952128,-118472952064⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-118472952128,-118472952064⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2141277806400,-2141277767168⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2141277806400,-2141277767168⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-169202906112,-169202906048⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-169202906112,-169202906048⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨80111941184,80111941248⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-86410969152,-86410969088⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨80112065216,80112065280⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-86411113472,-86411113408⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6299048256,-6299048192⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6299027968,-6299027904⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨166522910336,166522910400⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨166523178624,166523178688⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1972074861120,1972074899712⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1972074861184,1972074899776⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2506246686912,-2506246629056⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2148347702336,-2148347662976⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2134247820480,-2134247781376⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-170376798912,-170376798848⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-168031144896,-168031144832⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨77545184704,77545184768⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-83432013568,-83432013504⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨82701687424,82701687488⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-89431893824,-89431893760⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-6730206336,-6730206272⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-5886828864,-5886828800⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨160977198208,160977198272⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨172133581184,172133581248⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1963870982528,1963871021120⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1980316518144,1980316556736⟩



end LaneCBRB2Cell000034Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000034
open Set LaneCBRB2Cell000034Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112313394790,112313394791⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112313394791,-112313394790⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437442419097,437442419098⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨44513183661,44513183663⟩,⟨-111883898061,-111883898060⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156826578451,156826578454⟩,⟨987627729715,987627729716⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44513183660,44513183664⟩,⟨-111883898061,-111883898060⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2508346996352,-2508346938496⟩,⟨10763861442032,10763861442129⟩,⟨0,0⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-256223726387,-256223720474⟩,⟨-1408835368586,-1408835310710⟩,⟨0,0⟩,⟨10763861441838,10763861442323⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256223720474,256223726387⟩,⟨1408835310710,1408835368586⟩,⟨0,0⟩,⟨-10763861442323,-10763861441838⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨987198232985,987198232986⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-118472952128,-118472952064⟩,⟨-1224602900635,-1224602900633⟩,⟨0,0⟩,⟨-1363925788832,-1363925788826⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106371125183,-106371125124⟩,⟨-981038675714,-981038675646⟩,⟨0,0⟩,⟨1224602900628,1224602900640⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106371125124,106371125183⟩,⟨981038675646,981038675714⟩,⟨0,0⟩,⟨-1224602900640,-1224602900628⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨362594845598,362594851570⟩,⟨2389873986356,2389874044300⟩,⟨0,0⟩,⟨-11988464342963,-11988464342466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2141277806400,-2141277767168⟩,⟨6924261075134,6924261075276⟩,⟨3066910156562,3066910156630⟩,⟨-43606079487813,-43606079486036⟩,⟨-27022787697775,-27022787696814⟩,⟨-8554650693291,-8554650692920⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-305416753597,-305416747995⟩,⟨-935758331173,-935758295889⟩,⟨-414468301936,-414468286306⟩,⟨6219663414694,6219663415337⟩,⟨3796594227149,3796594266722⟩,⟨1220174997780,1220174997917⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305416747995,305416753597⟩,⟨935758295889,935758331173⟩,⟨414468286306,414468301936⟩,⟨-6219663415337,-6219663414694⟩,⟨-3796594266722,-3796594227149⟩,⟨-1220174997917,-1220174997780⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-156826578454,-156826578451⟩,⟨-987627729716,-987627729715⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨942685049322,942685049325⟩,⟨-987627729716,-987627729715⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-169202906112,-169202906048⟩,⟨-1151931043691,-1151931043685⟩,⟨-510216033051,-510216033047⟩,⟨-1206849564751,-1206849564736⟩,⟨747887449504,747887449517⟩,⟨-236760024911,-236760024907⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145068997785,-145068997729⟩,⟨-835642541261,-835642541193⟩,⟨-370124778551,-370124778518⟩,⟨1034713060517,1034713060548⟩,⟨1388606287275,1388606287364⟩,⟨202990245957,202990245967⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145068997729,145068997785⟩,⟨835642541193,835642541261⟩,⟨370124778518,370124778551⟩,⟨-1034713060548,-1034713060517⟩,⟨-1388606287364,-1388606287275⟩,⟨-202990245967,-202990245957⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨450485745724,450485751382⟩,⟨1771400837082,1771400872434⟩,⟨784593064824,784593080487⟩,⟨-7254376475885,-7254376475211⟩,⟨-5185200554086,-5185200514424⟩,⟨-1423165243884,-1423165243737⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨813080591322,813080602952⟩,⟨4161274823438,4161274916734⟩,⟨784593064824,784593080487⟩,⟨-19242840818848,-19242840817677⟩,⟨-5185200554086,-5185200514424⟩,⟨-1423165243884,-1423165243737⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89026367320,89026367328⟩,⟨-223767796122,-223767796120⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13579413109832,13579413111054⟩,⟨34131858183033,34131858189483⟩,⟨-133448359178339,-133448359154014⟩,⟨171580867833417,171580867882808⟩,⟨-335422483644127,-335422483395117⟩,⟨2622862183639574,2622862184359666⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨10041874012265,10041874156805⟩,⟨76633679168832,76633680691499⟩,⟨-88994019273128,-88994017649281⟩,⟨147580679219180,147580686947590⟩,⟨-792782144472580,-792782128338648⟩,⟨1731557193152588,1731557225268385⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨83102667776,83102801152⟩,⟨-628977125405,-628975069573⟩,⟨730423216654,730425602889⟩,⟨8270408023816,8270459374088⟩,⟨-4504254134510,-4504177892258⟩,⟨-1424916739699,-1424806489506⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1182614295552,1182614428928⟩,⟨-628977125405,-628975069573⟩,⟨730423216654,730425602889⟩,⟨8270408023816,8270459374088⟩,⟨-4504254134510,-4504177892258⟩,⟨-1424916739699,-1424806489506⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨80111941184,80112065280⟩,⟨-584778710684,-584776733363⟩,⟨679096077524,679098372668⟩,⟨7378226665656,7378277378023⟩,⟨-3826560661362,-3826486862441⟩,⟨-1744223260238,-1744117772833⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨86166916743,86167059937⟩,⟨-674805412487,-674802993999⟩,⟨783642782248,783645589546⟩,⟨9207519492430,9207584056681⟩,⟨-5220923082720,-5220832012913⟩,⟨-1077607098502,-1077479235764⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-83102801152,-83102667776⟩,⟨628975069573,628977125405⟩,⟨-730425602889,-730423216654⟩,⟨-8270459374088,-8270408023816⟩,⟨4504177892258,4504254134510⟩,⟨1424806489506,1424916739699⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1016408826624,1016408960000⟩,⟨628975069573,628977125405⟩,⟨-730425602889,-730423216654⟩,⟨-8270459374088,-8270408023816⟩,⟨4504177892258,4504254134510⟩,⟨1424806489506,1424916739699⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-86411113472,-86410969088⟩,⟨680400734145,680403047350⟩,⟨-790146073672,-790143388649⟩,⟨-9367711055133,-9367651469474⟩,⟨5361401437228,5361487876411⟩,⟨973474598822,973597924547⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-79880037426,-79879893472⟩,⟨579543391788,579545856858⟩,⟨-673021505459,-673018644071⟩,⟨-7231266209462,-7231199678418⟩,⟨3698178731257,3698271897708⟩,⟨1837722887797,1837852859254⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6286879317,6287166465⟩,⟨-95262020699,-95257137141⟩,⟨110621276789,110626945475⟩,⟨1976253282968,1976384378263⟩,⟨-1522744351463,-1522560115205⟩,⟨760115789295,760373623490⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3143439658,3143583233⟩,⟨-47631010350,-47628568570⟩,⟨55310638394,55313472738⟩,⟨988126641484,988192189132⟩,⟨-761372175732,-761280057602⟩,⟨380057894647,380186811745⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3143583233,-3143439658⟩,⟨47628568570,47631010350⟩,⟨-55313472738,-55310638394⟩,⟨-988192189132,-988126641484⟩,⟨761280057602,761372175732⟩,⟨-380186811745,-380057894647⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758979800383,758979963222⟩,⟨47628568570,47631010350⟩,⟨-55313472738,-55310638394⟩,⟨-988192189132,-988126641484⟩,⟨761280057602,761372175732⟩,⟨-380186811745,-380057894647⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6281018969,6281039132⟩,⟨-95078141352,-95077677990⟩,⟨110412871270,110413409190⟩,⟨1969788369967,1969802842876⟩,⟨-1516559007918,-1516540928598⟩,⟨755068873240,755092225544⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6281039132,-6281018969⟩,⟨95077677990,95078141352⟩,⟨-110413409190,-110412871270⟩,⟨-1969802842876,-1969788369967⟩,⟨1516540928598,1516559007918⟩,⟨-755092225544,-755068873240⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1093230588644,1093230608807⟩,⟨95077677990,95078141352⟩,⟨-110413409190,-110412871270⟩,⟨-1969802842876,-1969788369967⟩,⟨1516540928598,1516559007918⟩,⟨-755092225544,-755068873240⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6299048256,-6299027904⟩,⟨95623934831,95624402619⟩,⟨-111047777595,-111047234535⟩,⟨-1989436577453,-1989421903483⟩,⟨1534911742023,1534930047825⟩,⟨-770646059933,-770622449758⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3149524128,-3149513952⟩,⟨47811967415,47812201310⟩,⟨-55523888798,-55523617267⟩,⟨-994718288727,-994710951741⟩,⟨767455871011,767465023913⟩,⟨-385323029967,-385311224879⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3149513952,3149524128⟩,⟨-47812201310,-47811967415⟩,⟨55523617267,55523888798⟩,⟨994710951741,994718288727⟩,⟨-767465023913,-767455871011⟩,⟨385311224879,385323029967⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765272897568,765272927008⟩,⟨-47812201310,-47811967415⟩,⟨55523617267,55523888798⟩,⟨994710951741,994718288727⟩,⟨-767465023913,-767455871011⟩,⟨385311224879,385323029967⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273307647161,273307652202⟩,⟨23769419497,23769535338⟩,⟨-27603352298,-27603217817⟩,⟨-492450710719,-492447092491⟩,⟨379135232149,379139751980⟩,⟨-188773056386,-188767218310⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530545795136,1530545854016⟩,⟨-95624402620,-95623934830⟩,⟨111047234534,111047777596⟩,⟨1989421903482,1989436577454⟩,⟨-1534930047826,-1534911742022⟩,⟨770622449758,770646059934⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1189408857252,1189409013330⟩,⟨-736033614171,-736031015252⟩,⟨854746344847,854749361563⟩,⟨10589031874194,10589100818178⟩,⟨-6328788072451,-6328690139763⟩,⟨-438953122362,-438815158769⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1279306086728,1279306398884⟩,⟨-1472067228343,-1472062030503⟩,⟨1709492689694,1709498723127⟩,⟨21178063748396,21178201636356⟩,⟨-12657576144903,-12657380279531⟩,⟨-877906095702,-877630466562⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨166522910336,166523178688⟩,⟨-1265182000792,-1265177224749⟩,⟨1469239184260,1469244728253⟩,⟨16745866313276,16746000255017⟩,⟨-9188060295804,-9187876541658⟩,⟨-2717832724557,-2717580831931⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57364783242,57364887618⟩,⟨-430575686912,-430573984311⟩,⟨500021781267,500023757569⟩,⟨5579780427131,5579825144294⟩,⟨-2988414242966,-2988350441684⟩,⟨-1085829896560,-1085739785379⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380450610592,380450632246⟩,⟨9318049788,9318329034⟩,⟨-10821293493,-10820969313⟩,⟨-195123056240,-195114296176⟩,⟨151025928325,151036844567⟩,⟨-76797179703,-76783116064⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177615483190,3177615664051⟩,⟨-77828941463,-77826600273⟩,⟨90379346800,90382064719⟩,⟨1633453962538,1633527543376⟩,⟨-1265923747715,-1265832162958⟩,⟨646452343308,646570188164⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨165785625922,165785937008⟩,⟨-1248434906095,-1248429785173⟩,⟨1449790530136,1449796474331⟩,⟨16271878511613,16272014731828⟩,⟨-8773426199700,-8773234013542⟩,⟨-3022144669832,-3021875061056⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨332308536258,332309115696⟩,⟨-2513616906887,-2513607009922⟩,⟨2919029714396,2919041202584⟩,⟨33017744824889,33018014986845⟩,⟨-17961486495504,-17961110555200⟩,⟨-5739977394389,-5739455892987⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523914729810,523914954622⟩,⟨65754868892,65758254066⟩,⟨-76364481184,-76360551770⟩,⟨-1360148582209,-1360057372873⟩,⟨1046212763978,1046340656836⟩,⟨-519312208193,-519133545360⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361652107175,361652339953⟩,⟨68084705979,68088225707⟩,⟨-79070256726,-79066171119⟩,⟨-1404069340666,-1403974157803⟩,⟨1078320161159,1078453328404⟩,⟨-531950731935,-531765030717⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨723304214350,723304679906⟩,⟨136169411958,136176451414⟩,⟨-158140513452,-158132342238⟩,⟨-2808138681332,-2807948315606⟩,⟨2156640322318,2156906656808⟩,⟨-1063901463870,-1063530061434⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524264756004,1524264835047⟩,⟨-546724630,-545793478⟩,⟨633825344,634906326⟩,⟨19619060606,19648207487⟩,⟨-18389119228,-18352734104⟩,⟨15530224214,15577186694⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002724385946,1002725083350⟩,⟨188413457189,188423838636⟩,⟨-218814943864,-218802893269⟩,⟨-3880182154457,-3879898626551⟩,⟨2977833459148,2978227055914⟩,⟨-1464864291425,-1464318114932⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67936589399,67936591907⟩,⟨11816817490,11816875300⟩,⟨-13722833336,-13722766226⟩,⟨-243791077573,-243789264257⟩,⟨187291224204,187293486320⟩,⟨-92461383622,-92458466021⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50238597651,50238600225⟩,⟨265855163895,265855222029⟩,⟨38330478934,38330531465⟩,⟨-1279812540780,-1279810713712⟩,⟨-225386505710,-225384520056⟩,⟨-175893759749,-175891501801⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130555395532,2130555559457⟩,⟨-266222801608,-266221489014⟩,⟨309160673854,309162197660⟩,⟨5555275976872,5555317205703⟩,⟨-4292632544640,-4292581227080⟩,⟨2167879644569,2167945678331⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2965782734405,2965783076687⟩,⟨-555882532234,-555879770107⟩,⟨645538288229,645541494824⟩,⟨11634340035292,11634426909905⟩,⟨-9003498773124,-9003390879363⟩,⟨4573444828858,4573583343701⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135511768816,135511791399⟩,⟨691708823635,691709190716⟩,⟨132887008434,132887310090⟩,⟨-3189345074924,-3189334357043⟩,⟨-882626632406,-882615322960⟩,⟨-220472154804,-220459384591⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8921185434373,8921186921087⟩,⟨-45537498619699,-45537459275923⟩,⟨-8748410142614,-8748387367768⟩,⟨674848786525723,674850287935845⟩,⟨147416311354409,147417370043679⟩,⟨31671436546033,31672368564248⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8135875929467,8135882943887⟩,⟨-40000232465059,-40000083213389⟩,⟨-9753729777704,-9753605387042⟩,⟨568353065504215,568358041926015⟩,⟨166163821253275,166168671256784⟩,⟨20479763897883,20485268322563⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16271751858934,16271765887774⟩,⟨-80000464930118,-80000166426778⟩,⟨-19507459555408,-19507210774084⟩,⟨1136706131008430,1136716083852030⟩,⟨332327642506550,332337342513568⟩,⟨40959527795766,40970536645126⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10763861442032,10763861442129⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311394,2063168215367208⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9664349814256,9664349814353⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311405,2063168215367197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2389873986368,2389874044224⟩,⟨-11988464342936,-11988464342527⟩,⟨0,0⟩,⟨104010778944236,104010778977589⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7708679431332,7708679431481⟩,⟨-48546015868106,-48546015866178⟩,⟨-21502116617383,-21502116616501⟩,⟨611444716951234,611444716987939⟩,⟨324868121257467,324868121276160⟩,⟨119953365062878,119953365070385⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6609167803556,6609167803705⟩,⟨-48546015868106,-48546015866178⟩,⟨-21502116617384,-21502116616500⟩,⟨611444716951240,611444716987932⟩,⟨324868121257470,324868121276157⟩,⟨119953365062878,119953365070384⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1972074861120,1972074899776⟩,⟨-8076192119171,-8076192118628⟩,⟨-3577126189771,-3577126189525⟩,⟨42399229912622,42399229932120⟩,⟨27770675142234,27770675151559⟩,⟨8317890666270,8317890670187⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100840757001,100840757003⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134457942151,134457942155⟩,⟨705891231937,705891231945⟩,⟨312655020537,312655020542⟩,⟨-1774257784753,-1774257784749⟩,⟨-1571716941748,-1571716941736⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4361948847488,4361948944000⟩,⟨-20064656462107,-20064656461155⟩,⟨-3577126189771,-3577126189525⟩,⟨146410008856858,146410008909709⟩,⟨27770675142234,27770675151559⟩,⟨8317890666270,8317890670187⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨664617072516,664618231392⟩,⟨-5027233813774,-5027214019844⟩,⟨5838059428792,5838082405168⟩,⟨66035489649778,66036029973690⟩,⟨-35922972991008,-35922221110400⟩,⟨-11479954788778,-11478911785974⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5026565920004,5026567175392⟩,⟨-25091890275881,-25091870480999⟩,⟨2260933239021,2260956215643⟩,⟨212445498506636,212446038883399⟩,⟨-8152297848774,-8151545958841⟩,⟨-3162064122508,-3161021115787⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461007141428,461007256575⟩,⟨1698373218039,1698376032482⟩,⟨207359534535,207361641821⟩,⟨-30500270396724,-30500186823582⟩,⟨1051350704622,1051437946147⟩,⟨-290005973335,-289910314870⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨224626789580,224626789582⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-224626789582,-224626789580⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨874884838194,874884838196⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1901630199306,1901630245348⟩,⟨-14319006630082,-14319006514022⟩,⟨0,0⟩,⟨130715559209607,130715559237972⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨802118571530,802118617572⟩,⟨-14319006630082,-14319006514022⟩,⟨0,0⟩,⟨130715559209607,130715559237972⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32473373077,32473374945⟩,⟨-661319727126,-661319717687⟩,⟨319124126993,319124145312⟩,⟨8206096230957,8206096256229⟩,⟨-6498957778804,-6498957686573⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨493480514505,493480631520⟩,⟨1037053490913,1037056314795⟩,⟨526483661528,526485787133⟩,⟨-22294174165767,-22294090567353⟩,⟨-5447607074182,-5447519740426⟩,⟨-290005973335,-289910314870⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505853361827,505853374074⟩,⟨2537541677330,2537541800300⟩,⟨0,0⟩,⟨3442964323895,3442967248197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227036050326,227036109659⟩,⟨1616012348020,1616013984008⟩,⟨242219839611,242220823405⟩,⟨-3924846631294,-3924792976534⟩,⟨-1291224348774,-1291179143844⟩,⟨-133423327601,-133379314688⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-664618231392,-664617072516⟩,⟨5027214019844,5027233813774⟩,⟨-5838082405168,-5838059428792⟩,⟨-66036029973690,-66035489649778⟩,⟨35922221110400,35922972991008⟩,⟨11478911785974,11479954788778⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3697330616096,3697331871484⟩,⟨-15037442442263,-15037422647381⟩,⟨-9415208594939,-9415185618317⟩,⟨80373978883168,80374519259931⟩,⟨63692896252634,63693648142567⟩,⟨19796802452244,19797845458965⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨452142072474,452142226008⟩,⟨534791704387,534794931128⟩,⟨-100008576673,-100005409857⟩,⟨-15445673483938,-15445579958800⟩,⟨-7816914559677,-7816800437095⟩,⟨-4104125179790,-4103984166997⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨313653156902,313653156908⟩,⟨1975255459430,1975255459432⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-313653156908,-313653156902⟩,⟨-1975255459432,-1975255459430⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨785858470868,785858470874⟩,⟨-1975255459432,-1975255459430⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1409509181755,1409509209395⟩,⟨-9315131775519,-9315131705636⟩,⟨-4125880284136,-4125880253175⟩,⟨59321681994846,59321682010996⟩,⟨36645301273345,36645301358372⟩,⟨11637741204035,11637741207287⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1409509209395,-1409509181755⟩,⟨9315131705636,9315131775519⟩,⟨4125880253175,4125880284136⟩,⟨-59321682010996,-59321681994846⟩,⟨-36645301358372,-36645301273345⟩,⟨-11637741207287,-11637741204035⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-309997581619,-309997553979⟩,⟨9315131705636,9315131775519⟩,⟨4125880253175,4125880284136⟩,⟨-59321682010996,-59321681994846⟩,⟨-36645301358372,-36645301273345⟩,⟨-11637741207287,-11637741204035⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12550098551,-12550097430⟩,⟨408663166270,408663171947⟩,⟨43701196273,43701208540⟩,⟨-4297383779529,-4297383764418⟩,⟨2112629830472,2112629892657⟩,⟨2811827622201,2811827647020⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439591973923,439592128578⟩,⟨943454870657,943458103075⟩,⟨-56307380400,-56304201317⟩,⟨-19743057263467,-19742963723218⟩,⟨-5704284729205,-5704170544438⟩,⟨-1292297557589,-1292156519977⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100840757003,-100840757001⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4082488100,4082488101⟩,⟨25157944497,25157944503⟩,⟨40119652736,40119652738⟩,⟨-267079101977,-267079101966⟩,⟨247233542879,247233542884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8873605211,8873605429⟩,⟨10169564187,10169565539⟩,⟨87203183662,87203185778⟩,⟨-742941563195,-742941548746⟩,⟨99938903425,99938916483⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1486846218229,1486846239497⟩,⟨-7609548213917,-7609547825609⟩,⟨-1434752328010,-1434752258320⟩,⟨113078561132573,113078568976561⟩,⟨24167828632385,24167830228843⟩,⟨5371449260926,5371449565033⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11999587832,11999588299⟩,⟨-47660751345,-47660744675⟩,⟨106343848345,106343853742⟩,⟨-232827877564,-232827732029⟩,⟨-286598245763,-286598160641⟩,⟨-184232546833,-184232526736⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-11999588299,-11999587832⟩,⟨47660744675,47660751345⟩,⟨-106343853742,-106343848345⟩,⟨232827732029,232827877564⟩,⟨286598160641,286598245763⟩,⟨184232526736,184232546833⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112840345302,-112840344833⟩,⟨-827224093521,-827224086849⟩,⟨-106343853742,-106343848345⟩,⟨2431850987581,2431851133116⟩,⟨286598160641,286598245763⟩,⟨184232526736,184232546833⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨79838473979,79838475552⟩,⟨-527634665707,-527634661719⟩,⟨639774882814,639774898220⟩,⟨3360143109211,3360143110282⟩,⟨-3696917989106,-3696917949716⟩,⟨-2509584803969,-2509584803576⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨107963872419,107963876091⟩,⟨-1266058777741,-1266058723058⟩,⟨760972785761,760972826085⟩,⟨20058140053881,20058141279559⟩,⟨-6983645074822,-6983644428327⟩,⟨-4673307071863,-4673306871710⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-107963876091,-107963872419⟩,⟨1266058723058,1266058777741⟩,⟨-760972826085,-760972785761⟩,⟨-20058141279559,-20058140053881⟩,⟨6983644428327,6983645074822⟩,⟨4673306871710,4673307071863⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨991547751685,991547755357⟩,⟨1266058723058,1266058777741⟩,⟨-760972826085,-760972785761⟩,⟨-20058141279559,-20058140053881⟩,⟨6983644428327,6983645074822⟩,⟨4673306871710,4673307071863⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121255170812,121255171265⟩,⟨791402739655,791402748714⟩,⟨188896176437,188896182421⟩,⟨-2427294221301,-2427293995177⟩,⟨-691898437003,-691898311206⟩,⟨-175180516529,-175180467927⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11580544580,11580544677⟩,⟨169792203840,169792205916⟩,⟨21827648230,21827649430⟩,⟨745583326130,745583378160⟩,⟨101191013206,101191040336⟩,⟨-17243746917,-17243740544⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171381314246,171381463440⟩,⟨1670166648329,1670171996486⟩,⟨117567714138,117570632397⟩,⟨-1701926459767,-1701718753783⟩,⟨397133993821,397282348692⟩,⟨-598317048697,-598190860401⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171381463440,-171381314246⟩,⟨-1670171996486,-1670166648329⟩,⟨-117570632397,-117567714138⟩,⟨1701718753783,1701926459767⟩,⟨-397282348692,-397133993821⟩,⟨598190860401,598317048697⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨55654586886,55654795413⟩,⟨-54159648466,-54152664321⟩,⟨124649207214,124653109267⟩,⟨-2223127877511,-2222866516767⟩,⟨-1688506697466,-1688313137665⟩,⟨464767532800,464937734009⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29184878064721,29184903798806⟩,⟨-263008420267336,-263007779008201⟩,⟨-87926611066537,-87926118523850⟩,⟨3841498947404510,3841521765217192⟩,⟨1410596448034627,1410617010572127⟩,⟨323490364362245,323511836137811⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13372133661,13372133762⟩,⟨174553268840,174553271492⟩,⟨41663294066,41663295544⟩,⟨603897787765,603897865726⟩,⟨119319680498,119319720544⟩,⟨26266610690,26266625669⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354943122475,354943438132⟩,⟨1434575179287,1434587158184⟩,⟨36535996213,36543008900⟩,⟨-20758525072282,-20758026132919⟩,⟨-3602199818600,-3601842695856⟩,⟨-2032066318532,-2031766575407⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354943438132,-354943122475⟩,⟨-1434587158184,-1434575179287⟩,⟨-36543008900,-36535996213⟩,⟨20758026132919,20758525072282⟩,⟨3601842695856,3602199818600⟩,⟨2031766575407,2032066318532⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84648535791,84649006103⟩,⟨-491132287527,-491117076212⟩,⟨-92850389300,-92840197530⟩,⟨1014968869452,1015561349064⟩,⟨-2102442033349,-2101970725838⟩,⟨739469017818,739909798555⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235298699152,235298699158⟩,⟨1580776070131,1580776070141⟩,⟨312655020537,312655020542⟩,⟨-3973281040305,-3973281040301⟩,⟨-1571716941748,-1571716941736⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1669933846142,-1669932399453⟩,⟨-4031926819339,-4031885497083⟩,⟨428188376448,428215353353⟩,⟨39707783485881,39709288722731⟩,⟨-7451713961180,-7450496859413⟩,⟨2295200998135,2296381791877⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-184161867324,-184161707093⟩,⟨-1646623980392,-1646618366619⟩,⟨-239673748827,-239670515980⟩,⟨2261399476821,2261628581300⟩,⟨-155415887401,-155254017792⟩,⟨666305661461,666445459689⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51136831828,51136992065⟩,⟨-65847910261,-65842296478⟩,⟨72981271710,72984504562⟩,⟨-1711881563484,-1711652459001⟩,⟨-1727132829149,-1726970959528⟩,⟨318231361576,318371159807⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4284701653,4284741514⟩,⟨-29029640608,-29028216643⟩,⟨4896540720,4897427941⟩,⟨-71401969581,-71342976939⟩,⟨-287523123574,-287478685282⟩,⟨52158206371,52196930036⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2378306425,2378321331⟩,⟨-6125017654,-6124476280⟩,⟨6788524874,6788846860⟩,⟨-151349497034,-151326342634⟩,⟨-169395670832,-169378978276⟩,⟨39289461053,39303415869⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4265710515,4265737335⟩,⟨-28455154795,-28454074085⟩,⟨4438264774,4438891022⟩,⟨-89775575501,-89725512728⟩,⟨-273697680745,-273663232284⟩,⟨44287960426,44315198913⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4265737335,-4265710515⟩,⟨28454074085,28455154795⟩,⟨-4438891022,-4438264774⟩,⟨89725512728,89775575501⟩,⟨273663232284,273697680745⟩,⟨-44315198913,-44287960426⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨18964318,19030999⟩,⟨-575566523,-573061848⟩,⟨457649698,459163167⟩,⟨18323543147,18432598562⟩,⟨-13859891290,-13781004537⟩,⟨7843007458,7908969610⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨55654586886,55654795413⟩,⟨-54159648466,-54152664321⟩,⟨124649207214,124653109267⟩,⟨-2223127877511,-2222866516767⟩,⟨-1688506697466,-1688313137665⟩,⟨464767532800,464937734009⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨18964318,19030999⟩,⟨-575566523,-573061848⟩,⟨457649698,459163167⟩,⟨18323543147,18432598562⟩,⟨-13859891290,-13781004537⟩,⟨7843007458,7908969610⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112098646425,112528143156⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112528143156,-112098646425⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437227670732,437657167463⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨43722767072,45304355226⟩,⟨-113816633344,-109951162777⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨155821413497,157832498382⟩,⟨985694994432,989560464999⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨43293270341,45733851957⟩,⟨-113816633344,-109951162777⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2510451325440,-2506246629056⟩,⟨10743319721704,10784481866367⟩,⟨0,0⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-256929002840,-255519675851⟩,⟨-1415136306945,-1402522313037⟩,⟨0,0⟩,⟨10660837723011,10866649048270⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨255519675851,256929002840⟩,⟨1402522313037,1415136306945⟩,⟨0,0⟩,⟨-10866649048270,-10660837723011⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986983484620,987412981351⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-118712158400,-118233797824⟩,⟨-1224869350352,-1224336566813⟩,⟨0,0⟩,⟨-1364519380724,-1363332584183⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106609082876,-106133307577⟩,⟨-981756294544,-980321212902⟩,⟨0,0⟩,⟨1223270767889,1225934685685⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106133307577,106609082876⟩,⟨980321212902,981756294544⟩,⟨0,0⟩,⟨-1225934685685,-1223270767889⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨361652983428,363538085716⟩,⟨2382843525939,2396892601489⟩,⟨0,0⟩,⟨-12092583733955,-11884108490900⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2148347702336,-2134247781376⟩,⟨6866666364207,6982565574499⟩,⟨3045867694444,3088209340461⟩,⟨-44343525589447,-42883681960431⟩,⟨-27370408179856,-26681592212641⟩,⟨-8673884558907,-8437664302675⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308390631520,-302462927763⟩,⟨-960377558314,-910987714851⟩,⟨-423486527014,-405391247553⟩,⟨5946301731835,6491196231350⟩,⟨3666430918789,3925842618830⟩,⟨1177299422297,1262728916756⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨302462927763,308390631520⟩,⟨910987714851,960377558314⟩,⟨405391247553,423486527014⟩,⟨-6491196231350,-5946301731835⟩,⟨-3925842618830,-3666430918789⟩,⟨-1262728916756,-1177299422297⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157832498382,-155821413497⟩,⟨-989560464999,-985694994432⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941679129394,943690214279⟩,⟨-989560464999,-985694994432⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-170376798912,-168031144832⟩,⟨-1155418235036,-1148452205416⟩,⟨-511011797528,-509422372597⟩,⟨-1214167512311,-1199571186702⟩,⟨744067061725,751700667225⟩,⟨-237499131993,-236024019343⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146231211942,-143910640123⟩,⟨-841036511187,-830255274732⟩,⟨-371773209412,-368477948638⟩,⟨1017041705001,1052377466406⟩,⟨1380259452007,1396960679012⟩,⟨201308928823,204670012538⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨143910640123,146231211942⟩,⟨830255274732,841036511187⟩,⟨368477948638,371773209412⟩,⟨-1052377466406,-1017041705001⟩,⟨-1396960679012,-1380259452007⟩,⟨-204670012538,-201308928823⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨446373567886,454621843462⟩,⟨1741242989583,1801414069501⟩,⟨773869196191,795259736426⟩,⟨-7543573697756,-6963343436836⟩,⟨-5322803297842,-5046690370796⟩,⟨-1467398929294,-1378608351120⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨808026551314,818159929178⟩,⟨4124086515522,4198306670990⟩,⟨773869196191,795259736426⟩,⟨-19636157431711,-18847451927736⟩,⟨-5322803297842,-5046690370796⟩,⟨-1467398929294,-1378608351120⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨86586540682,91467703914⟩,⟨-227633266688,-219902325554⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13216969136464,13962052417068⟩,⟨31775611778955,36705792566987⟩,⟨-141144160852114,-126357706215211⟩,⟨152786844472730,192996726802656⟩,⟨-424370918481071,-252974628786231⟩,⟨2416025906562905,2853688490424798⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9713095996776,10389332434650⟩,⟨72926434034709,80625055898343⟩,⟨-95724582356468,-82761219764380⟩,⟨101304532849280,197360664513768⟩,⟨-899942137212519,-693973234913290⟩,⟨1552719044487374,1929023597869123⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨80345132032,85891433728⟩,⟨-707083253383,-559326781738⟩,⟨634757030372,839506383806⟩,⟨6014685423752,10828151983474⟩,⟨-8455955692320,-897588766580⟩,⟨-6942051132496,4450056787109⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1179856759808,1185403061504⟩,⟨-707083253383,-559326781738⟩,⟨634757030372,839506383806⟩,⟨6014685423752,10828151983474⟩,⟨-8455955692320,-897588766580⟩,⟨-6942051132496,4450056787109⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨77545184704,82701687488⟩,⟨-658932749623,-518799318323⟩,⟨588764073901,782338214292⟩,⟨5183980232175,9845990421512⟩,⟨-7602321901946,-363699618415⟩,⟨-7025974803370,3831749567932⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨83211680579,89162161694⟩,⟨-763591630838,-596157389105⟩,⟨676554576498,906597696442⟩,⟨6514820341120,12277100045447⟩,⟨-9838453444718,-1052594752157⟩,⟨-7417190422506,5660468309400⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-85891433728,-80345132032⟩,⟨559326781738,707083253383⟩,⟨-839506383806,-634757030372⟩,⟨-10828151983474,-6014685423752⟩,⟨897588766580,8455955692320⟩,⟨-4450056787109,6942051132496⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1013620194048,1019166495744⟩,⟨559326781738,707083253383⟩,⟨-839506383806,-634757030372⟩,⟨-10828151983474,-6014685423752⟩,⟨897588766580,8455955692320⟩,⟨-4450056787109,6942051132496⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-89431893824,-83432013504⟩,⟨603420837336,766999575843⟩,⟨-910643884177,-684797566070⟩,⟨-12280745432745,-6820010297469⟩,⟨1344171840723,9807739335051⟩,⟨-5581361311716,7103796314993⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-82896794845,-76914487833⟩,⟨498770306686,668509992778⟩,⟨-795933992030,-563019053535⟩,⟨-10313022450972,-4420010474652⟩,⟨-619870197828,8326224318478⟩,⟨-4947484822384,8337256905368⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨314885734,12247673861⟩,⟨-264821324152,72352603673⟩,⟨-119379415532,343578642907⟩,⟨-3798202109852,7857089570795⟩,⟨-10458323642546,7273629566321⟩,⟨-12364675244890,13997725214768⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨157442867,6123836931⟩,⟨-132410662076,36176301837⟩,⟨-59689707766,171789321454⟩,⟨-1899101054926,3928544785398⟩,⟨-5229161821273,3636814783161⟩,⟨-6182337622445,6998862607384⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6123836931,-157442867⟩,⟨-36176301837,132410662076⟩,⟨-171789321454,59689707766⟩,⟨-3928544785398,1899101054926⟩,⟨-3636814783161,5229161821273⟩,⟨-6998862607384,6182337622445⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755999546685,761965960013⟩,⟨-36176301837,132410662076⟩,⟨-171789321454,59689707766⟩,⟨-3928544785398,1899101054926⟩,⟨-3636814783161,5229161821273⟩,⟨-6998862607384,6182337622445⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨5871097747,6709650177⟩,⟨-110471581864,-81743899732⟩,⟨92767800038,131160790132⟩,⟨1448092267802,2601177085492⟩,⟨-2400875133484,-776987680990⟩,⟨-351694756640,1977228250448⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6709650177,-5871097747⟩,⟨81743899732,110471581864⟩,⟨-131160790132,-92767800038⟩,⟨-2601177085492,-1448092267802⟩,⟨776987680990,2400875133484⟩,⟨-1977228250448,351694756640⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092801977599,1093640530029⟩,⟨81743899732,110471581864⟩,⟨-131160790132,-92767800038⟩,⟨-2601177085492,-1448092267802⟩,⟨776987680990,2400875133484⟩,⟨-1977228250448,351694756640⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6730206336,-5886828800⟩,⟨82182733528,111149861813⟩,⟨-131966098905,-93265814519⟩,⟨-2628384109236,-1462008932337⟩,⟨788129991171,2428956649251⟩,⟨-2005207050187,345942862176⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3365103168,-2943414400⟩,⟨41091366764,55574930907⟩,⟨-65983049453,-46632907259⟩,⟨-1314192054618,-731004466168⟩,⟨394064995585,1214478324626⟩,⟨-1002603525094,172971431088⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨2943414400,3365103168⟩,⟨-55574930907,-41091366764⟩,⟨46632907259,65983049453⟩,⟨731004466168,1314192054618⟩,⟨-1214478324626,-394064995585⟩,⟨-172971431088,1002603525094⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765066798016,765488506048⟩,⟨-55574930907,-41091366764⟩,⟨46632907259,65983049453⟩,⟨731004466168,1314192054618⟩,⟨-1214478324626,-394064995585⟩,⟨-172971431088,1002603525094⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273200494399,273410132508⟩,⟨20435974933,27617895466⟩,⟨-32790197533,-23191950009⟩,⟨-650294271373,-362023066950⟩,⟨194246920247,600218783371⟩,⟨-494307062612,87923689160⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530133596032,1530977012096⟩,⟨-111149861814,-82182733528⟩,⟨93265814518,131966098906⟩,⟨1462008932336,2628384109236⟩,⟨-2428956649252,-788129991170⟩,⟨-345942862176,2005207050188⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1186190700600,1192681269290⟩,⟨-831993045415,-650991010658⟩,⟨738783005241,987809383925⟩,⟨7714929173379,13901765999890⟩,⟨-11327898735077,-1855588559106⟩,⟨-7248141869108,6872439978753⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1272869773424,1285850910804⟩,⟨-1663986090829,-1301982021316⟩,⟨1477566010481,1975618767850⟩,⟨15429858346762,27803531999767⟩,⟨-22655797470144,-3711177118213⟩,⟨-14491641654829,13744879957500⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨160977198208,172133581248⟩,⟨-1437359966845,-1113305095920⟩,⟨1263444304219,1706549917878⟩,⟨11314818649418,22889566068546⟩,⟨-18290903097392,-942447627883⟩,⟨-15166689440013,10421081174356⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨55243511628,59523107446⟩,⟨-492837538700,-374236926141⟩,⟨423024899734,586444113882⟩,⟨3658370029624,7698835404930⟩,⟨-6210118464835,2903519807⟩,⟨-5619936440332,3658007167833⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380199030525,380700501177⟩,⟨800603962,18035279619⟩,⟨-22483411167,540318727⟩,⟨-547791812979,146723524947⟩,⟨-330206298749,646553333520⟩,⟨-782175832198,617116747896⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175529887344,3179718312131⟩,⟨-150834442660,-6678062680⟩,⟨-4518847269,188035498429⟩,⟨-1227064676016,4595657014832⟩,⟨-5425158546829,2762042845853⟩,⟨-5161666560540,6563809940155⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨159550311088,172137074279⟩,⟨-1433420658439,-1081179528719⟩,⟨1221505259640,1706138887247⟩,⟨10503957146993,22648554892259⟩,⟨-18417701195666,157378798537⟩,⟨-16536754036120,11134648379356⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨320527509296,344270655527⟩,⟨-2870780625284,-2194484624639⟩,⟨2484949563859,3412688805125⟩,⟨21818775796411,45538120960805⟩,⟨-36708604293058,-785068829346⟩,⟨-31703443476133,21555729553712⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519808340493,528045460868⟩,⟨-50140644016,183522237868⟩,⟨-238101375076,82730412908⟩,⟨-5453707721131,2664060851949⟩,⟨-5082030484906,7262036635320⟩,⟨-9719131630900,8622450682337⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357408561990,365937618445⟩,⟨-52121500567,190772468379⟩,⟨-247507809273,85998761043⟩,⟨-5678219343146,2802458746752⟩,⟨-5325811886855,7563875131241⟩,⟨-10122484580002,9018891231100⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714817123980,731875236890⟩,⟨-104243001134,381544936758⟩,⟨-495015618546,171997522086⟩,⟨-11356438686292,5604917493504⟩,⟨-10651623773710,15127750262482⟩,⟨-20244969160004,18037782462200⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523423945855,1525105914349⟩,⟨-29405962082,28288848336⟩,⟨-37894975614,39198298868⟩,⟨-1139168153156,1180291841434⟩,⟨-1651968968262,1612745142314⟩,⟨-2323171112624,2356901806828⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨990412012086,1015166392196⟩,⟨-164166624950,548061823081⟩,⟨-711848444367,264665416087⟩,⟨-16530921275482,8579723838493⟩,⟨-15900106202499,22083679097844⟩,⟨-29662988845707,26622732541572⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67883329520,67987548899⟩,⟨10155633308,13735211650⟩,⟨-16307553330,-11525211826⟩,⟨-322651274173,-178519499465⟩,⟨94883504786,297644777650⟩,⟨-244855424068,45682872149⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49887178323,50590359199⟩,⟨262082490061,269819956774⟩,⟨35643671228,40704510915⟩,⟨-1378092871565,-1189934686336⟩,⟨-314522309503,-123393897506⟩,⟨-296525498927,-67345028909⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2129407968555,2131756092755⟩,⟨-309533576610,-228738939012⟩,⟨259586442834,367503278178⟩,⟨4081490236341,7342077773467⟩,⟨-6790914643792,-2207541942172⟩,⟨-947569892257,5615840472441⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2963387189396,2968290185348⟩,⟨-646499015960,-477486267258⟩,⟨541879586201,767575880802⟩,⟨8545644582828,15381770353723⟩,⟨-14239388496212,-4637287402818⟩,⟨-1946093511408,11795537794835⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134455172117,136575969631⟩,⟨676614287087,706753314210⟩,⟨120652514166,145205139936⟩,⟨-3649927860405,-2726982982657⟩,⟨-1399046175862,-370088993135⟩,⟨-854923330114,418057151987⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8851672976445,8991292789858⟩,⟨-47262041899998,-43852285410569⟩,⟨-9710165159143,-7819652330264⟩,⟨611238766678827,740936759698524⟩,⟨101465021630615,195638562615641⟩,⟨-14140427243205,78143500097290⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7973361100928,8301556829482⟩,⟨-44978975670062,-35019225751771⟩,⟨-14786447643514,-4879433027637⟩,⟨368289712973730,768372598113727⟩,⟨-54843197022912,393269160192104⟩,⟨-260300470515063,302430426146070⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15946722201856,16603113658964⟩,⟨-89957951340124,-70038451503542⟩,⟨-29572895287028,-9758866055274⟩,⟨736579425947460,1536745196227454⟩,⟨-109686394045824,786538320384208⟩,⟨-520600941030126,604860852292140⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10743319721704,10784481866367⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239228,2075048233589864⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9643808093928,9684970238591⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239235,2075048233589852⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2387534470720,2392217527616⟩,⟨-12060075023605,-11917323006543⟩,⟨0,0⟩,⟨100606314842521,107411991083576⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7659549408441,7758406193883⟩,⟨-49270583988244,-47835392513597⟩,⟨-21791113317734,-21218487833879⟩,⟨597482868746368,625796171501434⟩,⟨318386128635075,331518660490571⟩,⟨117558932503347,122409837216487⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6560037780665,6658894566107⟩,⟨-49270583988244,-47835392513596⟩,⟨-21791113317735,-21218487833878⟩,⟨597482868746368,625796171501429⟩,⟨318386128635075,331518660490569⟩,⟨117558932503347,122409837216487⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1963870982528,1980316556736⟩,⟨-8258120122771,-7898543784657⟩,⟨-3652354342496,-3503580641728⟩,⟨36631519744398,48147500494265⟩,⟨25139878418907,30396403481544⟩,⟨7278862485519,9352690792625⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100626050579,101055547311⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133453589117,135464674003⟩,⟨702151377221,709629730362⟩,⟨311639858542,313669581803⟩,⟨-1781208837000,-1767320322048⟩,⟨-1575651702216,-1567782181268⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4351405453248,4372534084352⟩,⟨-20318195146376,-19815866791200⟩,⟨-3652354342496,-3503580641728⟩,⟨137237834586919,155559491577841⟩,⟨25139878418907,30396403481544⟩,⟨7278862485519,9352690792625⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨641055018592,688541311054⟩,⟨-5741561250568,-4388969249278⟩,⟨4969899127718,6825377610250⟩,⟨43637551592822,91076241921610⟩,⟨-73417208586116,-1570137658692⟩,⟨-63406886952266,43111459107424⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4992460471840,5061075395406⟩,⟨-26059756396944,-24204836040478⟩,⟨1317544785222,3321796968522⟩,⟨180875386179741,246635733499451⟩,⟨-48277330167209,28826265822852⟩,⟨-56128024466747,52464149900049⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨456904290288,465160832451⟩,⟨1575427432874,1813891492999⟩,⟨120580196560,305304648201⟩,⟨-35060660058872,-25817575055475⟩,⟨-3389284709290,5293869047748⟩,⟨-5158697815180,4821952991148⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨224197292850,225056286312⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-225056286312,-224197292850⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨874455341464,875314334926⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1898836008741,1904429422379⟩,⟨-14385385406069,-14253064895063⟩,⟨0,0⟩,⟨127682751799218,133750314871228⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨799324380965,804917794603⟩,⟨-14385385406069,-14253064895063⟩,⟨0,0⟩,⟨127682751799218,133750314871228⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨31473397498,33480311009⟩,⟨-681677302061,-641146868304⟩,⟨317856335867,320395012775⟩,⟨7878121330779,8541528015552⟩,⟨-6530975501168,-6467144718132⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨488377687786,498641143460⟩,⟨893750130813,1172744624695⟩,⟨438436532427,625699660976⟩,⟨-27182538728093,-17276047039923⟩,⟨-9920260210458,-1173275670384⟩,⟨-5158697815180,4821952991148⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505357813684,506349053570⟩,⟨2517543755956,2557704464203⟩,⟨0,0⟩,⟨2303354216540,4586136051397⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨224468276930,229635107701⟩,⟨1529020492417,1700022775783⟩,⟨201514310416,288148322538⟩,⟨-7402228065757,-404434933952⟩,⟨-3564610973754,916252964540⟩,⟨-2375692707911,2220614381647⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-688541311054,-641055018592⟩,⟨4388969249278,5741561250568⟩,⟨-6825377610250,-4969899127718⟩,⟨-91076241921610,-43637551592822⟩,⟨1570137658692,73417208586116⟩,⟨-43111459107424,63406886952266⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3662864142194,3731479065760⟩,⟨-15929225897098,-14074305540632⟩,⟨-10477731952746,-8473479769446⟩,⟨46161592665309,111921939985019⟩,⟨26710016077599,103813612067660⟩,⟨-35832596621905,72759577744891⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨444581352188,459734651661⟩,⟨376565102436,700039795048⟩,⟨-252719546678,36047995784⟩,⟨-21003704953670,-10074082783024⟩,⟨-13412125151119,-1832882932328⟩,⟨-11575366566998,3002521241811⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨311642826994,315664996764⟩,⟨1971389988864,1979120929998⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-315664996764,-311642826994⟩,⟨-1979120929998,-1971389988864⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨783846631012,787868800782⟩,⟨-1979120929998,-1971389988864⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1400052181813,1419020582693⟩,⟨-9482029002629,-9152065585912⟩,⟨-4193657792400,-4059609048557⟩,⟨54438454415366,64229925765081⟩,⟨34413692054617,38890031616314⟩,⟨10762015744777,12517020425824⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1419020582693,-1400052181813⟩,⟨9152065585912,9482029002629⟩,⟨4059609048557,4193657792400⟩,⟨-64229925765081,-54438454415366⟩,⟨-38890031616314,-34413692054617⟩,⟨-12517020425824,-10762015744777⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-319508954917,-300540554037⟩,⟨9152065585912,9482029002629⟩,⟨4059609048557,4193657792400⟩,⟨-64229925765081,-54438454415366⟩,⟨-38890031616314,-34413692054617⟩,⟨-12517020425824,-10762015744777⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13289877864,-11833784314⟩,⟨390416637825,427476283432⟩,⟨32667565237,54922091508⟩,⟨-4634700556243,-3973927259644⟩,⟨1888188482939,2332800938660⟩,⟨2708016161403,2914790388250⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨431291474324,447900867347⟩,⟨766981740261,1127516078480⟩,⟨-220051981441,90970087292⟩,⟨-25638405509913,-14048010042668⟩,⟨-11523936668180,499918006332⟩,⟨-8867350405595,5917311630061⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101055547311,-100626050579⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨3962150741,4203374775⟩,⟨23970850928,26345828650⟩,⟨40014577925,40224844809⟩,⟨-272685124817,-261477608973⟩,⟨246677084567,247790085082⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8603612034,9145321030⟩,⟨5946474397,14376130727⟩,⟨86889653291,87517563587⟩,⟨-808695486160,-676782926704⟩,⟨94437742819,105411467849⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1477615532734,1496146157139⟩,⟨-7773606426771,-7448194511054⟩,⟨-1472507056417,-1397625456607⟩,⟨109126934273781,117137894499723⟩,⟨23204417623497,25157297198084⟩,⟨5133729410029,5615526381923⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11562252238,12444376730⟩,⟨-56666543424,-38719538846⟩,⟨104521815579,108152052459⟩,⟨-449790244044,-15772739730⟩,⟨-329520449963,-243471241481⟩,⟨-194242460342,-174188781961⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12444376730,-11562252238⟩,⟨38719538846,56666543424⟩,⟨-108152052459,-104521815579⟩,⟨15772739730,449790244044⟩,⟨243471241481,329520449963⟩,⟨174188781961,194242460342⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113499924041,-112188302817⟩,⟨-836594796080,-817788798040⟩,⟨-108152052459,-104521815579⟩,⟨2214795995282,2648813499596⟩,⟨243471241481,329520449963⟩,⟨174188781961,194242460342⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨77327419932,82370665254⟩,⟨-548487702492,-507392259752⟩,⟨629027001663,650305329162⟩,⟨3022074846768,3712369580129⟩,⟨-3927194688132,-3462371378180⟩,⟨-2621011254502,-2397419148382⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨103919043611,112084812173⟩,⟨-1328712552203,-1205699253559⟩,⟨735025134724,786601093390⟩,⟨18610336606089,21582699296941⟩,⟨-7664669140067,-6294880105183⟩,⟨-4947283958581,-4400314927921⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-112084812173,-103919043611⟩,⟨1205699253559,1328712552203⟩,⟨-786601093390,-735025134724⟩,⟨-21582699296941,-18610336606089⟩,⟨6294880105183,7664669140067⟩,⟨4400314927921,4947283958581⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨987426815603,995592584165⟩,⟨1205699253559,1328712552203⟩,⟨-786601093390,-735025134724⟩,⟨-21582699296941,-18610336606089⟩,⟨6294880105183,7664669140067⟩,⟨4400314927921,4947283958581⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119849257801,122661390246⟩,⟨776915832159,806263151189⟩,⟨182958403864,194809551615⟩,⟨-2732017356294,-2130880450031⟩,⟨-828626419969,-553973641635⟩,⟨-230200723774,-119420815049⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11447096120,11716322440⟩,⟨166885615388,172719311756⟩,⟨21329697296,22328549202⟩,⟨669639825348,821122101174⟩,⟨87450141818,114896136270⟩,⟨-20230244561,-14270112598⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166022493288,176921669788⟩,⟨1461832820619,1878962828166⟩,⟨-5772398471,235570735171⟩,⟨-10881826825366,7513668279736⟩,⟨-6372846387473,7276373112955⟩,⟨-7054089321534,5859761529407⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176921669788,-166022493288⟩,⟨-1878962828166,-1461832820619⟩,⟨-235570735171,5772398471⟩,⟨-7513668279736,10881826825366⟩,⟨-7276373112955,6372846387473⟩,⟨-5859761529407,7054089321534⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47546607142,63612614413⟩,⟨-349942335749,238189955164⟩,⟨-34056424755,293920721009⟩,⟨-14915896345493,10477391891414⟩,⟨-10840984086709,7289099352013⟩,⟨-8235454237318,9274703703181⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28482922970088,29903659080643⟩,⟨-286723413825388,-239654005874510⟩,⟨-108415541434438,-68244645329984⟩,⟨2853178722727234,4846158403784387⟩,⟨460341715413713,2396559135440411⟩,⟨-769886097786431,1427107357454757⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13063840556,13684090534⟩,⟨169371170810,179893248114⟩,⟨39885760836,43465862172⟩,⟨488371666796,717911149998⟩,⟨73674185694,164935833120⟩,⟨9526114318,42997754192⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338419671834,372169213877⟩,⟨819124451055,2045148577200⟩,⟨-316053984341,371302265782⟩,⟨-47271430930017,6004921934327⟩,⟨-21694738601631,15106215196742⟩,⟨-17906685975721,13979367631512⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372169213877,-338419671834⟩,⟨-2045148577200,-819124451055⟩,⟨-371302265782,316053984341⟩,⟨-6004921934327,47271430930017⟩,⟨-15106215196742,21694738601631⟩,⟨-13979367631512,17906685975721⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59122260447,109481195513⟩,⟨-1278166836939,308391627425⟩,⟨-591354247223,407024071633⟩,⟨-31643327444240,33223420887349⟩,⟨-26630151864922,22194656607963⟩,⟨-22846718037107,23823997605782⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234079639696,236520221314⟩,⟨1576606718685,1584944065288⟩,⟨311639858542,313669581803⟩,⟨-3980232092552,-3966343577600⟩,⟨-1575651702216,-1567782181268⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1713899236290,-1627118489814⟩,⟨-5486602712792,-2574625012262⟩,⟨-637401353078,1536810497490⟩,⟨-22326643764531,101735771588717⟩,⟨-63744877401258,47648545888305⟩,⟨-58056586456353,62491322345471⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-191202400916,-177359600782⟩,⟨-1868873474042,-1430363238223⟩,⟨-374774097371,-99305625213⟩,⟨-7383926794258,11969786804465⟩,⟨-7731078190592,7305828568779⟩,⟨-6525927833557,7874936318099⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨42877238780,59160620532⟩,⟨-292266755357,154580827065⟩,⟨-63134238829,214363956590⟩,⟨-11364158886810,8003443226865⟩,⟨-9306729892808,5738046387511⟩,⟨-6874343969218,7527203686221⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2556646805,6334071328⟩,⟨-108793428292,41559286487⟩,⟨-37604084180,52814955096⟩,⟨-3869734386785,3779019088424⟩,⟨-3091383544699,2280523422194⟩,⟨-2457990716743,2519462250468⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1672067451,3183212377⟩,⟨-31451568444,16634835724⟩,⟨-6794035920,23068250252⟩,⟨-1305105849198,1016648682675⟩,⟨-1115483198450,677760804374⟩,⟨-764383294522,893607551612⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨2986530260,5733243756⟩,⟨-80555229862,17949189561⟩,⟨-22810637682,36219912324⟩,⟨-2544781903343,2442913317920⟩,⟨-2199368255172,1464211334242⟩,⟨-1518907986572,1681679244906⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5733243756,-2986530260⟩,⟨-17949189561,80555229862⟩,⟨-36219912324,22810637682⟩,⟨-2442913317920,2544781903343⟩,⟨-1464211334242,2199368255172⟩,⟨-1681679244906,1518907986572⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3176596951,3347541068⟩,⟨-126742617853,122114516349⟩,⟨-73823996504,75625592778⟩,⟨-6312647704705,6323800991767⟩,⟨-4555594878941,4479891677366⟩,⟨-4139669961649,4038370237040⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47546607142,63612614413⟩,⟨-349942335749,238189955164⟩,⟨-34056424755,293920721009⟩,⟨-14915896345493,10477391891414⟩,⟨-10840984086709,7289099352013⟩,⟨-8235454237318,9274703703181⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3176596951,3347541068⟩,⟨-126742617853,122114516349⟩,⟨-73823996504,75625592778⟩,⟨-6312647704705,6323800991767⟩,⟨-4555594878941,4479891677366⟩,⟨-4139669961649,4038370237040⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (523/5120) u, BivariateJet2.affineZ (521/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000034

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000035Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2508346996352,-2508346938496⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2508346996352,-2508346938496⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-118472952128,-118472952064⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-118472952128,-118472952064⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2130548223296,-2130548184192⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2130548223232,-2130548184192⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-170998099072,-170998099008⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-170998099072,-170998099008⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨82488679808,82488679872⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-89182839104,-89182839040⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨82488803520,82488803584⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-89182983744,-89182983680⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6694180224,-6694180160⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6694159296,-6694159232⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨171671518848,171671518912⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨171671787264,171671787328⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1959550085184,1959550123776⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1959550085184,1959550123776⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2506246686912,-2506246629056⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2137554519296,-2137554480128⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2123581081472,-2123581042496⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-172174794048,-172174793984⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-169823543104,-169823543040⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨79922478784,79922478848⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-86190566528,-86190566464⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨85077603008,85077603072⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-92216995392,-92216995328⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7139392320,-7139392256⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6268087744,-6268087680⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨166113045248,166113045312⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨177294598336,177294598400⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1951406248512,1951406287104⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1967730937088,1967730975680⟩



end LaneCBRB2Cell000035Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000035
open Set LaneCBRB2Cell000035Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112313394790,112313394791⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨115749368627,115749368628⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112313394791,-112313394790⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437442419097,437442419098⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46051067166,46051067168⟩,⟨-115749368628,-115749368627⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158364461956,158364461959⟩,⟨983762259148,983762259149⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46051067165,46051067169⟩,⟨-115749368628,-115749368627⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2508346996352,-2508346938496⟩,⟨10763861442032,10763861442129⟩,⟨0,0⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-256223726387,-256223720474⟩,⟨-1408835368586,-1408835310710⟩,⟨0,0⟩,⟨10763861441838,10763861442323⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256223720474,256223726387⟩,⟨1408835310710,1408835368586⟩,⟨0,0⟩,⟨-10763861442323,-10763861441838⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨987198232985,987198232986⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-118472952128,-118472952064⟩,⟨-1224602900635,-1224602900633⟩,⟨0,0⟩,⟨-1363925788832,-1363925788826⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106371125183,-106371125124⟩,⟨-981038675714,-981038675646⟩,⟨0,0⟩,⟨1224602900628,1224602900640⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106371125124,106371125183⟩,⟨981038675646,981038675714⟩,⟨0,0⟩,⟨-1224602900640,-1224602900628⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨362594845598,362594851570⟩,⟨2389873986356,2389874044300⟩,⟨0,0⟩,⟨-11988464342963,-11988464342466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2130548223296,-2130548184192⟩,⟨6830181655151,6830181655290⟩,⟨3037127271673,3037127271739⟩,⟨-42429184253934,-42429184252222⟩,⟨-26500497358743,-26500497357811⟩,⟨-8389308336281,-8389308335920⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-306866352785,-306866347146⟩,⟨-922495828942,-922495793913⟩,⟨-410199520533,-410199504954⟩,⟨6111144953311,6111144953937⟩,⟨3748434999937,3748435039374⟩,⟨1208325830492,1208325830627⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306866347146,306866352785⟩,⟨922495793913,922495828942⟩,⟨410199504954,410199520533⟩,⟨-6111144953937,-6111144953311⟩,⟨-3748435039374,-3748434999937⟩,⟨-1208325830627,-1208325830492⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158364461959,-158364461956⟩,⟨-983762259149,-983762259148⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941147165817,941147165820⟩,⟨-983762259149,-983762259148⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-170998099072,-170998099008⟩,⟨-1149297455477,-1149297455470⟩,⟨-511049752632,-511049752628⟩,⟨-1201337582793,-1201337582780⟩,⟨750333620577,750333620589⟩,⟨-237534413523,-237534413519⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146368962581,-146368962524⟩,⟨-830765717835,-830765717767⟩,⟨-369410558226,-369410558193⟩,⟨1028306961609,1028306961641⟩,⟨1385763317129,1385763317217⟩,⟨203321942594,203321942604⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146368962524,146368962581⟩,⟨830765717767,830765717835⟩,⟨369410558193,369410558226⟩,⟨-1028306961641,-1028306961609⟩,⟨-1385763317217,-1385763317129⟩,⟨-203321942604,-203321942594⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨453235309670,453235315366⟩,⟨1753261511680,1753261546777⟩,⟨779610063147,779610078759⟩,⟨-7139451915578,-7139451914920⟩,⟨-5134198356591,-5134198317066⟩,⟨-1411647773231,-1411647773086⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨815830155268,815830166936⟩,⟨4143135498036,4143135591077⟩,⟨779610063147,779610078759⟩,⟨-19127916258541,-19127916257386⟩,⟨-5134198356591,-5134198317066⟩,⟨-1411647773231,-1411647773086⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92102134330,92102134338⟩,⟨-231498737256,-231498737254⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13125926215543,13125926216684⟩,⟨32992018762953,32992018768975⟩,⟨-124684122879403,-124684122857439⟩,⟨165850894509242,165850894555362⟩,⟨-313393573544773,-313393573319974⟩,⟨2368767009267529,2368767009896117⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9739348045025,9739348185165⟩,⟨73940440996194,73940442465795⟩,⟨-83207819095342,-83207817568713⟩,⟨143350327296149,143350334752990⟩,⟨-740264438304510,-740264423228506⟩,⟨1563941964134801,1563941993313661⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨85661808640,85661942016⟩,⟨-644658351016,-644656305551⟩,⟨725454751745,725457052471⟩,⟨8410475136372,8410525988829⟩,⟨-4417062630383,-4416989447152⟩,⟨-1401805903943,-1401703367810⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1185173436416,1185173569792⟩,⟨-644658351016,-644656305551⟩,⟨725454751745,725457052471⟩,⟨8410475136372,8410525988829⟩,⟨-4417062630383,-4416989447152⟩,⟨-1401805903943,-1401703367810⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨82488679808,82488803584⟩,⟨-598063820119,-598061855189⟩,⟨673020353557,673022563733⟩,⟨7477274682761,7477324875392⟩,⟨-3731728050066,-3731657290263⟩,⟨-1712450510824,-1712352533698⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨88915287154,88915430581⟩,⟨-693022710721,-693020294127⟩,⟨779880474451,779883192736⟩,⟨9392101686411,9392165987770⟩,⟨-5143049655629,-5142961846846⟩,⟨-1062919864000,-1062800462337⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-85661942016,-85661808640⟩,⟨644656305551,644658351016⟩,⟨-725457052471,-725454751745⟩,⟨-8410525988829,-8410475136372⟩,⟨4416989447152,4417062630383⟩,⟨1401703367810,1401805903943⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1013849685760,1013849819136⟩,⟨644656305551,644658351016⟩,⟨-725457052471,-725454751745⟩,⟨-8410525988829,-8410475136372⟩,⟨4416989447152,4417062630383⟩,⟨1401703367810,1401805903943⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-89182983744,-89182839040⟩,⟨699124357960,699126668224⟩,⟨-786752193987,-786749595367⟩,⟨-9565687203672,-9565627916713⟩,⟨5290442670315,5290525972531⟩,⟨957177414763,957292533199⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-82234830133,-82234685883⟩,⟨592367046360,592369512195⟩,⟨-666614555688,-666611781995⟩,⟨-7318440420542,-7318374050316⟩,⟨3597428139982,3597518085731⟩,⟨1807092533284,1807214022085⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6680457021,6680744698⟩,⟨-100655664361,-100650781932⟩,⟨113265918763,113271410741⟩,⟨2073661265869,2073791937454⟩,⟨-1545621515647,-1545443761115⟩,⟨744172669284,744413559748⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3340228510,3340372349⟩,⟨-50327832181,-50325390966⟩,⟨56632959381,56635705371⟩,⟨1036830632934,1036895968727⟩,⟨-772810757824,-772721880557⟩,⟨372086334642,372206779874⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3340372349,-3340228510⟩,⟨50325390966,50327832181⟩,⟨-56635705371,-56632959381⟩,⟨-1036895968727,-1036830632934⟩,⟨772721880557,772810757824⟩,⟨-372206779874,-372086334642⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758783011267,758783174370⟩,⟨50325390966,50327832181⟩,⟨-56635705371,-56632959381⟩,⟨-1036895968727,-1036830632934⟩,⟨772721880557,772810757824⟩,⟨-372206779874,-372086334642⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6673822517,6673843300⟩,⟨-100449481188,-100449006066⟩,⟨113038852070,113039386568⟩,⟨2066441564220,2066456325547⟩,⟨-1538948909192,-1538931037230⟩,⟨738879281502,738901670625⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6673843300,-6673822517⟩,⟨100449006066,100449481188⟩,⟨-113039386568,-113038852070⟩,⟨-2066456325547,-2066441564220⟩,⟨1538931037230,1538948909192⟩,⟨-738901670625,-738879281502⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092837784476,1092837805259⟩,⟨100449006066,100449481188⟩,⟨-113039386568,-113038852070⟩,⟨-2066456325547,-2066441564220⟩,⟨1538931037230,1538948909192⟩,⟨-738901670625,-738879281502⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6694180224,-6694159232⟩,⟨101062435465,101062915411⟩,⟨-113729705995,-113729166069⟩,⟨-2088365270741,-2088350291496⟩,⟨1558782596350,1558800706174⟩,⟨-755177874119,-755155222431⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3347090112,-3347079616⟩,⟨50531217732,50531457706⟩,⟨-56864852998,-56864583034⟩,⟨-1044182635371,-1044175145748⟩,⟨779391298175,779400353087⟩,⟨-377588937060,-377577611215⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3347079616,3347090112⟩,⟨-50531457706,-50531217732⟩,⟨56864583034,56864852998⟩,⟨1044175145748,1044182635371⟩,⟨-779400353087,-779391298175⟩,⟨377577611215,377588937060⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765470463232,765470492992⟩,⟨-50531457706,-50531217732⟩,⟨56864583034,56864852998⟩,⟨1044175145748,1044182635371⟩,⟨-779400353087,-779391298175⟩,⟨377577611215,377588937060⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273209446119,273209451315⟩,⟨25112251516,25112370297⟩,⟨-28259846642,-28259713017⟩,⟨-516614081387,-516610391055⟩,⟨384732759307,384737227298⟩,⟨-184725417657,-184719820375⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530940926464,1530940985984⟩,⟨-101062915412,-101062435464⟩,⟨113729166068,113729705996⟩,⟨2088350291496,2088365270742⟩,⟨-1558800706174,-1558782596350⟩,⟨755155222430,755177874120⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1192411140976,1192411297843⟩,⟨-758197109293,-758194504087⟩,⟨853223339321,853226269749⟩,⟨10855941167566,10856010078140⟩,⟨-6280057441827,-6279962690382⟩,⟨-427656598975,-427527343392⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1285310654176,1285310967910⟩,⟨-1516394218586,-1516389008173⟩,⟨1706446678642,1706452539498⟩,⟨21711882335141,21712020156278⟩,⟨-12560114883653,-12559925380768⟩,⟨-855313049831,-855054834904⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨171671518848,171671787328⟩,⟨-1297190737673,-1297185963819⟩,⟨1459769668344,1459775038300⟩,⟨17042890491192,17043024187366⟩,⟨-9022265694205,-9022088288999⟩,⟨-2669754159227,-2669518833301⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59115996109,59116100862⟩,⟨-440963909530,-440962206008⟩,⟨496230510686,496232426863⟩,⟨5664346293273,5664390900552⟩,⟨-2921644829107,-2921583219988⟩,⟨-1071133950070,-1071049691473⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380412095692,380412117717⟩,⟨9853492823,9853779309⟩,⟨-11088809528,-11088487239⟩,⟨-205022391493,-205013449461⟩,⟨153555476732,153566275294⟩,⟨-75411791015,-75398299938⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177937198399,3177937382395⟩,⟨-82317817911,-82315415093⟩,⟨92632475227,92635178336⟩,⟨1716932835466,1717007983639⟩,⟨-1287681505627,-1287590866777⟩,⟨635272534319,635385625677⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨170863971157,170864283820⟩,⟨-1278951459253,-1278946324709⟩,⟨1439243951549,1439249727111⟩,⟨16530094361661,16530230625108⟩,⟨-8588017018357,-8587831008098⟩,⟨-2978147433022,-2977894815934⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨342535490005,342536071148⟩,⟨-2576142196926,-2576132288528⟩,⟨2899013619893,2899024765411⟩,⟨33572984852853,33573254812474⟩,⟨-17610282712562,-17609919297097⟩,⟨-5647901592249,-5647413649235⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523643082658,523643307777⟩,⟨69460023406,69463407748⟩,⟨-78169651360,-78165844490⟩,⟨-1426536199992,-1426445267750⟩,⟨1061340086608,1061463488782⟩,⟨-507892673100,-507725756192⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361370871440,361371104476⟩,⟨71902494331,71906013137⟩,⟨-80918402362,-80914444233⟩,⟨-1471929950096,-1471835038535⟩,⟨1093293645930,1093422146044⟩,⟨-519712992112,-519539504948⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722741742880,722742208952⟩,⟨143804988662,143812026274⟩,⟨-161836804724,-161828888466⟩,⟨-2943859900192,-2943670077070⟩,⟨2186587291860,2186844292088⟩,⟨-1039425984224,-1039079009896⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524267083164,1524267163467⟩,⟨-613909346,-612954276⟩,⟨689779500,690853926⟩,⟨21893965949,21923706522⟩,⟨-19869668944,-19833687158⟩,⟨16253551805,16298592618⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001946155429,1001946854338⟩,⟨198955160535,198965555428⟩,⟨-223903038972,-223891346195⟩,⟨-4066880020853,-4066596835270⟩,⟨3018413528900,3018793921594⟩,⟨-1430489089609,-1429978058930⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67887778139,67887780723⟩,⟨12479912270,12479971538⟩,⟨-14044157426,-14044090750⟩,⟨-255592066499,-255590216797⟩,⟨189907864004,189910100290⟩,⟨-90349419449,-90346622308⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50372269997,50372272636⟩,⟨265072005508,265072065101⟩,⟨37715242528,37715294948⟩,⟨-1276620940054,-1276619071074⟩,⟨-220165159890,-220163189420⟩,⟨-174114893338,-174112718638⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131655601553,2131655767304⟩,⟨-281436513192,-281435165706⟩,⟨316709037844,316710553732⟩,⟨5834143932416,5834186048663⟩,⟨-4361801521954,-4361750723032⟩,⟨2126457473541,2126520858338⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2968080299564,2968080645747⟩,⟨-587801004711,-587798167533⟩,⟨661470259478,661473451240⟩,⟨12223843769271,12223932575965⟩,⟨-9153611810584,-9153504942724⟩,⟨4490402483573,4490535508570⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135977590818,135977613803⟩,⟨688620389199,688620764919⟩,⟨132114679987,132114981181⟩,⟨-3169580302491,-3169569325750⟩,⟨-874377310234,-874366073108⟩,⟨-218915607760,-218903295303⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8890623874059,8890625376889⟩,⟨-45024104419063,-45024064632032⟩,⟨-8638076298376,-8638053685128⟩,⟨663259370539584,663260887169503⟩,⟨144658661931566,144659707537429⟩,⟨31097870757604,31098765668002⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8101711873658,8101718894497⟩,⟨-39420160002871,-39420010801800⟩,⟨-9682054419443,-9681933468417⟩,⟨555225213028699,555230177798406⟩,⟨163834182191527,163838879609368⟩,⟨20289390142628,20294552480577⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16203423747316,16203437788994⟩,⟨-78840320005742,-78840021603600⟩,⟨-19364108838886,-19363866936834⟩,⟨1110450426057398,1110460355596812⟩,⟨327668364383054,327677759218736⟩,⟨40578780285256,40589104961154⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10763861442032,10763861442129⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311394,2063168215367208⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9664349814256,9664349814353⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311405,2063168215367197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2389873986368,2389874044224⟩,⟨-11988464342936,-11988464342527⟩,⟨0,0⟩,⟨104010778944236,104010778977589⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7633820142852,7633820142998⟩,⟨-47421397812726,-47421397810861⟩,⟨-21086528562452,-21086528561596⟩,⟨589164776810137,589164776845161⟩,⟨314980617147651,314980617165587⟩,⟨116492576051941,116492576059164⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6534308515076,6534308515222⟩,⟨-47421397812726,-47421397810861⟩,⟨-21086528562453,-21086528561595⟩,⟨589164776810141,589164776845153⟩,⟨314980617147653,314980617165584⟩,⟨116492576051941,116492576059164⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1959550085184,1959550123776⟩,⟨-7979479110977,-7979479110446⟩,⟨-3548177024465,-3548177024224⟩,⟨41227846661967,41227846678855⟩,⟨27250830974840,27250830983025⟩,⟨8151773920891,8151773924313⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100840757001,100840757003⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135554968925,135554968929⟩,⟨700376477806,700376477814⟩,⟨311431321827,311431321832⟩,⟨-1760396448892,-1760396448888⟩,⟨-1565565407728,-1565565407718⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4349424071552,4349424168000⟩,⟨-19967943453913,-19967943452973⟩,⟨-3548177024465,-3548177024224⟩,⟨145238625606203,145238625656444⟩,⟨27250830974840,27250830983025⟩,⟨8151773920891,8151773924313⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨685070980010,685072142296⟩,⟨-5152284393852,-5152264577056⟩,⟨5798027239786,5798049530822⟩,⟨67145969705706,67146509624948⟩,⟨-35220565425124,-35219838594194⟩,⟨-11295803184498,-11294827298470⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5034495051562,5034496310296⟩,⟨-25120227847765,-25120208030029⟩,⟨2249850215321,2249872506598⟩,⟨212384595311909,212385135281392⟩,⟨-7969734450284,-7969007611169⟩,⟨-3144029263607,-3143053374157⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461734354864,461734470318⟩,⟨1702083496927,1702086316129⟩,⟨206343064612,206345109042⟩,⟨-30566810939313,-30566727360463⟩,⟨1059275552062,1059359950742⟩,⟨-288351921865,-288262419002⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨224626789580,224626789582⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-224626789582,-224626789580⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨874884838194,874884838196⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1901630199306,1901630245348⟩,⟨-14319006630082,-14319006514022⟩,⟨0,0⟩,⟨130715559209607,130715559237972⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨802118571530,802118617572⟩,⟨-14319006630082,-14319006514022⟩,⟨0,0⟩,⟨130715559209607,130715559237972⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33595293836,33595295768⟩,⟨-684167625573,-684167615810⟩,⟨319124126993,319124145312⟩,⟨8489608192939,8489608219066⟩,⟨-6498957778804,-6498957686573⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨495329648700,495329766086⟩,⟨1017915871354,1017918700319⟩,⟨525467191605,525469254354⟩,⟨-22077202746374,-22077119141397⟩,⟨-5439682226742,-5439597735831⟩,⟨-288351921865,-288262419002⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505853361827,505853374074⟩,⟨2537541677330,2537541800300⟩,⟨0,0⟩,⟨3442964323895,3442967248197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227886783256,227886842781⟩,⟨1611475266303,1611476905479⟩,⟨241752191325,241753146190⟩,⟨-3907568766569,-3907515085944⟩,⟨-1289924247905,-1289880496151⟩,⟨-132662346547,-132621165667⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-685072142296,-685070980010⟩,⟨5152264577056,5152284393852⟩,⟨-5798049530822,-5798027239786⟩,⟨-67146509624948,-67145969705706⟩,⟨35219838594194,35220565425124⟩,⟨11294827298470,11295803184498⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3664351929256,3664353187990⟩,⟨-14815678876857,-14815659059121⟩,⟨-9346226555287,-9346204264010⟩,⟨78092115981255,78092655950738⟩,⟨62470669569034,62471396408149⟩,⟨19446601219361,19447577108811⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451765219532,451765374731⟩,⟨507577176758,507580421900⟩,⟨-114353938751,-114350833954⟩,⟨-15114024755250,-15113930921102⟩,⟨-7665693022103,-7665581807388⟩,⟨-4057073171648,-4056939831187⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨316728923912,316728923918⟩,⟨1967524518296,1967524518298⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-316728923918,-316728923912⟩,⟨-1967524518298,-1967524518296⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨782782703858,782782703864⟩,⟨-1967524518298,-1967524518296⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1395075663845,1395075691332⟩,⟨-9187407292557,-9187407223072⟩,⟨-4085297676263,-4085297645358⟩,⟨57909425659421,57909425673600⟩,⟨36018560368966,36018560453004⟩,⟨11450138294528,11450138297408⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1395075691332,-1395075663845⟩,⟨9187407223072,9187407292557⟩,⟨4085297645358,4085297676263⟩,⟨-57909425673600,-57909425659421⟩,⟨-36018560453004,-36018560368966⟩,⟨-11450138297408,-11450138294528⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-295564063556,-295564036069⟩,⟨9187407223072,9187407292557⟩,⟨4085297645358,4085297676263⟩,⟨-57909425673600,-57909425659421⟩,⟨-36018560453004,-36018560368966⟩,⟨-11450138297408,-11450138294528⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12379169260,-12379168107⟩,⟨415913070960,415913076800⟩,⟨53514720361,53514732608⟩,⟨-4359812044911,-4359812029458⟩,⟨2012142396654,2012142458705⟩,⟨2771115652290,2771115677052⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439386050272,439386206624⟩,⟨923490247718,923493498700⟩,⟨-60839218390,-60836101346⟩,⟨-19473836800161,-19473742950560⟩,⟨-5653550625449,-5653439348683⟩,⟨-1285957519358,-1285824154135⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100840757003,-100840757001⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4223533754,4223533756⟩,⟨26027124922,26027124927⟩,⟨40119652736,40119652738⟩,⟨-276306403007,-276306402996⟩,⟨247233542879,247233542884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9180178903,9180179130⟩,⟨10520911887,10520913293⟩,⟨87203183662,87203185778⟩,⟨-768609409917,-768609394906⟩,⟨99938903425,99938916483⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1481835152229,1481835173423⟩,⟨-7525394847788,-7525394463524⟩,⟨-1416046745516,-1416046676652⟩,⟨111177399723789,111177407432319⟩,⟨23708098614701,23708100181389⟩,⟨5270407916981,5270408215109⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12372321909,12372322393⟩,⟨-48652705718,-48652698856⟩,⟨105702547585,105702552987⟩,⟨-251631801970,-251631653007⟩,⟨-277758720669,-277758635737⟩,⟨-180611357128,-180611337175⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12372322393,-12372321909⟩,⟨48652698856,48652705718⟩,⟨-105702552987,-105702547585⟩,⟨251631653007,251631801970⟩,⟨277758635737,277758720669⟩,⟨180611337175,180611357128⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113213079396,-113213078910⟩,⟨-826232139340,-826232132476⟩,⟨-105702552987,-105702547585⟩,⟨2450654908559,2450655057522⟩,⟨277758635737,277758720669⟩,⟨180611337175,180611357128⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨82072231258,82072232882⟩,⟨-540494709763,-540494705646⟩,⟨631001049553,631001064934⟩,⟨3406808604005,3406808604990⟩,⟨-3619317516401,-3619317477116⟩,⟨-2481873155917,-2481873155544⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨110610487627,110610491398⟩,⟨-1290163736897,-1290163681130⟩,⟨744713741415,744713781541⟩,⟨20288805661027,20288806901783⟩,⟨-6730826388524,-6730825748895⟩,⟨-4576783621689,-4576783424646⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-110610491398,-110610487627⟩,⟨1290163681130,1290163736897⟩,⟨-744713781541,-744713741415⟩,⟨-20288806901783,-20288805661027⟩,⟨6730825748895,6730826388524⟩,⟨4576783424646,4576783621689⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨988901136378,988901140149⟩,⟨1290163681130,1290163736897⟩,⟨-744713781541,-744713741415⟩,⟨-20288806901783,-20288805661027⟩,⟨6730825748895,6730826388524⟩,⟨4576783424646,4576783621689⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121918185697,121918186166⟩,⟨788978643411,788978652702⟩,⟨188288262997,188288269022⟩,⟨-2440998337112,-2440998106962⟩,⟨-687191619508,-687191493877⟩,⟨-170675531857,-170675483610⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11657176615,11657176717⟩,⟨170148784694,170148786840⟩,⟨21767684048,21767685256⟩,⟨737078755512,737078808988⟩,⟨101661355442,101661382622⟩,⟨-16870288800,-16870282449⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171790973027,171791123403⟩,⟨1671594250870,1671599626454⟩,⟨115487791776,115490654048⟩,⟨-1765559733624,-1765351492180⟩,⟨414728781080,414873581958⟩,⟨-585120068885,-585000671705⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171791123403,-171790973027⟩,⟨-1671599626454,-1671594250870⟩,⟨-115490654048,-115487791776⟩,⟨1765351492180,1765559733624⟩,⟨-414873581958,-414728781080⟩,⟨585000671705,585120068885⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56095659853,56095869754⟩,⟨-60124360151,-60117345391⟩,⟨126261537277,126265354414⟩,⟨-2142217274389,-2141955352320⟩,⟨-1704797829863,-1704609277231⟩,⟨452338325158,452498903218⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28877748613309,28877774207122⟩,⟨-258102365650379,-258101729158311⟩,⟨-86799998418709,-86799521304380⟩,⟨3730947453307340,3730970046736007⟩,⟨1380514057067439,1380533878724211⟩,⟨317427889083739,317447956573130⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13518769268,13518769373⟩,⟨174970127332,174970130068⟩,⟨41756290396,41756291896⟩,⟨590962754472,590962834267⟩,⟨117823697128,117823737408⟩,⟨26637314867,26637329843⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355059110445,355059427886⟩,⟨1422010424065,1422022419258⟩,⟨29466261257,29473147164⟩,⟨-20751865433019,-20751367572956⟩,⟨-3546547866147,-3546199555997⟩,⟨-1990367370013,-1990083115841⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355059427886,-355059110445⟩,⟨-1422022419258,-1422010424065⟩,⟨-29473147164,-29466261257⟩,⟨20751367572956,20751865433019⟩,⟨3546199555997,3546547866147⟩,⟨1990083115841,1990367370013⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84326622386,84327096179⟩,⟨-498532171540,-498516925365⟩,⟨-90312365554,-90302362603⟩,⟨1277530772795,1278122482459⟩,⟨-2107351069452,-2106891482536⟩,⟨704125596483,704543215878⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236395725926,236395725932⟩,⟨1575261316000,1575261316010⟩,⟨311431321827,311431321832⟩,⟨-3959419704444,-3959419704440⟩,⟨-1565565407728,-1565565407718⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1668414451064,-1668412998075⟩,⟨-4058237647759,-4058196234600⟩,⟨436101121576,436127467510⟩,⟨40263950618756,40265456468799⟩,⟨-7516179802273,-7514996529800⟩,⟨2205456075785,2206568493313⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185000375175,-185000213349⟩,⟨-1647200732619,-1647195082109⟩,⟨-237354662641,-237351483149⟩,⟨2344472736709,2344702805880⟩,⟨-172698363284,-172540032495⟩,⟨652897000733,653029677789⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51395350751,51395512583⟩,⟨-71939416619,-71933766099⟩,⟨74076659186,74079838683⟩,⟨-1614946967735,-1614716898560⟩,⟨-1738263771012,-1738105440213⟩,⟨304822700848,304955377907⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4302235107,4302275378⟩,⟨-30045801819,-30044364902⟩,⟨5075942936,5076817679⟩,⟨-44605260047,-44545788295⟩,⟨-290577140447,-290533490395⟩,⟨49872967247,49909843041⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2402413955,2402429085⟩,⟨-6725464468,-6724915036⟩,⟨6925248964,6925568016⟩,⟨-141565688859,-141542226085⟩,⟨-172200485204,-172183994102⟩,⟨38478576357,38491926647⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4281583160,4281610210⟩,⟨-29421259961,-29420170721⟩,⟨4589427148,4590044834⟩,⟨-64606930095,-64556567612⟩,⟨-275912445225,-275878585218⟩,⟨41689736800,41715702423⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4281610210,-4281583160⟩,⟨29420170721,29421259961⟩,⟨-4590044834,-4589427148⟩,⟨64556567612,64606930095⟩,⟨275878585218,275912445225⟩,⟨-41715702423,-41689736800⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨20624897,20692218⟩,⟨-625631098,-623104941⟩,⟨485898102,487390531⟩,⟨19951307565,20061141800⟩,⟨-14698555229,-14621045170⟩,⟨8157264824,8220106241⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56095659853,56095869754⟩,⟨-60124360151,-60117345391⟩,⟨126261537277,126265354414⟩,⟨-2142217274389,-2141955352320⟩,⟨-1704797829863,-1704609277231⟩,⟨452338325158,452498903218⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨20624897,20692218⟩,⟨-625631098,-623104941⟩,⟨485898102,487390531⟩,⟨19951307565,20061141800⟩,⟨-14698555229,-14621045170⟩,⟨8157264824,8220106241⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112098646425,112528143156⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨113816633344,117682103911⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112528143156,-112098646425⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437227670732,437657167463⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨45259895603,46842993706⟩,⟨-117682103911,-113816633344⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157358542028,159371136862⟩,⟨981829523865,985694994432⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44830398872,47272490437⟩,⟨-117682103911,-113816633344⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2510451325440,-2506246629056⟩,⟨10743319721704,10784481866367⟩,⟨0,0⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-256929002840,-255519675851⟩,⟨-1415136306945,-1402522313037⟩,⟨0,0⟩,⟨10660837723011,10866649048270⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨255519675851,256929002840⟩,⟨1402522313037,1415136306945⟩,⟨0,0⟩,⟨-10866649048270,-10660837723011⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986983484620,987412981351⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-118712158400,-118233797824⟩,⟨-1224869350352,-1224336566813⟩,⟨0,0⟩,⟨-1364519380724,-1363332584183⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106609082876,-106133307577⟩,⟨-981756294544,-980321212902⟩,⟨0,0⟩,⟨1223270767889,1225934685685⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106133307577,106609082876⟩,⟨980321212902,981756294544⟩,⟨0,0⟩,⟨-1225934685685,-1223270767889⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨361652983428,363538085716⟩,⟨2382843525939,2396892601489⟩,⟨0,0⟩,⟨-12092583733955,-11884108490900⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2137554519296,-2123581042496⟩,⟨6773704443847,6887348432765⟩,⟨3016461558980,3058042724618⟩,⟨-43142398166589,-41730410787387⟩,⟨-26838220357165,-26168959561578⟩,⟨-8505253668396,-8275528977541⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309832552234,-303920038937⟩,⟨-946853592345,-897989606662⟩,⟨-419140690801,-401200529473⟩,⟨5844042766553,6376479314385⟩,⟨3620667840999,3875312849053⟩,⟨1166216840045,1250121803659⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨303920038937,309832552234⟩,⟨897989606662,946853592345⟩,⟨401200529473,419140690801⟩,⟨-6376479314385,-5844042766553⟩,⟨-3875312849053,-3620667840999⟩,⟨-1250121803659,-1166216840045⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159371136862,-157358542028⟩,⟨-985694994432,-981829523865⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940140490914,942153085748⟩,⟨-985694994432,-981829523865⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-172174794048,-169823543040⟩,⟨-1152788459059,-1145814830215⟩,⟨-511848121910,-510253498319⟩,⟨-1208646818977,-1194067977067⟩,⟨746502495318,754157551424⟩,⟨-238277152587,-236794796861⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147533695327,-145208095202⟩,⟨-836157992594,-825380160962⟩,⟨-371062683675,-367760041379⟩,⟨1010684471380,1045922520756⟩,⟨1377405108505,1394129110236⟩,⟨201635286914,205007037809⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145208095202,147533695327⟩,⟨825380160962,836157992594⟩,⟨367760041379,371062683675⟩,⟨-1045922520756,-1010684471380⟩,⟨-1394129110236,-1377405108505⟩,⟨-205007037809,-201635286914⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨449128134139,457366247561⟩,⟨1723369767624,1783011584939⟩,⟨768960570852,790203374476⟩,⟨-7422401835141,-6854727237933⟩,⟨-5269441959289,-4998072949504⟩,⟨-1455128841468,-1367852126959⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨810781117567,820904333277⟩,⟨4106213293563,4179904186428⟩,⟨768960570852,790203374476⟩,⟨-19514985569096,-18738835728833⟩,⟨-5269441959289,-4998072949504⟩,⟨-1455128841468,-1367852126959⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89660797744,94544980874⟩,⟨-235364207822,-227633266688⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12786779461363,13483326604637⟩,⟨30786365942451,35394426158986⟩,⟨-131631095824351,-118266115205125⟩,⟨148246918750175,185824379970601⟩,⟨-393668887460418,-238799488150595⟩,⟨2187708648291840,2570099485977066⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9428985633136,10066761421273⟩,⟨70455142113818,77683990757090⟩,⟨-89334214610283,-77519291948349⟩,⟨99953148068384,189925503105231⟩,⟨-837413580961411,-650452849967353⟩,⟨1406171771249278,1737527256943597⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨82898903040,88455720192⟩,⟨-722397099414,-575116335328⟩,⟨632780089075,830734581011⟩,⟨6168239945744,10943568607452⟩,⟨-8213471311108,-942672112015⟩,⟨-6552341415052,4072676030078⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1182410530816,1187967347968⟩,⟨-722397099414,-575116335328⟩,⟨632780089075,830734581011⟩,⟨6168239945744,10943568607452⟩,⟨-8213471311108,-942672112015⟩,⟨-6552341415052,4072676030078⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨79922478784,85077603072⟩,⟨-671749777237,-532293332050⟩,⟨585663458640,772491708770⟩,⟨5298547055401,9918621315301⟩,⟨-7354093935877,-400524985894⟩,⟨-6635691197384,3475182149845⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨85948323033,91922096993⟩,⟨-781689427683,-614230852449⟩,⟨675816403830,898918945983⟩,⟨6703248839970,12446063034832⟩,⟨-9596349137826,-1111925391510⟩,⟨-7002426741331,5237204813079⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-88455720192,-82898903040⟩,⟨575116335328,722397099414⟩,⟨-830734581011,-632780089075⟩,⟨-10943568607452,-6168239945744⟩,⟨942672112015,8213471311108⟩,⟨-4072676030078,6552341415052⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1011055907584,1016612724736⟩,⟨575116335328,722397099414⟩,⟨-830734581011,-632780089075⟩,⟨-10943568607452,-6168239945744⟩,⟨942672112015,8213471311108⟩,⟨-4072676030078,6552341415052⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-92216995392,-86190566464⟩,⟨622013754727,785598506195⟩,⟨-903414266774,-684379654940⟩,⟨-12462312836438,-7023108840438⟩,⟨1406707620969,9577542630650⟩,⟨-5171278941556,6699610601352⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-85264192378,-79256534628⟩,⟨511384670359,681284141326⟩,⟨-785696797709,-559646874651⟩,⟨-10388467828189,-4507950964148⟩,⟨-582448853856,8065586760907⟩,⟨-4543200316400,7901211829073⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨684130655,12665562365⟩,⟨-270304757324,67053288877⟩,⟨-109880393879,339272071332⟩,⟨-3685218988219,7938112070684⟩,⟨-10178797991682,6953661369397⟩,⟨-11545627057731,13138416642152⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨342065327,6332781183⟩,⟨-135152378662,33526644439⟩,⟨-54940196940,169636035666⟩,⟨-1842609494110,3969056035342⟩,⟨-5089398995841,3476830684699⟩,⟨-5772813528866,6569208321076⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6332781183,-342065327⟩,⟨-33526644439,135152378662⟩,⟨-169636035666,54940196940⟩,⟨-3969056035342,1842609494110⟩,⟨-3476830684699,5089398995841⟩,⟨-6569208321076,5772813528866⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755790602433,761781337553⟩,⟨-33526644439,135152378662⟩,⟨-169636035666,54940196940⟩,⟨-3969056035342,1842609494110⟩,⟨-3476830684699,5089398995841⟩,⟨-6569208321076,5772813528866⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6250255069,7116263473⟩,⟨-116233706092,-86723072524⟩,⟨95418318322,133665208800⟩,⟨1531769383927,2710073771387⟩,⟨-2413160058144,-804118189824⟩,⟨-325929136458,1910614510847⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7116263473,-6250255069⟩,⟨86723072524,116233706092⟩,⟨-133665208800,-95418318322⟩,⟨-2710073771387,-1531769383927⟩,⟨804118189824,2413160058144⟩,⟨-1910614510847,325929136458⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092395364303,1093261372707⟩,⟨86723072524,116233706092⟩,⟨-133665208800,-95418318322⟩,⟨-2710073771387,-1531769383927⟩,⟨804118189824,2413160058144⟩,⟨-1910614510847,325929136458⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7139392320,-6268087680⟩,⟨87218874659,116990895023⟩,⟨-134535952923,-95963831812⟩,⟨-2740176319762,-1547445267640⟩,⟨816327733186,2443195241615⟩,⟨-1939522737234,319676769655⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3569696160,-3134043840⟩,⟨43609437329,58495447512⟩,⟨-67267976462,-47981915906⟩,⟨-1370088159881,-773722633820⟩,⟨408163866593,1221597620808⟩,⟨-969761368617,159838384828⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3134043840,3569696160⟩,⟨-58495447512,-43609437329⟩,⟨47981915906,67267976462⟩,⟨773722633820,1370088159881⟩,⟨-1221597620808,-408163866593⟩,⟨-159838384828,969761368617⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765257427456,765693099040⟩,⟨-58495447512,-43609437329⟩,⟨47981915906,67267976462⟩,⟨773722633820,1370088159881⟩,⟨-1221597620808,-408163866593⟩,⟨-159838384828,969761368617⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273098841075,273315343177⟩,⟨21680768131,29058426523⟩,⟨-33416302200,-23854579580⟩,⟨-677518442847,-382942345981⟩,⟨201029547456,603290014536⟩,⟨-477653627712,81482284115⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530514854912,1531386198080⟩,⟨-116990895024,-87218874658⟩,⟨95963831812,134535952924⟩,⟨1547445267640,2740176319762⟩,⟨-2443195241616,-816327733186⟩,⟨-319676769656,1939522737234⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1189170458129,1195706202344⟩,⟨-854329306467,-672735388135⟩,⟨740186867733,982452586021⟩,⟨7976381513786,14163037650214⟩,⟨-11117427139353,-1940153705510⟩,⟨-6827559669093,6430938799086⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1278829288482,1291900776912⟩,⟨-1708658612934,-1345470776270⟩,⟨1480373735466,1964905172042⟩,⟨15952763027575,28326075300427⟩,⟨-22234854278703,-3880307411019⟩,⟨-13650462459598,12861877598171⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨166113045248,177294598400⟩,⟨-1469070211124,-1145104012459⟩,⟨1259917297587,1689385834057⟩,⟨11614244669678,23161601263439⟩,⟨-17804918154625,-1045246212525⟩,⟨-14332112446008,9614658683181⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨56983673739,61285315353⟩,⟨-503200000928,-384454797818⟩,⟨421317933636,579982838611⟩,⟨3743066101202,7774392345359⟩,⟨-6031728030724,-24971027534⟩,⟨-5324528049117,3369139826478⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380152262664,380670230029⟩,⟨1098061209,18808623033⟩,⟨-22706128883,237334224⟩,⟨-565465621327,144656348955⟩,⟨-323709990046,644604961088⟩,⟨-752912571504,591447873452⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175782407577,3180109493872⟩,⟨-157340851413,-9160693941⟩,⟨-1985385576,189944880307⟩,⟨-1210049191359,4745891311343⟩,⟨-5411146432326,2708146178403⟩,⟨-4947909937865,6321073102979⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨164589208524,177255072403⟩,⟨-1464171677040,-1110917577000⟩,⟨1216806055396,1688067425894⟩,⟨10750271916351,22894364688331⟩,⟨-17917058947265,76221589560⟩,⟨-15677978262275,10297255401903⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨330702253772,354549670803⟩,⟨-2933241888164,-2256021589459⟩,⟨2476723352983,3377453259951⟩,⟨22364516586029,46055965951770⟩,⟨-35721977101890,-969024622965⟩,⟨-30010090708283,19911914085084⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519521049433,527789603661⟩,⟨-46456938516,187276891286⟩,⟨-235059935490,76129102510⟩,⟨-5508052747557,2586478677530⟩,⟨-4859451006566,7065745144600⟩,⟨-9119721905704,8051571050712⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357112300596,365671685562⟩,⟨-48280565482,194628283776⟩,⟨-244287010077,79117484625⟩,⟨-5732832353388,2722538880127⟩,⟨-5093545037608,7357141589211⟩,⟨-9495326854344,8422027167422⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714224601192,731343371124⟩,⟨-96561130964,389256567552⟩,⟨-488574020154,158234969250⟩,⟨-11465664706776,5445077760254⟩,⟨-10187090075216,14714283178422⟩,⟨-18990653708688,16844054334844⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523398591439,1525135943011⟩,⟨-30267822500,29014831434⟩,⟨-37701376988,39117634602⟩,⟨-1162628503747,1208406935835⟩,⟨-1639077051792,1596832324958⟩,⟨-2230291280503,2265451873692⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989574574693,1014448627743⟩,⟨-154072970759,559238275729⟩,⟨-702779699261,245507418918⟩,⟨-16698815581095,8377203479706⟩,⟨-15247020898124,21499663266336⟩,⟨-27860242895314,24904816863608⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67832822420,67940415480⟩,⟨10770222888,14446620876⟩,⟨-16613172382,-11850093938⟩,⟨-335978493257,-188695992135⟩,⟨98097937132,298989528802⟩,⟨-236434105703,42540719185⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50019999952,50724867354⟩,⟨261269024585,269068296595⟩,⟨35036410419,40089537988⟩,⟨-1376258991385,-1185370166763⟩,⟨-308893243542,-118993593531⟩,⟨-290317447914,-69201559837⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130469257377,2132895758833⟩,⟨-325886943650,-242816501290⟩,⟨267162377208,374760022994⟩,⟨4321909912291,7657863654292⟩,⟨-6834334187756,-2287873175256⟩,⟨-873732525876,5435610134178⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2965602876746,2970670836495⟩,⟨-680836957562,-506999088760⟩,⟨557833100616,782941688347⟩,⟨9053008631338,16050679522111⟩,⟨-14337977370870,-4808851576090⟩,⟨-1790416087053,11424759169726⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134913949070,137048922747⟩,⟨673285109360,703906377862⟩,⟨119877669198,144434520405⟩,⟨-3639765271808,-2697647597989⟩,⟨-1388309173708,-364275493331⟩,⟨-831430275369,397513385564⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8821126028450,8960717760826⟩,⟨-46752069934553,-43335859076448⟩,⟨-9593055285915,-7715901787454⟩,⟨599428766243216,729598906601033⟩,⟨99258887415086,192311265418372⟩,⟨-12903744612934,75761985952725⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7939126624402,8267477675020⟩,⟨-44390778925660,-34445190944709⟩,⟨-14578356334620,-4943592594444⟩,⟨355844348721512,754528469968833⟩,⟨-50243182503434,383876567830717⟩,⟨-243242804421125,285131397051680⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15878253248804,16534955350040⟩,⟨-88781557851320,-68890381889418⟩,⟨-29156712669240,-9887185188888⟩,⟨711688697443024,1509056939937666⟩,⟨-100486365006868,767753135661434⟩,⟨-486485608842250,570262794103360⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10743319721704,10784481866367⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239228,2075048233589864⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9643808093928,9684970238591⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239235,2075048233589852⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2387534470720,2392217527616⟩,⟨-12060075023605,-11917323006543⟩,⟨0,0⟩,⟨100606314842521,107411991083576⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7585600777017,7682619602561⟩,⟨-48123982268613,-46732218554583⟩,⟨-21367467508403,-20810760493660⟩,⟨575801525872610,602897914825233⟩,⟨308749095729401,321372710159217⟩,⟨114186803406974,118857548946049⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6486089149241,6583107974785⟩,⟨-48123982268613,-46732218554583⟩,⟨-21367467508404,-20810760493660⟩,⟨575801525872619,602897914825227⟩,⟨308749095729404,321372710159216⟩,⟨114186803406974,118857548946049⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1951406248512,1967730975680⟩,⟨-8157901758966,-7805221772042⟩,⟨-3622179473812,-3475816169697⟩,⟨35642342204342,46794536390614⟩,⟨24692309302751,29804445095793⟩,⟨7138758140364,9160668131506⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100626050579,101055547311⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134549861242,136562456077⟩,⟨696642344972,704109259656⟩,⟨310415559095,312446483827⟩,⟨-1767320322048,-1753486165276⟩,⟨-1569500168196,-1561630647248⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4338940719232,4359948503296⟩,⟨-20217976782571,-19722544778585⟩,⟨-3622179473812,-3475816169697⟩,⟨136248657046863,154206527474190⟩,⟨24692309302751,29804445095793⟩,⟨7138758140364,9160668131506⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨661404507544,709099341606⟩,⟨-5866483776328,-4512043178918⟩,⟨4953446705966,6754906519902⟩,⟨44729033172058,92111931903540⟩,⟨-71443954203780,-1938049245930⟩,⟨-60020181416566,39823828170168⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5000345226776,5069047844902⟩,⟨-26084460558899,-24234587957503⟩,⟨1331267232154,3279090350205⟩,⟨180977690218921,246318459377730⟩,⟨-46751644901029,27866395849863⟩,⟨-52881423276202,48984496301674⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457625894070,465893576177⟩,⟨1579427730236,1817515448689⟩,⟨121836059258,301379504911⟩,⟨-35106575866701,-25909829209453⟩,⟨-3238146128834,5171649421069⟩,⟨-4860304372198,4502139821416⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨224197292850,225056286312⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-225056286312,-224197292850⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨874455341464,875314334926⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1898836008741,1904429422379⟩,⟨-14385385406069,-14253064895063⟩,⟨0,0⟩,⟨127682751799218,133750314871228⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨799324380965,804917794603⟩,⟨-14385385406069,-14253064895063⟩,⟨0,0⟩,⟨127682751799218,133750314871228⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32590861180,34606699727⟩,⟨-704637762817,-663882923968⟩,⟨317856335867,320395012775⟩,⟨8156839989726,8829843246541⟩,⟨-6530975501168,-6467144718132⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨490216755250,500500275904⟩,⟨874789967419,1153632524721⟩,⟨439692395125,621774517686⟩,⟨-26949735876975,-17079985962912⟩,⟨-9769121630002,-1295495297063⟩,⟨-4860304372198,4502139821416⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505357813684,506349053570⟩,⟨2517543755956,2557704464203⟩,⟨0,0⟩,⟨2303354216540,4586136051397⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225313549585,230491278686⟩,⟨1524516916662,1695545986036⟩,⟨202091530349,286340708558⟩,⟨-7377990536541,-395484574123⟩,⟨-3492132825772,850947607116⟩,⟨-2238276027970,2073333450984⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-709099341606,-661404507544⟩,⟨4512043178918,5866483776328⟩,⟨-6754906519902,-4953446705966⟩,⟨-92111931903540,-44729033172058⟩,⟨1938049245930,71443954203780⟩,⟨-39823828170168,60020181416566⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3629841377626,3698543995752⟩,⟨-15705933603653,-13856061002257⟩,⟨-10377085993714,-8429262875663⟩,⟨44136725143323,109477494302132⟩,⟨26630358548681,101248399299573⟩,⟨-32685070029804,69180849548072⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨444192349905,459369632126⟩,⟨349118946622,672887826513⟩,⟨-264081890749,19500399922⟩,⟨-20659452535002,-9749600201877⟩,⟨-13129120308775,-1832686245225⟩,⟨-11129262847231,2684959086421⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨314717084056,318742273724⟩,⟨1963659047730,1971389988864⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-318742273724,-314717084056⟩,⟨-1971389988864,-1963659047730⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨780769354052,784794543720⟩,⟨-1971389988864,-1963659047730⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1385704487023,1404500411102⟩,⟨-9350916966355,-9027621214842⟩,⟨-4151888622540,-4020174276769⟩,⟨53189102986109,62654097337859⟩,⟨33852140264218,38197785007519⟩,⟨10597992161876,12305766723003⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1404500411102,-1385704487023⟩,⟨9027621214842,9350916966355⟩,⟨4020174276769,4151888622540⟩,⟨-62654097337859,-53189102986109⟩,⟨-38197785007519,-33852140264218⟩,⟨-12305766723003,-10597992161876⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-304988783326,-286192859247⟩,⟨9027621214842,9350916966355⟩,⟨4020174276769,4151888622540⟩,⟨-62654097337859,-53189102986109⟩,⟨-38197785007519,-33852140264218⟩,⟨-12305766723003,-10597992161876⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13112712026,-11668944384⟩,⟨397708725042,434677399027⟩,⟨42514774889,64700250711⟩,⟨-4695435910834,-4037679546006⟩,⟨1789422419966,2230687545246⟩,⟨2668219740555,2873180540034⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨431079637879,447700687742⟩,⟨746827671664,1107565225540⟩,⟨-221567115860,84200650633⟩,⟨-25354888445836,-13787279747883⟩,⟨-11339697888809,398001300021⟩,⟨-8461043106676,5558139626455⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101055547311,-100626050579⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4102826991,4344790245⟩,⟨24838075053,27216965668⟩,⟨40014577925,40224844809⟩,⟨-281916955696,-270700380156⟩,⟨246677084567,247790085082⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8909083470,9452999965⟩,⟨6278482086,14746717924⟩,⟨86889653291,87517563587⟩,⟨-835019522574,-701793982750⟩,⟨94437742819,105411467849⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1472675646367,1491063116076⟩,⟨-7687032697336,-7366412955909⟩,⟨-1453219716583,-1379490227793⟩,⟨107311350493516,115148458043342⟩,⟨22766967814991,24674611271326⟩,⟨5038284649794,5508721275916⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11932743525,12819345634⟩,⟨-57679564775,-39690076590⟩,⟨103885204582,107506109534⟩,⟨-469061013255,-34120895062⟩,⟨-320389166117,-234924228800⟩,⟨-190519130605,-170669330321⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12819345634,-11932743525⟩,⟨39690076590,57679564775⟩,⟨-107506109534,-103885204582⟩,⟨34120895062,469061013255⟩,⟨234924228800,320389166117⟩,⟨170669330321,190519130605⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113874892945,-112558794104⟩,⟨-835624258336,-816775776689⟩,⟨-107506109534,-103885204582⟩,⟨2233144150614,2668084268807⟩,⟨234924228800,320389166117⟩,⟨170669330321,190519130605⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨79564706977,84600782185⟩,⟨-561350183522,-520243424777⟩,⟨620256618414,641529677390⟩,⟨3069170404112,3758188867340⟩,⟨-3848377213850,-3386100387339⟩,⟨-2592525781638,-2370505552694⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨106568228398,114728305478⟩,⟨-1352725605766,-1229869949529⟩,⟨718949460612,770162390903⟩,⟨18847226306221,21805663756806⟩,⟨-7403755337893,-6050356567532⟩,⟨-4846985648841,-4307566592524⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-114728305478,-106568228398⟩,⟨1229869949529,1352725605766⟩,⟨-770162390903,-718949460612⟩,⟨-21805663756806,-18847226306221⟩,⟨6050356567532,7403755337893⟩,⟨4307566592524,4846985648841⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨984783322298,992943399378⟩,⟨1229869949529,1352725605766⟩,⟨-770162390903,-718949460612⟩,⟨-21805663756806,-18847226306221⟩,⟨6050356567532,7403755337893⟩,⟨4307566592524,4846985648841⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120510284767,123326380494⟩,⟨774453468683,803877058333⟩,⟨182368965304,194183597715⟩,⟨-2745878260688,-2144372380057⟩,⟨-822963464621,-550234365540⟩,⟨-225230975825,-115388710827⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11522826871,11793864582⟩,⟨167229330104,173088888842⟩,⟨21269794802,22268517050⟩,⟨660829498714,812920713483⟩,⟨87978399580,115309240114⟩,⟨-19832823220,-13920308308⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166403299954,177361493359⟩,⟨1462678468070,1881021585179⟩,⟨-5587146426,231266869343⟩,⟨-10950969785654,7456252268427⟩,⟨-6195401424717,7132892286572⟩,⟨-6697549674373,5533343200040⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177361493359,-166403299954⟩,⟨-1881021585179,-1462678468070⟩,⟨-231266869343,5587146426⟩,⟨-7456252268427,10950969785654⟩,⟨-7132892286572,6195401424717⟩,⟨-5533343200040,6697549674373⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47952056226,64087978732⟩,⟨-356504668517,232867517966⟩,⟨-29175338994,291927854984⟩,⟨-14834242804968,10555485211531⟩,⟨-10625025112344,7046349031833⟩,⟨-7771619228010,8770883125357⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28180622944248,29591632322772⟩,⟨-281569339483836,-234982880684536⟩,⟨-106652025840576,-67742625421058⟩,⟨2755897480075788,4721829198881910⟩,⟨464717762731867,2331023215156415⟩,⟨-705030939390898,1350432917274435⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13208344839,13832865194⟩,⟨169765568078,180333241528⟩,⟨39976541194,43561085946⟩,⟨475008979241,705402997024⟩,⟨72292409438,163328585094⟩,⟨9970824033,43295118707⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338531559123,372289888030⟩,⟨808712454343,2030556115213⟩,⟨-317176511196,358591643849⟩,⟨-47080657360441,5826630921104⟩,⟨-21212121407463,14719008722727⟩,⟨-17065185636593,13228871485698⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372289888030,-338531559123⟩,⟨-2030556115213,-808712454343⟩,⟨-358591643849,317176511196⟩,⟨-5826630921104,47080657360441⟩,⟨-14719008722727,21212121407463⟩,⟨-13228871485698,17065185636593⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58789749849,109169128619⟩,⟨-1283728443549,298852771197⟩,⟨-580158759709,401377161829⟩,⟨-31181519366940,33293377612558⟩,⟨-26058706611536,21610122707484⟩,⟨-21689914592374,22623325263048⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235175911821,237618003388⟩,⟨1571097686436,1579423594582⟩,⟨310415559095,312446483827⟩,⟨-3966343577600,-3952509420828⟩,⟨-1569500168196,-1561630647248⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1712502371753,-1625482617021⟩,⟨-5514076738255,-2600229194237⟩,⟨-604558480570,1519494568750⟩,⟨-21690792682890,102214362013987⟩,⟨-62268841206090,46065098010046⟩,⟨-54728315506711,58951419701607⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192082297050,-178158527943⟩,⟨-1870532737384,-1429921223181⟩,⟨-370253365736,-99174774405⟩,⟨-7325694695253,12078578309199⟩,⟨-7586757746225,7128305156662⟩,⟨-6181538446890,7499780295996⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43093614771,59459475445⟩,⟨-299435050948,149502371401⟩,⟨-59837806641,213271709422⟩,⟨-11292038272853,8126068888371⟩,⟨-9156257914421,5566674509414⟩,⟨-6529954582551,7152047664118⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2563946864,6363214919⟩,⟨-110222449802,40540557225⟩,⟨-36712889223,52380492489⟩,⟨-3834137918189,3821104442534⟩,⟨-3044827727637,2226684612646⟩,⟨-2343961285734,2402647809600⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1688985898,3215454145⟩,⟨-32385744016,16169601770⟩,⟨-6471827138,23066648228⟩,⟨-1302732785202,1041977417606⟩,⟨-1106468185404,660067912788⟩,⟨-729468202679,856274390583⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨2997601436,5754508240⟩,⟨-81816134022,16947994268⟩,⟨-22175087663,35941733340⟩,⟨-2516615756180,2482189632003⟩,⟨-2166663225224,1423154036985⟩,⟨-1446499478190,1601854445818⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5754508240,-2997601436⟩,⟨-16947994268,81816134022⟩,⟨-35941733340,22175087663⟩,⟨-2482189632003,2516615756180⟩,⟨-1423154036985,2166663225224⟩,⟨-1601854445818,1446499478190⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3190561376,3365613483⟩,⟨-127170444070,122356691247⟩,⟨-72654622563,74555580152⟩,⟨-6316327550192,6337720198714⟩,⟨-4467981764622,4393347837870⟩,⟨-3945815731552,3849147287790⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47952056226,64087978732⟩,⟨-356504668517,232867517966⟩,⟨-29175338994,291927854984⟩,⟨-14834242804968,10555485211531⟩,⟨-10625025112344,7046349031833⟩,⟨-7771619228010,8770883125357⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3190561376,3365613483⟩,⟨-127170444070,122356691247⟩,⟨-72654622563,74555580152⟩,⟨-6316327550192,6337720198714⟩,⟨-4467981764622,4393347837870⟩,⟨-3945815731552,3849147287790⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (523/5120) u, BivariateJet2.affineZ (539/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000035

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000036Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2512559689728,-2512559631872⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2512559689728,-2512559631872⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-117994695616,-117994695552⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-117994695616,-117994695552⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2122557485824,-2122557446848⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2122557485824,-2122557446848⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-172348406848,-172348406784⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-172348406848,-172348406784⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨85083510144,85083510208⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-92223936128,-92223936064⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨85083635008,85083635072⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-92224082816,-92224082752⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7140447808,-7140447744⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7140425984,-7140425920⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨177307446208,177307446272⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨177307717760,177307717824⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1950209040000,1950209078592⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1950209040000,1950209078592⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2129523360768,-2129523321664⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2115630293888,-2115630254976⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-173528316672,-173528316608⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-171170644032,-171170643968⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨82510385856,82510385920⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-89208213632,-89208213568⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨87679218688,87679218752⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-95281720320,-95281720256⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7602501568,-7602501504⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6697827776,-6697827712⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨171718599488,171718599552⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨182960939008,182960939072⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1942101938304,1942101976896⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1958352677696,1958352716288⟩



end LaneCBRB2Cell000036Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000036
open Set LaneCBRB2Cell000036Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111883898060,111883898061⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨119614839193,119614839194⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111883898061,-111883898060⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437871915827,437871915828⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨47635675217,47635675219⟩,⟨-119614839194,-119614839193⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159519573277,159519573280⟩,⟨979896788582,979896788583⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47635675216,47635675220⟩,⟨-119614839194,-119614839193⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2512559689728,-2512559631872⟩,⟨10805181447606,10805181447704⟩,⟨0,0⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-255672577803,-255672571913⟩,⟨-1413048061962,-1413048004086⟩,⟨0,0⟩,⟨10805181447410,10805181447900⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨255672571913,255672577803⟩,⟨1413048004086,1413048061962⟩,⟨0,0⟩,⟨-10805181447900,-10805181447410⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨987627729715,987627729716⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117994695616,-117994695552⟩,⟨-1224070348819,-1224070348816⟩,⟨0,0⟩,⟨-1362739766463,-1362739766455⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105987813504,-105987813446⟩,⟨-981516932226,-981516932158⟩,⟨0,0⟩,⟨1224070348810,1224070348825⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105987813446,105987813504⟩,⟨981516932158,981516932226⟩,⟨0,0⟩,⟨-1224070348825,-1224070348810⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨361660385359,361660391307⟩,⟨2394564936244,2394564994188⟩,⟨0,0⟩,⟨-12029251796725,-12029251796220⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2122557485824,-2122557446848⟩,⟨6754079708921,6754079709056⟩,⟨3018095228246,3018095228311⟩,⟨-41488958883092,-41488958881439⟩,⟨-26118096706788,-26118096705882⟩,⟨-8284495204091,-8284495203739⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-307945323949,-307945318288⟩,⟨-911749658278,-911749623500⟩,⟨-407420020433,-407420004889⟩,⟨6019309709094,6019309709702⟩,⟨3712805296767,3712805336069⟩,⟨1201932845727,1201932845860⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307945318288,307945323949⟩,⟨911749623500,911749658278⟩,⟨407420004889,407420020433⟩,⟨-6019309709702,-6019309709094⟩,⟨-3712805336069,-3712805296767⟩,⟨-1201932845860,-1201932845727⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159519573280,-159519573277⟩,⟨-979896788583,-979896788582⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939992054496,939992054499⟩,⟨-979896788583,-979896788582⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-172348406848,-172348406784⟩,⟨-1146188319268,-1146188319261⟩,⟨-512180140914,-512180140910⟩,⟨-1194846539172,-1194846539157⟩,⟨752178851906,752178851919⟩,⟨-238586377916,-238586377911⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147343719658,-147343719601⟩,⟨-826298003401,-826298003333⟩,⟨-369235509301,-369235509268⟩,⟨1021495566547,1021495566580⟩,⟨1383623764467,1383623764556⟩,⟨203971739705,203971739717⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147343719601,147343719658⟩,⟨826298003333,826298003401⟩,⟨369235509268,369235509301⟩,⟨-1021495566580,-1021495566547⟩,⟨-1383623764556,-1383623764467⟩,⟨-203971739717,-203971739705⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨455289037889,455289043607⟩,⟨1738047626833,1738047661679⟩,⟨776655514157,776655529734⟩,⟨-7040805276282,-7040805275641⟩,⟨-5096429100625,-5096429061234⟩,⟨-1405904585577,-1405904585432⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨816949423248,816949434914⟩,⟨4132612563077,4132612655867⟩,⟨776655514157,776655529734⟩,⟨-19070057073007,-19070057071861⟩,⟨-5096429100625,-5096429061234⟩,⟨-1405904585577,-1405904585432⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95271350432,95271350440⟩,⟨-239229678388,-239229678386⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12689290264401,12689290265467⟩,⟨31863249706017,31863249711638⟩,⟨-116641231888566,-116641231868701⟩,⟨160019459035673,160019459078679⟩,⟨-292890194910776,-292890194707693⟩,⟨2144355860471808,2144355861022048⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9428284431968,9428284567397⟩,⟨71368580241443,71368581658577⟩,⟨-77702480870769,-77702479437899⟩,⟨138333459526922,138333466708688⟩,⟨-692337207433302,-692337193341610⟩,⟨1412272683043277,1412272709540144⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨88462102528,88462237440⟩,⟨-663388690652,-663386627706⟩,⟨722261611823,722263856830⟩,⟨8617224926516,8617276071669⟩,⟨-4346582573884,-4346511287709⟩,⟨-1388578675362,-1388482063061⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1187973730304,1187973865216⟩,⟨-663388690652,-663386627706⟩,⟨722261611823,722263856830⟩,⟨8617224926516,8617276071669⟩,⟨-4346582573884,-4346511287709⟩,⟨-1388578675362,-1388482063061⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨85083510144,85083635072⟩,⟨-613989653560,-613987674502⟩,⟨668478544644,668480698394⟩,⟨7632680678214,7632731130894⟩,⟨-3649624813592,-3649555972942⟩,⟨-1691601249944,-1691509067038⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨91928973172,91929118593⟩,⟨-714723849533,-714721400896⟩,⟨778152301322,778154966170⟩,⟨9654495722903,9654560800316⟩,⟨-5086264547925,-5086178603247⟩,⟨-1056915256720,-1056802256272⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-88462237440,-88462102528⟩,⟨663386627706,663388690652⟩,⟨-722263856830,-722261611823⟩,⟨-8617276071669,-8617224926516⟩,⟨4346511287709,4346582573884⟩,⟨1388482063061,1388578675362⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1011049390336,1011049525248⟩,⟨663386627706,663388690652⟩,⟨-722263856830,-722261611823⟩,⟨-8617276071669,-8617224926516⟩,⟨4346511287709,4346582573884⟩,⟨1388482063061,1388578675362⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-92224082816,-92223936064⟩,⟨721429853492,721432193204⟩,⟨-785458669476,-785456123230⟩,⟨-9844608279029,-9844548338075⟩,⟨5242177220341,5242258716583⟩,⟨948859245406,948968150256⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-84804119204,-84803972942⟩,⟨607743277211,607745778779⟩,⟨-661682685100,-661679962631⟩,⟨-7459219242106,-7459151945270⟩,⟨3508022650555,3508110812555⟩,⟨1787969065835,1788084166743⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7124853968,7125145651⟩,⟨-106980572322,-106975622117⟩,⟨116469616222,116475003539⟩,⟨2195276480797,2195408855046⟩,⟨-1578241897370,-1578067790692⟩,⟨731053809115,731281910471⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3562426984,3562572826⟩,⟨-53490286161,-53487811058⟩,⟨58234808111,58237501770⟩,⟨1097638240398,1097704427523⟩,⟨-789120948685,-789033895346⟩,⟨365526904557,365640955236⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3562572826,-3562426984⟩,⟨53487811058,53490286161⟩,⟨-58237501770,-58234808111⟩,⟨-1097704427523,-1097638240398⟩,⟨789033895346,789120948685⟩,⟨-365640955236,-365526904557⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758560810790,758560975896⟩,⟨53487811058,53490286161⟩,⟨-58237501770,-58234808111⟩,⟨-1097704427523,-1097638240398⟩,⟨789033895346,789120948685⟩,⟨-365640955236,-365526904557⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7117290427,7117312137⟩,⟨-106747116420,-106746621668⟩,⟨116220291160,116220829656⟩,⟨2187115847436,2187131170692⟩,⟨-1570970369344,-1570952412584⟩,⟨725458556968,725480342704⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7117312137,-7117290427⟩,⟨106746621668,106747116420⟩,⟨-116220829656,-116220291160⟩,⟨-2187131170692,-2187115847436⟩,⟨1570952412584,1570970369344⟩,⟨-725480342704,-725458556968⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092394315639,1092394337349⟩,⟨106746621668,106747116420⟩,⟨-116220829656,-116220291160⟩,⟨-2187131170692,-2187115847436⟩,⟨1570952412584,1570970369344⟩,⟨-725480342704,-725458556968⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7140447808,-7140425920⟩,⟨107442109261,107442609372⟩,⟨-116978047000,-116977502669⟩,⟨-2211880186292,-2211864621706⟩,⟨1592618469407,1592636680987⟩,⟨-742652489661,-742630431646⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3570223904,-3570212960⟩,⟨53721054630,53721304686⟩,⟨-58489023500,-58488751334⟩,⟨-1105940093146,-1105932310853⟩,⟨796309234703,796318340494⟩,⟨-371326244831,-371315215823⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3570212960,3570223904⟩,⟨-53721304686,-53721054630⟩,⟨58488751334,58489023500⟩,⟨1105932310853,1105940093146⟩,⟨-796318340494,-796309234703⟩,⟨371315215823,371326244831⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765693596576,765693626784⟩,⟨-53721304686,-53721054630⟩,⟨58488751334,58489023500⟩,⟨1105932310853,1105940093146⟩,⟨-796318340494,-796309234703⟩,⟨371315215823,371326244831⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273098578909,273098584338⟩,⟨26686655417,26686779105⟩,⟨-29055207414,-29055072790⟩,⟨-546782792673,-546778961859⟩,⟨392738103146,392742592336⟩,⟨-181370085676,-181364639242⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531387193152,1531387253568⟩,⟨-107442609372,-107442109260⟩,⟨116977502668,116978047000⟩,⟨2211864621706,2211880186292⟩,⟨-1592636680988,-1592618469406⟩,⟨742630431646,742652489662⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1195713750340,1195713909895⟩,⟨-784554239054,-784551589937⟩,⟨854179858683,854182741696⟩,⟨11220673288611,11220743310403⟩,⟨-6261394988022,-6261301891194⟩,⟨-421799728878,-421676957155⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1291915872904,1291916192014⟩,⟨-1569108478107,-1569103179874⟩,⟨1708359717367,1708365483392⟩,⟨22441346577233,22441486620792⟩,⟨-12522789976037,-12522603782394⟩,⟨-843599308009,-843354064060⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨177307446208,177307717824⟩,⟨-1335422106893,-1335417267865⟩,⟨1453934384659,1453939651086⟩,⟨17477216383551,17477352042674⟩,⟨-8891895307586,-8891721415895⟩,⟨-2640580268996,-2640357443691⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨61030627164,61030733525⟩,⟨-453373221129,-453371492571⟩,⟨493607816821,493609697994⟩,⟨5792220722935,5792265949575⟩,⟨-2864984650037,-2864924246157⟩,⟨-1063920260435,-1063840400793⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380368570594,380368593163⟩,⟨10482088160,10482386649⟩,⟨-11412689257,-11412364376⟩,⟨-217381701632,-217372410741⟩,⟨157097706583,157108564690⟩,⟨-74336789734,-74323654145⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178300841196,3178301029780⟩,⟨-87589203885,-87586699362⟩,⟨95359942824,95362668797⟩,⟨1821157454560,1821235579149⟩,⟨-1318031005799,-1317939821132⟩,⟨626759153104,626869312576⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨176418046661,176418364582⟩,⟨-1315404196205,-1315398974297⟩,⟨1432139485167,1432145168176⟩,⟨16916587813240,16916726394462⟩,⟨-8433465903560,-8433283068766⟩,⟨-2955008793626,-2954768815904⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨353725492869,353726082406⟩,⟨-2650826303098,-2650816242162⟩,⟨2886073869826,2886084819262⟩,⟨34393804196791,34394078437136⟩,⟨-17325361211146,-17325004484661⟩,⟨-5595589062622,-5595126259595⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523336442407,523336670224⟩,⟨73803234632,73806665882⟩,⟨-80356942230,-80353207988⟩,⟨-1509424320568,-1509332183334⟩,⟨1083053668042,1083174546734⟩,⟨-498347921087,-498189871857⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361053495060,361053730819⟩,⟨76376056542,76379624032⟩,⟨-83158248142,-83154365621⟩,⟨-1556658588655,-1556562399093⟩,⟨1114945579153,1115071460402⟩,⟨-509336949173,-509172685111⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722106990120,722107461638⟩,⟨152752113084,152759248064⟩,⟨-166316496284,-166308731242⟩,⟨-3113317177310,-3113124798186⟩,⟨2229891158306,2230142920804⟩,⟨-1018673898346,-1018345370222⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524269881015,1524269963141⟩,⟨-695987704,-694992840⟩,⟨756673012,757755840⟩,⟨24733451014,24764338856⟩,⟨-21684268404,-21648100062⟩,⟨17150088942,17193932694⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001068027026,1001068734636⟩,⟨211305511875,211316068298⟩,⟨-230070182434,-230058693737⟩,⟨-4299989357929,-4299701845496⟩,⟨3077301448966,3077674711463⟩,⟨-1401169248286,-1400684588464⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67832692186,67832694884⟩,⟨13256954244,13257015952⟩,⟨-14433564526,-14433497360⟩,⟨-270326252654,-270324332235⟩,⟨193687497722,193689744742⟩,⟨-88562440187,-88559718574⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50400448125,50400450850⟩,⟨264805291442,264805353301⟩,⟨37190277037,37190329963⟩,⟨-1277698657659,-1277696714922⟩,⟨-215390059970,-215388075970⟩,⟨-172928728409,-172926606523⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132898530680,2132898698975⟩,⟨-299289681576,-299288276666⟩,⟨325849849964,325851379100⟩,⟨6182317450126,6182361245039⟩,⟨-4459274240508,-4459223122918⟩,⟨2093544878148,2093606635716⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2970676627388,2970676978987⟩,⟨-625270881970,-625267922187⟩,⟨680759904470,680763125972⟩,⟨12959860119977,12959952535249⟩,⟨-9364002000234,-9363894392241⟩,⟨4425798919843,4425928601259⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136172669276,136172692756⟩,⟨686793060358,686793449394⟩,⟨131686548238,131686852487⟩,⟨-3159218417136,-3159206995283⟩,⟨-868375919472,-868364589974⟩,⟨-218294958117,-218282930976⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8877887299921,8877888830720⟩,⟨-44776062082098,-44776021277268⟩,⟨-8585432326935,-8585409530435⟩,⟨657626747449568,657628308460979⟩,⟨143215515108038,143216567206513⟩,⟨30836264365943,30837138711786⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8083015130515,8083022237778⟩,⟨-39060950521372,-39060799022640⟩,⟨-9674427363954,-9674307998653⟩,⟨546815936386136,546820983811661⟩,⟨162958969451518,162963600882217⟩,⟨20354554830097,20359474978567⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16166030261030,16166044475556⟩,⟨-78121901042744,-78121598045280⟩,⟨-19348854727908,-19348615997306⟩,⟨1093631872772272,1093641967623322⟩,⟨325917938903036,325927201764434⟩,⟨40709109660194,40718949957134⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10805181447606,10805181447704⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230896,2087019636287702⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9705669819830,9705669819928⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230908,2087019636287687⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2394564936256,2394564994112⟩,⟨-12029251796733,-12029251796224⟩,⟨0,0⟩,⟨104822536628670,104822536664337⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7578542211197,7578542211340⟩,⟨-46553466903638,-46553466901832⟩,⟨-20802655931763,-20802655930929⟩,⟨571937246025498,571937246059064⟩,⟨307809291076794,307809291094089⟩,⟨114204152123417,114204152130408⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6479030583421,6479030583564⟩,⟨-46553466903638,-46553466901831⟩,⟨-20802655931764,-20802655930928⟩,⟨571937246025498,571937246059060⟩,⟨307809291076792,307809291094088⟩,⟨114204152123416,114204152130408⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1950209040000,1950209078592⟩,⟨-7900268028509,-7900268027990⟩,⟨-3530275369308,-3530275369070⟩,⟨40294112333989,40294112352113⟩,⟨26870275553840,26870275562602⟩,⟨8045908824142,8045908827838⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100498837339,100498837341⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136376121569,136376121573⟩,⟨695565611676,695565611685⟩,⟨310817068201,310817068207⟩,⟨-1746589471214,-1746589471210⟩,⟨-1560944962444,-1560944962432⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4344773976256,4344774072704⟩,⟨-19929519825242,-19929519824214⟩,⟨-3530275369308,-3530275369070⟩,⟨145116648962659,145116649016450⟩,⟨26870275553840,26870275562602⟩,⟨8045908824142,8045908827838⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨707450985738,707452164812⟩,⟨-5301652606196,-5301632484324⟩,⟨5772147739652,5772169638524⟩,⟨68787608393582,68788156874272⟩,⟨-34650722422292,-34650008969322⟩,⟨-11191178125244,-11190252519190⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5052224961994,5052226237516⟩,⟨-25231172431438,-25231152308538⟩,⟨2241872370344,2241894269454⟩,⟨213904257356241,213904805890722⟩,⟨-7780446868452,-7779733406720⟩,⟨-3145269301102,-3144343691352⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461789327032,461789443629⟩,⟨1717809348051,1717812203337⟩,⟨204914219177,204916220830⟩,⟨-30745396604294,-30745311859832⟩,⟨1074458882986,1074541537962⟩,⟨-287487553474,-287402949811⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨223767796120,223767796122⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-223767796122,-223767796120⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨875743831654,875743831656⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1907233556649,1907233602736⟩,⟨-14370241087281,-14370240971140⟩,⟨0,0⟩,⟨131606519757458,131606519788094⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨807721928873,807721974960⟩,⟨-14370241087281,-14370240971140⟩,⟨0,0⟩,⟨131606519757458,131606519788094⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34994063270,34994065270⟩,⟨-710453306434,-710453296334⟩,⟨321668947845,321668966201⟩,⟨8828422830746,8828422857850⟩,⟨-6530558220472,-6530558128119⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨496783390302,496783508899⟩,⟨1007356041617,1007358907003⟩,⟨526583167022,526585187031⟩,⟨-21916973773548,-21916889001982⟩,⟨-5456099337486,-5456016590157⟩,⟨-287487553474,-287402949811⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504862395711,504862407910⟩,⟨2536208829314,2536208952001⟩,⟨0,0⟩,⟨3381169318170,3381172243620⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228107867385,228107927354⟩,⟨1608461939435,1608463595308⟩,⟨241791021147,241791954518⟩,⟨-3888650846717,-3888596548728⟩,⟨-1290622614534,-1290579840684⟩,⟨-132005569405,-131966718778⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-707452164812,-707450985738⟩,⟨5301632484324,5301652606196⟩,⟨-5772169638524,-5772147739652⟩,⟨-68788156874272,-68787608393582⟩,⟨34650008969322,34650722422292⟩,⟨11190252519190,11191178125244⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3637321811444,3637323086966⟩,⟨-14627887340918,-14627867218018⟩,⟨-9302445007832,-9302423108722⟩,⟨76328492088387,76329040622868⟩,⟨61520284523162,61520997984894⟩,⟨19236161343332,19237086953082⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451149245730,451149403952⟩,⟨486671913929,486675216837⟩,⟨-125591823034,-125588746185⟩,⟨-14818249203714,-14818153680395⟩,⟨-7553190933048,-7553081086608⟩,⟨-4027160978346,-4027033385925⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨319039146554,319039146560⟩,⟨1959793577164,1959793577166⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-319039146560,-319039146554⟩,⟨-1959793577166,-1959793577164⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨780472481216,780472481222⟩,⟨-1959793577166,-1959793577164⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1384327777794,1384327805200⟩,⟨-9083986712436,-9083986643232⟩,⟨-4059226146545,-4059226115614⟩,⟨56765415965821,56765415980787⟩,⟨35558775973603,35558776058015⟩,⟨11334890751296,11334890754358⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1384327805200,-1384327777794⟩,⟨9083986643232,9083986712436⟩,⟨4059226115614,4059226146545⟩,⟨-56765415980787,-56765415965821⟩,⟨-35558776058015,-35558775973603⟩,⟨-11334890754358,-11334890751296⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-284816177424,-284816150018⟩,⟨9083986643232,9083986712436⟩,⟨4059226115614,4059226146545⟩,⟨-56765415980787,-56765415965821⟩,⟨-35558776058015,-35558775973603⟩,⟨-11334890754358,-11334890751296⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12339488354,-12339487164⟩,⟨424543100404,424543106419⟩,⟨62437694945,62437707216⟩,⟨-4435804056891,-4435804040960⟩,⟨1920281022875,1920281085009⟩,⟨2742032900104,2742032924923⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438809757376,438809916788⟩,⟨911215014333,911218323256⟩,⟨-63154128089,-63151038969⟩,⟨-19254053260605,-19253957721355⟩,⟨-5632909910173,-5632800001599⟩,⟨-1285128078242,-1285000461002⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100498837341,-100498837339⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4354051247,4354051249⟩,⟨27007896705,27007896710⟩,⟨40022876823,40022876824⟩,⟨-285814051313,-285814051302⟩,⟨248259301866,248259301870⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9482444917,9482445152⟩,⟨11183313874,11183315331⟩,⟨87163587057,87163589166⟩,⟨-798324623092,-798324607558⟩,⟨102798145600,102798158703⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1479804952361,1479804973494⟩,⟨-7485727497509,-7485727115620⟩,⟨-1406817463710,-1406817395311⟩,⟨110277553163057,110277560797468⟩,⟨23464589885934,23464591435800⟩,⟨5221485395210,5221485690109⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12762183313,12762183812⟩,⟨-49507322878,-49507315807⟩,⟨105178549668,105178555074⟩,⟨-275662774983,-275662621710⟩,⟨-267021162897,-267021077708⟩,⟨-178019100743,-178019080840⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12762183812,-12762183313⟩,⟨49507315807,49507322878⟩,⟨-105178555074,-105178549668⟩,⟨275662621710,275662774983⟩,⟨267021077708,267021162897⟩,⟨178019080840,178019100743⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113261021153,-113261020652⟩,⟨-826236515849,-826236508776⟩,⟨-105178555074,-105178549668⟩,⟨2474685877262,2474686030535⟩,⟨267021077708,267021162897⟩,⟨178019080840,178019100743⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨84491625268,84491626948⟩,⟨-554435743914,-554435739661⟩,⟨623708472337,623708487733⟩,⟨3464643512195,3464643513256⟩,⟨-3548235341332,-3548235302016⟩,⟨-2463225045317,-2463225044930⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨113715146203,113715150089⟩,⟨-1321439473469,-1321439416303⟩,⟨731327045164,731327085281⟩,⟨20686671291817,20686672558054⟩,⟨-6509305333965,-6509304696513⟩,⟨-4510010395421,-4510010199915⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-113715150089,-113715146203⟩,⟨1321439416303,1321439473469⟩,⟨-731327085281,-731327045164⟩,⟨-20686672558054,-20686671291817⟩,⟨6509304696513,6509305333965⟩,⟨4510010199915,4510010395421⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨985796477687,985796481573⟩,⟨1321439416303,1321439473469⟩,⟨-731327085281,-731327045164⟩,⟨-20686672558054,-20686671291817⟩,⟨6509304696513,6509305333965⟩,⟨4510010199915,4510010395421⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122271649418,122271649905⟩,⟨787530473165,787530482729⟩,⟨187962377408,187962383493⟩,⟨-2459868751800,-2459868516141⟩,⟨-681230057600,-681229931427⟩,⟨-166769248924,-166769200732⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11667051511,11667051616⟩,⟨170221738306,170221740518⟩,⟨21668947530,21668948742⟩,⟨731927323762,731927378858⟩,⟨103062608278,103062635554⟩,⟨-16552981517,-16552975181⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171539711831,171539864208⟩,⟨1673795414475,1673800870235⟩,⟨113283726634,113286559640⟩,⟨-1822875926907,-1822664300415⟩,⟨438557824604,438700934229⟩,⟨-574054537234,-573940357238⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171539864208,-171539711831⟩,⟨-1673800870235,-1673795414475⟩,⟨-113286559640,-113283726634⟩,⟨1822664300415,1822875926907⟩,⟨-438700934229,-438557824604⟩,⟨573940357238,574054537234⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56568003177,56568215523⟩,⟨-65338930800,-65331819167⟩,⟨128504461507,128508227884⟩,⟨-2065986546302,-2065720621821⟩,⟨-1729323548763,-1729137665288⟩,⟨441934787833,442087818456⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28673765296820,28673791076610⟩,⟨-254722294783384,-254721652470730⟩,⟨-86224554963263,-86224085203492⟩,⟨3654867878786212,3654890697948031⟩,⟨1363008599758787,1363028076508663⟩,⟨314752073027188,314771165335279⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13597269800,13597269909⟩,⟨175155309844,175155312672⟩,⟨41804869240,41804870762⟩,⟨581043487419,581043569415⟩,⟨117744961078,117745001734⟩,⟨27173344461,27173359493⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354598271699,354598593352⟩,⟨1417751674079,1417763823129⟩,⟨23905579139,23912416914⟩,⟨-20804688718199,-20804184442809⟩,⟨-3494219025690,-3493874377544⟩,⟨-1955669899906,-1955396771293⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354598593352,-354598271699⟩,⟨-1417763823129,-1417751674079⟩,⟨-23912416914,-23905579139⟩,⟨20804184442809,20804688718199⟩,⟨3493874377544,3494219025690⟩,⟨1955396771293,1955669899906⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84211164024,84211645089⟩,⟨-506548808796,-506533350823⟩,⟨-87066545003,-87056618108⟩,⟨1550131182204,1550730996844⟩,⟨-2139035532629,-2138580975909⟩,⟨670268693051,670669438904⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236874958908,236874958914⟩,⟨1571309443330,1571309443341⟩,⟨310817068201,310817068207⟩,⟨-3945612726766,-3945612726762⟩,⟨-1560944962444,-1560944962432⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1665269069514,-1665267597905⟩,⟨-4100770031955,-4100727998888⟩,⟨446673581661,446699621426⟩,⟨41138876992985,41140407995987⟩,⟨-7635142137052,-7633974224772⟩,⟨2124680334269,2125742462704⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185186942568,-185186778179⟩,⟨-1648784811439,-1648779066784⟩,⟨-235006544138,-235003387386⟩,⟨2426072455381,2426306662803⟩,⟨-198408767644,-198251919945⟩,⟨641574999400,641702318959⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51688016340,51688180735⟩,⟨-77475368109,-77469623443⟩,⟨75810524063,75813680821⟩,⟨-1519540271385,-1519306063959⟩,⟨-1759353730088,-1759196882377⟩,⟨292816860191,292944179752⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4332521160,4332562175⟩,⟨-31065484146,-31064017764⟩,⟨5362663799,5363536029⟩,⟨-18287036803,-18226217192⟩,⟨-296530494305,-296487006847⟩,⟨47979546844,48015124931⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2429852459,2429867917⟩,⟨-7284253716,-7283690432⟩,⟨7127701986,7128021456⟩,⟨-131950818515,-131926724853⟩,⟨-176099067918,-176082557942⟩,⟨37984788308,37997717134⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4309840943,4309868447⟩,⟨-30379329061,-30378218633⟩,⟨4840700047,4841316577⟩,⟨-40324014634,-40272613740⟩,⟨-280796523790,-280762751943⟩,⟨39381931605,39407029478⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4309868447,-4309840943⟩,⟨30378218633,30379329061⟩,⟨-4841316577,-4840700047⟩,⟨40272613740,40324014634⟩,⟨280762751943,280796523790⟩,⟨-39407029478,-39381931605⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨22652713,22721232⟩,⟨-687265513,-684688703⟩,⟨521347222,522835982⟩,⟨21985576937,22097797442⟩,⟨-15767742362,-15690483057⟩,⟨8572517366,8633193326⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56568003177,56568215523⟩,⟨-65338930800,-65331819167⟩,⟨128504461507,128508227884⟩,⟨-2065986546302,-2065720621821⟩,⟨-1729323548763,-1729137665288⟩,⟨441934787833,442087818456⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨22652713,22721232⟩,⟨-687265513,-684688703⟩,⟨521347222,522835982⟩,⟨21985576937,22097797442⟩,⟨-15767742362,-15690483057⟩,⟨8572517366,8633193326⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111669149696,112098646426⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨117682103910,121547574477⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112098646426,-111669149696⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437657167462,438086664192⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46842993704,48429111706⟩,⟨-121547574477,-117682103910⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158512143400,160527758132⟩,⟨977964053299,981829523866⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46413496974,48858608436⟩,⟨-121547574477,-117682103910⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2514672104640,-2510451267584⟩,⟨10784481866270,10825960642718⟩,⟨0,0⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-256378679420,-254967706864⟩,⟨-1419373165097,-1406710748927⟩,⟨0,0⟩,⟨10701364779618,10908759273099⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨254967706864,256378679420⟩,⟨1406710748927,1419373165097⟩,⟨0,0⟩,⟨-10908759273099,-10701364779618⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨987412981350,987842478080⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-118233797888,-117755645312⟩,⟨-1224336566816,-1223804246568⟩,⟨0,0⟩,⟨-1363332584190,-1362147335310⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106225677790,-105750089286⟩,⟨-982234238937,-980799781353⟩,⟨0,0⟩,⟨1222739374527,1225400975868⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105750089286,106225677790⟩,⟨980799781353,982234238937⟩,⟨0,0⟩,⟨-1225400975868,-1222739374527⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨360717796150,362604357210⟩,⟨2387510530280,2401607404034⟩,⟨0,0⟩,⟨-12134160248967,-11924104154145⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2129523360768,-2115630254976⟩,⟨6698423130440,6810411838672⟩,⟨2997669376334,3038766437202⟩,⟨-42183918969676,-40808001753625⟩,⟨-26448928983397,-25793288098746⟩,⟨-8398366353378,-8172739116901⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310908591013,-305001855265⟩,⟨-935913248722,-887439632624⟩,⟨-416320096875,-398462708415⟩,⟨5757050648106,6279845365455⟩,⟨3586682012775,3838056293967⟩,⟨1160271543802,1243286268252⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305001855265,310908591013⟩,⟨887439632624,935913248722⟩,⟨398462708415,416320096875⟩,⟨-6279845365455,-5757050648106⟩,⟨-3838056293967,-3586682012775⟩,⟨-1243286268252,-1160271543802⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160527758132,-158512143400⟩,⟨-981829523866,-977964053299⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938983869644,940999484376⟩,⟨-981829523866,-977964053299⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173528316672,-171170643968⟩,⟨-1149682132873,-1142702908983⟩,⟨-512981529104,-511380880216⟩,⟨-1202141908514,-1187590840526⟩,⟨748336495089,756013986024⟩,⟨-239333575520,-237842327488⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148511441251,-146179876212⟩,⟨-831688846529,-820913896672⟩,⟨-370893117352,-367579520001⟩,⟨1003927373960,1039056841584⟩,⟨1375250333527,1392004813714⟩,⟨202277300469,205664605097⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146179876212,148511441251⟩,⟨820913896672,831688846529⟩,⟨367579520001,370893117352⟩,⟨-1039056841584,-1003927373960⟩,⟨-1392004813714,-1375250333527⟩,⟨-205664605097,-202277300469⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨451181731477,459420032264⟩,⟨1708353529296,1767602095251⟩,⟨766042228416,787213214227⟩,⟨-7318902207039,-6760978022066⟩,⟨-5230061107681,-4961932346302⟩,⟨-1448950873349,-1362548844271⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨811899527627,822024389474⟩,⟨4095864059576,4169209499285⟩,⟨766042228416,787213214227⟩,⟨-19453062456006,-18685082176211⟩,⟨-5230061107681,-4961932346302⟩,⟨-1448950873349,-1362548844271⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92826993948,97717216872⟩,⟨-243095148954,-235364207820⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12371676745544,13023429588724⟩,⟨29798739565354,34105731760920⟩,⟨-122925252282970,-110820859916685⟩,⟨143548024725695,178632046347438⟩,⟨-365421235881436,-225333680329177⟩,⟨1985383751171335,2320528175145935⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9135472742546,9736665339487⟩,⟨68090492928383,74881563416886⟩,⟨-83282728733546,-72507817049677⟩,⟨97592562359325,181955314352877⟩,⟨-780503376123682,-610629673338186⟩,⟨1272860621737948,1565137450242318⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨85685206016,91269964032⟩,⟨-741141884321,-593625151217⟩,⟨632136176570,824292598718⟩,⟨6374742536841,11142170158159⟩,⟨-8014947544836,-980989867073⟩,⟨-6220144446747,3737984578801⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1185196833792,1190781591808⟩,⟨-741141884321,-593625151217⟩,⟨632136176570,824292598718⟩,⟨6374742536841,11142170158159⟩,⟨-8014947544836,-980989867073⟩,⟨-6220144446747,3737984578801⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨82510385856,87679218752⟩,⟨-687560155756,-548125500758⟩,⟨583684767431,764699390970⟩,⟨5456183377261,10063383785219⟩,⟨-7144520519703,-427608588456⟩,⟨-6302292565169,3157888718295⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨88940440101,94957431133⟩,⟨-803735673014,-635388322097⟩,⟨676608704573,893908954016⟩,⟨6951628071248,12714179498517⟩,⟨-9407639801206,-1164809977354⟩,⟨-6650311537666,4864679266341⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-91269964032,-85685206016⟩,⟨593625151217,741141884321⟩,⟨-824292598718,-632136176570⟩,⟨-11142170158159,-6374742536841⟩,⟨980989867073,8014947544836⟩,⟨-3737984578801,6220144446747⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1008241663744,1013826421760⟩,⟨593625151217,741141884321⟩,⟨-824292598718,-632136176570⟩,⟨-11142170158159,-6374742536841⟩,⟨980989867073,8014947544836⟩,⟨-3737984578801,6220144446747⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-95281720320,-89208213568⟩,⟨643796356352,808232935562⟩,⟨-898910776625,-685562204296⟩,⟨-12744921570372,-7290476055942⟩,⟨1465316646799,9401266372187⟩,⟨-4811270138263,6355757709153⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-87856392903,-81803080017⟩,⟨526129075024,697083729156⟩,⟨-777570455380,-557222265894⟩,⟨-10539325938999,-4630133849509⟩,⟨-562727609682,7848762796285⟩,⟨-4187060322396,7532187462133⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1084047198,13154351116⟩,⟨-277606597990,61695407059⟩,⟨-100961750807,336686688122⟩,⟨-3587697867751,8084045649008⟩,⟨-9970367410888,6683952818931⟩,⟨-10837371860062,12396866728474⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨542023599,6577175558⟩,⟨-138803298995,30847703530⟩,⟨-50480875404,168343344061⟩,⟨-1793848933876,4042022824504⟩,⟨-4985183705444,3341976409466⟩,⟨-5418685930031,6198433364237⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6577175558,-542023599⟩,⟨-30847703530,138803298995⟩,⟨-168343344061,50480875404⟩,⟨-4042022824504,1793848933876⟩,⟨-3341976409466,4985183705444⟩,⟨-6198433364237,5418685930031⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755546208058,761581379281⟩,⟨-30847703530,138803298995⟩,⟨-168343344061,50480875404⟩,⟨-4042022824504,1793848933876⟩,⟨-3341976409466,4985183705444⟩,⟨-6198433364237,5418685930031⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6677468745,7576278526⟩,⟨-123043706708,-92522702066⟩,⟨98525049032,136848313264⟩,⟨1634565610811,2848968074012⟩,⟨-2441887307182,-835476843830⟩,⟨-305801612195,1856504252576⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7576278526,-6677468745⟩,⟨92522702066,123043706708⟩,⟨-136848313264,-98525049032⟩,⟨-2848968074012,-1634565610811⟩,⟨835476843830,2441887307182⟩,⟨-1856504252576,305801612195⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091935349250,1092834159031⟩,⟨92522702066,123043706708⟩,⟨-136848313264,-98525049032⟩,⟨-2848968074012,-1634565610811⟩,⟨835476843830,2441887307182⟩,⟨-1856504252576,305801612195⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7602501568,-6697827712⟩,⟨93088037113,123897432521⟩,⟨-137797820887,-99127059803⟩,⟨-2882696604751,-1652434303274⟩,⟨848974201878,2474357703028⟩,⟨-1886655115158,298986531327⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3801250784,-3348913856⟩,⟨46544018556,61948716261⟩,⟨-68898910444,-49563529901⟩,⟨-1441348302376,-826217151637⟩,⟨424487100939,1237178851514⟩,⟨-943327557579,149493265664⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3348913856,3801250784⟩,⟨-61948716261,-46544018556⟩,⟨49563529901,68898910444⟩,⟨826217151637,1441348302376⟩,⟨-1237178851514,-424487100939⟩,⟨-149493265664,943327557579⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765472297472,765924653664⟩,⟨-61948716261,-46544018556⟩,⟨49563529901,68898910444⟩,⟨826217151637,1441348302376⟩,⟨-1237178851514,-424487100939⟩,⟨-149493265664,943327557579⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272983837312,273208539758⟩,⟨23130675516,30760926677⟩,⟨-34212078316,-24631262258⟩,⟨-712242018503,-408641402702⟩,⟨208869210957,610471826796⟩,⟨-464126063144,76450403049⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530944594944,1531849307328⟩,⟨-123897432522,-93088037112⟩,⟨99127059802,137797820888⟩,⟨1652434303274,2882696604752⟩,⟨-2474357703028,-848974201878⟩,⟨-298986531328,1886655115158⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1192438659781,1199043704588⟩,⟨-881397330183,-698207863334⟩,⟨743503620549,980283682746⟩,⟨8315463833882,14546542230162⟩,⟨-10972896068160,-2024503501442⟩,⟨-6470087710348,6048240481438⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1285365691786,1298575781400⟩,⟨-1762794660365,-1396415726668⟩,⟨1487007241098,1960567365492⟩,⟨16630927667768,29093084460309⟩,⟨-21945792136309,-4049007002883⟩,⟨-12935466030692,12096480962871⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨171718599488,182960939072⟩,⟨-1507908013136,-1182353275543⟩,⟨1259057634981,1677084295290⟩,⟨12013505840281,23615010053760⟩,⟨-17418678047508,-1128306648982⟩,⟨-13623151887343,8905667419377⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨58879897998,63218526607⟩,⟨-515915714729,-396396589987⟩,⟨420407923434,575140149473⟩,⟨3857850421001,7908164566426⟩,⟨-5886156848262,-42750617877⟩,⟨-5075349074465,3114623491579⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380098872701,380636549730⟩,⟨1420581647,19744743118⟩,⟨-23053565478,-55985213⟩,⟨-588972384644,143394213276⟩,⟨-319835374838,647443982365⟩,⟨-729492568692,570869394126⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176063413963,3180556182722⟩,⟨-165218234809,-11853452850⟩,⟨467145330,192905492442⟩,⟨-1199792354917,4945513595671⟩,⟨-5437663324755,2676285373605⟩,⟨-4776867965643,6127580442046⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨170081229816,182872168501⟩,⟨-1501888409274,-1145671046262⟩,⟨1214420744897,1674798804148⟩,⟨11083398758591,23315339745714⟩,⟨-17516467992265,25687481342⟩,⟨-14955755113671,9563797900884⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨341799829304,365833107573⟩,⟨-3009796422410,-2328024321805⟩,⟨2473478379878,3351883099438⟩,⟨23096904598872,46930349799474⟩,⟨-34935146039773,-1102619167640⟩,⟨-28578907001014,18469465320261⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519185116455,527512563411⟩,⟨-42733584638,192285384216⟩,⟨-233207458520,69931583708⟩,⟨-5607236891208,2520079399065⟩,⟨-4672171808064,6918762654832⟩,⟨-8602200160193,7558100671256⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356765982376,365383808122⟩,⟨-44399397208,199780926951⟩,⟨-242298198717,72657610839⟩,⟨-5833906609164,2654726891230⟩,⟨-4898459812127,7201707658319⟩,⟨-8953586047270,7906284268834⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713531964752,730767616244⟩,⟨-88798794416,399561853902⟩,⟨-484596397434,145315221678⟩,⟨-11667813218328,5309453782460⟩,⟨-9796919624254,14403415316638⟩,⟨-17907172094540,15812568537668⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523368316418,1525171838583⟩,⟨-31374730456,29955669596⟩,⟨-37721253462,39272771856⟩,⟨-1196533770738,1248130993941⟩,⟨-1638880859198,1592913105304⟩,⟨-2155490783904,2192456727353⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988595263929,1013673853635⟩,⟨-144028542791,574155929469⟩,⟨-697271615464,227673766580⟩,⟨-17002894820301,8216249065506⟩,⟨-14705815700011,21066288096408⟩,⟨-26306898086441,23424599724195⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67775704732,67887327711⟩,⟨11485645812,15287055902⟩,⟨-17002152088,-12230769222⟩,⟨-352985032223,-201191621425⟩,⟨101800694154,302345831420⟩,⟨-229550105170,40122120998⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50046821940,50754387408⟩,⟨260957006988,268849202593⟩,⟨34508837593,39573611230⟩,⟨-1379422832339,-1184409591131⟩,⟨-304216865655,-114436452152⟩,⟨-285426563479,-71036008697⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131665817422,2134185979559⟩,⟨-345229993744,-259228958876⟩,⟨276046260144,383962281338⟩,⟨4617415011580,8060319252787⟩,⟨-6925649230982,-2380984386096⟩,⟨-815227644000,5291548533503⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2968101636187,2973366749299⟩,⟨-721466212943,-541420158848⟩,⟨576544421058,802409460504⟩,⟨9676756694083,16902914795645⟩,⟨-14538213124233,-5007930368786⟩,⟨-1666350232645,11130529112159⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135100030171,137253125923⟩,⟨671142828415,702394501133⟩,⟨119398421978,144057285434⟩,⟨-3642681163702,-2674028772016⟩,⟨-1382908641022,-357655751073⟩,⟨-812597757340,379795504204⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8808002087273,8948375644954⟩,⟨-46523230521365,-43069528608429⟩,⟨-9541661114541,-7662204725225⟩,⟨592805890253520,725028720348398⟩,⟨97885567370449,190812737546741⟩,⟨-11824906899219,74171127612829⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7919469815674,8249784899631⟩,⟨-44063384730754,-34051999197145⟩,⟨-14471498374217,-5036335018986⟩,⟨346038749108954,747482850945843⟩,⟨-46288255518357,378117458214094⟩,⟨-228951991564062,271123744223247⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15838939631348,16499569799262⟩,⟨-88126769461508,-68103998394290⟩,⟨-28942996748434,-10072670037972⟩,⟨692077498217908,1494965701891686⟩,⟨-92576511036714,756234916428188⟩,⟨-457903983128124,542247488446494⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10784481866270,10825960642718⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533866,2099083303790624⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9684970238494,9726449014942⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533869,2099083303790615⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2392217469760,2396916459264⟩,⟨-12101371604921,-11957606413725⟩,⟨0,0⟩,⟨101381360168522,108260423343400⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7530945636333,7626707920819⟩,⟨-47240084235488,-45879879002768⟩,⟨-21078252808477,-20532102197535⟩,⟨559016994400622,585213327098630⟩,⟨301752660316618,314021088925267⟩,⟨111955985611205,116509704074350⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6431434008557,6527196293043⟩,⟨-47240084235488,-45879879002768⟩,⟨-21078252808478,-20532102197534⟩,⟨559016994400629,585213327098621⟩,⟨301752660316622,314021088925263⟩,⟨111955985611205,116509704074349⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1942101938304,1958352716288⟩,⟨-8076118303503,-7728503660614⟩,⟨-3603517353268,-3458649639947⟩,⟨34846278608331,45723586097133⟩,⟨24361977711255,29373773367510⟩,⟨7048983118468,9038774665989⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100284130918,100713627649⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135369505910,137385120643⟩,⟨691835865659,699294012018⟩,⟨309799316355,311834218728⟩,⟨-1753486165281,-1739706366688⟩,⟨-1564882742808,-1557007182066⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4334319408064,4355269175552⟩,⟨-20177489908424,-19686110074339⟩,⟨-3603517353268,-3458649639947⟩,⟨136227638776853,153984009440533⟩,⟨24361977711255,29373773367510⟩,⟨7048983118468,9038774665989⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨683599658608,731666215146⟩,⟨-6019592844820,-4656048643610⟩,⟨4946956759756,6703766198876⟩,⟨46193809197744,93860699598948⟩,⟨-69870292079546,-2205238335280⟩,⟨-57157814002028,36938930640522⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5017919066672,5086935390698⟩,⟨-26197082753244,-24342158717949⟩,⟨1343439406488,3245116558929⟩,⟨182421447974597,247844709039481⟩,⟨-45508314368291,27168535032230⟩,⟨-50108830883560,45977705306511⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457673788894,465955706035⟩,⟨1595120240968,1833454808407⟩,⟨122532267888,297247843986⟩,⟨-35287196835654,-26090912723470⟩,⟨-3098990107558,5074549605921⟩,⟨-4589894284012,4211489333462⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨223338299392,224197292852⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-224197292852,-223338299392⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨875314334924,876173328384⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1904429376315,1910042803476⟩,⟨-14437113416200,-14303810670437⟩,⟨0,0⟩,⟨128539492851485,134675511271456⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨804917748539,810531175700⟩,⟨-14437113416200,-14303810670437⟩,⟨0,0⟩,⟨128539492851485,134675511271456⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33977855751,36017286529⟩,⟨-731138579607,-689955675071⟩,⟨320394994437,322946015318⟩,⟨8487925178775,9176483497421⟩,⟨-6562818552468,-6498504886492⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨491651644645,501972992564⟩,⟨863981661361,1143499133336⟩,⟨442927262325,620193859304⟩,⟨-26799271656879,-16914429226049⟩,⟨-9661808660026,-1423955280571⟩,⟨-4589894284012,4211489333462⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504367106722,505357825907⟩,⟨2516159178967,2556424289217⟩,⟨0,0⟩,⟨2234856254543,4531068346710⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225530054671,230716959947⟩,⟨1521437051750,1692689863077⟩,⟨203179244442,285053666066⟩,⟨-7363833112264,-372956378458⟩,⟨-3427153498749,788788785017⟩,⟨-2109608427883,1935685844173⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-731666215146,-683599658608⟩,⟨4656048643610,6019592844820⟩,⟨-6703766198876,-4946956759756⟩,⟨-93860699598948,-46193809197744⟩,⟨2205238335280,69870292079546⟩,⟨-36938930640522,57157814002028⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3602653192918,3671669516944⟩,⟨-15521441264814,-13666517229519⟩,⟨-10307283552144,-8405606399703⟩,⟨42366939177905,107790200242789⟩,⟨26567216046535,99244065447056⟩,⟨-29889947522054,66196588668017⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443550909667,458778922209⟩,⟨327445022477,652605033282⟩,⟨-272819214009,6447780873⟩,⟨-20382805766314,-9430334637957⟩,⟨-12912350515099,-1840705104682⟩,⟨-10747082744488,2392972950806⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨317024286800,321055516264⟩,⟨1955928106598,1963659047732⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-321055516264,-317024286800⟩,⟨-1963659047732,-1955928106598⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨778456111512,782487340976⟩,⟨-1963659047732,-1955928106598⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1375011491338,1393697138757⟩,⟨-9245011248556,-8926611075780⟩,⟨-4125070635837,-3994825070800⟩,⟨52167791736415,61386902288622⟩,⟨33437752652501,37692396191481⟩,⟨10497510818065,12175713291687⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1393697138757,-1375011491338⟩,⟨8926611075780,9245011248556⟩,⟨3994825070800,4125070635837⟩,⟨-61386902288622,-52167791736415⟩,⟨-37692396191481,-33437752652501⟩,⟨-12175713291687,-10497510818065⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-294185510981,-275499863562⟩,⟨8926611075780,9245011248556⟩,⟨3994825070800,4125070635837⟩,⟨-61386902288622,-52167791736415⟩,⟨-37692396191481,-33437752652501⟩,⟨-12175713291687,-10497510818065⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13072617266,-11629628792⟩,⟨406304606916,443338576485⟩,⟨51418330417,73642441790⟩,⟨-4771842221606,-4113002785985⟩,⟨1697772190737,2138671404925⟩,⟨2639207415847,2844036027666⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430478292401,447149293417⟩,⟨733749629393,1095943609767⟩,⟨-221400883592,80090222663⟩,⟨-25154647987920,-13543337423942⟩,⟨-11214578324362,297966300243⟩,⟨-8107875328641,5237008978472⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100713627649,-100284130918⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4233276928,4475375770⟩,⟨25815918049,28200667711⟩,⟨39917784923,40128086017⟩,⟨-291433663695,-280198968767⟩,⟨247702508009,248816179610⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9210379195,9756242293⟩,⟨6911345635,15438477252⟩,⟨86849488477,87478538129⟩,⟨-865748271573,-730491562616⟩,⟨97273538155,108293929972⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1470669039866,1489009142730⟩,⟨-7646255295332,-7327836668896⟩,⟨-1443734887602,-1370512363120⟩,⟨106453310482664,114205594557558⟩,⟨22534884827536,24419370312983⟩,⟨4992064885849,5457024311195⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12319487293,13212351381⟩,⟨-58602761099,-40476261911⟩,⟨103356275267,106986958155⟩,⟨-495424330846,-55828693123⟩,⟨-309737777824,-224098590230⟩,⟨-187913268985,-168089667565⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13212351381,-12319487293⟩,⟨40476261911,58602761099⟩,⟨-106986958155,-103356275267⟩,⟨55828693123,495424330846⟩,⟨224098590230,309737777824⟩,⟨168089667565,187913268985⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113925979030,-112603618211⟩,⟨-835697066473,-816711573825⟩,⟨-106986958155,-103356275267⟩,⟨2254851948675,2694447586398⟩,⟨224098590230,309737777824⟩,⟨168089667565,187913268985⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨81981618165,87022625435⟩,⟨-575365379072,-534107606083⟩,⟨612919384260,634281772539⟩,⟨3125342835534,3817382067947⟩,⟨-3777609495000,-3314779132040⟩,⟨-2573995367734,-2351756536134⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨109655800473,117850035983⟩,⟨-1384361458255,-1260781053122⟩,⟨705553213277,756785572898⟩,⟨19236964546106,22211105380112⟩,⟨-7180759018441,-5830409823421⟩,⟨-4779316919434,-4241699691027⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-117850035983,-109655800473⟩,⟨1260781053122,1384361458255⟩,⟨-756785572898,-705553213277⟩,⟨-22211105380112,-19236964546106⟩,⟨5830409823421,7180759018441⟩,⟨4241699691027,4779316919434⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨981661591793,989855827303⟩,⟨1260781053122,1384361458255⟩,⟨-756785572898,-705553213277⟩,⟨-22211105380112,-19236964546106⟩,⟨5830409823421,7180759018441⟩,⟨4241699691027,4779316919434⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120860063045,123683514406⟩,⟨772906792338,802529865497⟩,⟨182032647713,193868371468⟩,⟨-2767289323378,-2160731992750⟩,⟨-817067408340,-544205658139⟩,⟨-221321407514,-111485417635⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11532006132,11804448785⟩,⟨167282775232,173181627308⟩,⟨21169927202,22170923242⟩,⟨654927526909,808513685045⟩,⟨89358012076,116732508078⟩,⟨-19509904642,-13608397304⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166123526426,177140761180⟩,⟨1463644222501,1884515423283⟩,⟨-5772493614,227057719624⟩,⟨-11068073194652,7459786804054⟩,⟨-6042433271196,7026966722299⟩,⟨-6376099071812,5237702443917⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177140761180,-166123526426⟩,⟨-1884515423283,-1463644222501⟩,⟨-227057719624,5772493614⟩,⟨-7459786804054,11068073194652⟩,⟨-7026966722299,6042433271196⟩,⟨-5237702443917,6376099071812⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48389293491,64593433521⟩,⟨-363078371533,229045640576⟩,⟨-23878475182,290826159680⟩,⟨-14823619916318,10695116816194⟩,⟨-10454120221048,6831222056213⟩,⟨-7347310871800,8311784915985⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27976816780866,29387572189052⟩,⟨-278156017892231,-231626663852621⟩,⟨-105626061115716,-67615014684402⟩,⟨2681824440319823,4643456191017813⟩,⟨471086395192817,2289146082625080⟩,⟨-650664713140921,1291155892866252⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13285129934,13913096824⟩,⟨169918282426,180552368294⟩,⟨40018635042,43616312752⟩,⟨464054829987,696505558423⟩,⟨72098375810,163367854706⟩,⟨10481153983,43857309451⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338037030881,371867042567⟩,⟨803775989005,2027086731400⟩,⟨-318315501365,348794204955⟩,⟨-47141195379204,5782797588893⟩,⟨-20852574687286,14453403880263⟩,⟨-16346867107156,12588421311928⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371867042567,-338037030881⟩,⟨-2027086731400,-803775989005⟩,⟨-348794204955,318315501365⟩,⟨-5782797588893,47141195379204⟩,⟨-14453403880263,20852574687286⟩,⟨-12588421311928,16346867107156⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58611249834,109112262536⟩,⟨-1293337102007,292167620762⟩,⟨-570195088547,398405724028⟩,⟨-30937445576813,33597857955262⟩,⟨-25667982204625,21150540987529⟩,⟨-20696296640569,21583876085628⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235653636828,238098748292⟩,⟨1567150200583,1575467340402⟩,⟨309799316355,311834218728⟩,⟨-3952509420833,-3938729622240⟩,⟨-1564882742808,-1557007182066⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1709604151033,-1622103728655⟩,⟨-5566003388119,-2633821008552⟩,⟨-573909066924,1510038997506⟩,⟨-21244268179399,103519924845317⟩,⟨-61245261699219,44813898251990⟩,⟨-51869907644119,55898175597982⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192312517941,-178304216124⟩,⟨-1873951304898,-1429779115729⟩,⟨-366000006546,-98688275548⟩,⟨-7327255141895,12244782861350⟩,⟨-7486889771081,6977654488572⟩,⟨-5872732062976,7164592176597⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43341118887,59794532168⟩,⟨-306801104315,145688224673⟩,⟨-56200690191,213145943180⟩,⟨-11279764562728,8306053239110⟩,⟨-9051772513889,5420647306506⟩,⟨-6221832373504,6816176040939⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2579469737,6410060157⟩,⟨-112010990702,39893891751⟩,⟨-35867099541,52266017463⟩,⟨-3827391076120,3889303894416⟩,⟨-3019017255005,2186017490192⟩,⟨-2246617322911,2303593588646⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1708442674,3251794694⟩,⟨-33369412452,15845870144⟩,⟨-6112702936,23182950748⟩,⟨-1308154520683,1074628899378⟩,⟨-1103471574440,646064879764⟩,⟨-698511039664,824004474703⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3017675979,5791808664⟩,⟨-83319681075,16214560110⟩,⟨-21544771706,35917300857⟩,⟨-2508605878857,2539469991573⟩,⟨-2149767745974,1391849365491⟩,⟨-1385131817149,1534443165818⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5791808664,-3017675979⟩,⟨-16214560110,83319681075⟩,⟨-35917300857,21544771706⟩,⟨-2539469991573,2508605878857⟩,⟨-1391849365491,2149767745974⟩,⟨-1534443165818,1385131817149⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3212338927,3392384178⟩,⟨-128225550812,123213572826⟩,⟨-71784400398,73810789169⟩,⟨-6366861067693,6397909773273⟩,⟨-4410866620496,4335785236166⟩,⟨-3781060488729,3688725405795⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48389293491,64593433521⟩,⟨-363078371533,229045640576⟩,⟨-23878475182,290826159680⟩,⟨-14823619916318,10695116816194⟩,⟨-10454120221048,6831222056213⟩,⟨-7347310871800,8311784915985⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3212338927,3392384178⟩,⟨-128225550812,123213572826⟩,⟨-71784400398,73810789169⟩,⟨-6366861067693,6397909773273⟩,⟨-4410866620496,4335785236166⟩,⟨-3781060488729,3688725405795⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (521/5120) u, BivariateJet2.affineZ (557/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000036

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000037Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2512559689728,-2512559631872⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2512559689728,-2512559631872⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-117994695616,-117994695552⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-117994695616,-117994695552⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2111997864256,-2111997825408⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2111997864256,-2111997825408⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-174150516224,-174150516160⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-174150516224,-174150516160⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨87423245312,87423245376⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-94979480256,-94979480192⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨87423368960,87423369024⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-94979626176,-94979626112⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7556257216,-7556257152⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7556234880,-7556234816⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨182402725504,182402725568⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨182402995136,182402995200⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1937847309184,1937847347840⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1937847309248,1937847347840⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2118902136896,-2118902097920⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2105131553984,-2105131515136⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-175333248064,-175333248000⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-172969938880,-172969938816⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨84850940352,84850940416⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-91950731648,-91950731584⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨90017864384,90017864448⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-98050194624,-98050194560⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8032330176,-8032330112⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7099791296,-7099791232⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨176801671936,176801672000⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨188068058944,188068059008⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1929798267136,1929798305728⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1945932159104,1945932197696⟩



end LaneCBRB2Cell000037Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000037
open Set LaneCBRB2Cell000037Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111883898060,111883898061⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨123480309760,123480309760⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111883898061,-111883898060⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437871915827,437871915828⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49175068671,49175068673⟩,⟨-123480309760,-123480309760⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161058966731,161058966734⟩,⟨976031318016,976031318016⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49175068670,49175068674⟩,⟨-123480309760,-123480309760⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2512559689728,-2512559631872⟩,⟨10805181447606,10805181447704⟩,⟨0,0⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-255672577803,-255672571913⟩,⟨-1413048061962,-1413048004086⟩,⟨0,0⟩,⟨10805181447410,10805181447900⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨255672571913,255672577803⟩,⟨1413048004086,1413048061962⟩,⟨0,0⟩,⟨-10805181447900,-10805181447410⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨987627729715,987627729716⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117994695616,-117994695552⟩,⟨-1224070348819,-1224070348816⟩,⟨0,0⟩,⟨-1362739766463,-1362739766455⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105987813504,-105987813446⟩,⟨-981516932226,-981516932158⟩,⟨0,0⟩,⟨1224070348810,1224070348825⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105987813446,105987813504⟩,⟨981516932158,981516932226⟩,⟨0,0⟩,⟨-1224070348825,-1224070348810⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨361660385359,361660391307⟩,⟨2394564936244,2394564994188⟩,⟨0,0⟩,⟨-12029251796725,-12029251796220⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2111997864256,-2111997825408⟩,⟨6663135899812,6663135899938⟩,⟨2989248426779,2989248426843⟩,⟨-40379181901739,-40379181900219⟩,⟨-25621211816387,-25621211815522⟩,⟨-8126886457267,-8126886456923⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309370256002,-309370250305⟩,⟨-898779286114,-898779251589⟩,⟨-403214733641,-403214718148⟩,⟨5914834504590,5914834505148⟩,⟨3666028013853,3666028053014⟩,⟨1190444832409,1190444832541⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309370250305,309370256002⟩,⟨898779251589,898779286114⟩,⟨403214718148,403214733641⟩,⟨-5914834505148,-5914834504590⟩,⟨-3666028053014,-3666028013853⟩,⟨-1190444832541,-1190444832409⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161058966734,-161058966731⟩,⟨-976031318016,-976031318016⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938452661042,938452661045⟩,⟨-976031318016,-976031318016⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-174150516224,-174150516160⟩,⟨-1143539602777,-1143539602771⟩,⟨-513020297044,-513020297040⟩,⟨-1189330599226,-1189330599214⟩,⟨754648553215,754648553227⟩,⟨-239369751562,-239369751557⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148640552082,-148640552026⟩,⟨-821438721156,-821438721089⟩,⟨-368517833321,-368517833288⟩,⟨1015114745028,1015114745054⟩,⟨1380766824442,1380766824528⟩,⟨204306325321,204306325332⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148640552026,148640552082⟩,⟨821438721089,821438721156⟩,⟨368517833288,368517833321⟩,⟨-1015114745054,-1015114745028⟩,⟨-1380766824528,-1380766824442⟩,⟨-204306325332,-204306325321⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨458010802331,458010808084⟩,⟨1720217972678,1720218007270⟩,⟨771732551436,771732566962⟩,⟨-6929949250202,-6929949249618⟩,⟨-5046794877542,-5046794838295⟩,⟨-1394751157873,-1394751157730⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨819671187690,819671199391⟩,⟨4114782908922,4114783001458⟩,⟨771732551436,771732566962⟩,⟨-18959201046927,-18959201045838⟩,⟨-5046794877542,-5046794838295⟩,⟨-1394751157873,-1394751157730⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98350137340,98350137348⟩,⟨-246960619520,-246960619520⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12292060308334,12292060309335⟩,⟨30865791454686,30865791459715⟩,⟨-109452780498212,-109452780480134⟩,⟨155010154233994,155010154271867⟩,⟨-274839743152899,-274839742972581⟩,⟨1949211255774615,1949211256259742⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9163566275755,9163566407314⟩,⟨69011511743906,69011513114388⟩,⟨-72967949384742,-72967948032190⟩,⟨134625021778936,134625028719259⟩,⟨-649259194305144,-649259181083821⟩,⟨1283871269352291,1283871293576822⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨90992774656,90992908544⟩,⟨-678521942955,-678519905539⟩,⟨717419513862,717421667134⟩,⟨8745524460987,8745574776803⟩,⟨-4262969711545,-4262901600740⟩,⟨-1366250898141,-1366161276755⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1190504402432,1190504536320⟩,⟨-678521942955,-678519905539⟩,⟨717419513862,717421667134⟩,⟨8745524460987,8745574776803⟩,⟨-4262969711545,-4262901600740⟩,⟨-1366250898141,-1366161276755⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨87423245312,87423369024⟩,⟨-626661072783,-626659120614⟩,⟨662585545387,662587608598⟩,⟨7719922284177,7719971887885⟩,⟨-3559505808579,-3559440108519⟩,⟨-1661113937681,-1661028537685⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨94658169854,94658314450⟩,⟨-732472039176,-732469610798⟩,⟨774462160663,774464727236⟩,⟨9827604090540,9827668455899⟩,⟨-5010816903024,-5010734435111⟩,⟨-1042555900199,-1042450663177⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-90992908544,-90992774656⟩,⟨678519905539,678521942955⟩,⟨-717421667134,-717419513862⟩,⟨-8745574776803,-8745524460987⟩,⟨4262901600740,4262969711545⟩,⟨1366161276755,1366250898141⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1008518719232,1008518853120⟩,⟨678519905539,678521942955⟩,⟨-717421667134,-717419513862⟩,⟨-8745574776803,-8745524460987⟩,⟨4262901600740,4262969711545⟩,⟨1366161276755,1366250898141⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-94979626176,-94979480192⟩,⟨739738799636,739741119083⟩,⟨-782150544151,-782148092764⟩,⟨-10032329144864,-10032269902543⟩,⟨5173738608806,5173816781090⟩,⟨933030041499,933131434287⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-87119354849,-87119209380⟩,⟨619906737738,619909221402⟩,⟨-655448672887,-655446047866⟩,⟨-7533610837605,-7533544164560⟩,⟨3411973331811,3412058038641⟩,⟨1758479694986,1758586996096⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7538815005,7539105070⟩,⟨-112565301438,-112560389396⟩,⟨119013487776,119018679370⟩,⟨2293993252935,2294124291339⟩,⟨-1598843571213,-1598676396470⟩,⟨715923794787,716136332919⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3769407502,3769552535⟩,⟨-56282650719,-56280194698⟩,⟨59506743888,59509339685⟩,⟨1146996626467,1147062145670⟩,⟨-799421785607,-799338198235⟩,⟨357961897393,358068166460⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3769552535,-3769407502⟩,⟨56280194698,56282650719⟩,⟨-59509339685,-59506743888⟩,⟨-1147062145670,-1146996626467⟩,⟨799338198235,799421785607⟩,⟨-358068166460,-357961897393⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758353831081,758353995378⟩,⟨56280194698,56282650719⟩,⟨-59509339685,-59506743888⟩,⟨-1147062145670,-1146996626467⟩,⟨799338198235,799421785607⟩,⟨-358068166460,-357961897393⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7530329675,7530351837⟩,⟨-112305651966,-112305149494⟩,⟨118743614000,118744145122⟩,⟨2284957733971,2284973221144⟩,⟨-1591045214066,-1591027586098⟩,⟨710081832669,710102619040⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7530351837,-7530329675⟩,⟨112305149494,112305651966⟩,⟨-118744145122,-118743614000⟩,⟨-2284973221144,-2284957733971⟩,⟨1591027586098,1591045214066⟩,⟨-710102619040,-710081832669⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091981275939,1091981298101⟩,⟨112305149494,112305651966⟩,⟨-118744145122,-118743614000⟩,⟨-2284973221144,-2284957733971⟩,⟨1591027586098,1591045214066⟩,⟨-710102619040,-710081832669⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7556257216,-7556234816⟩,⟨113079608545,113080116778⟩,⟨-119563010071,-119562472859⟩,⟨-2312360310276,-2312344565067⟩,⟨1614295790120,1614313682682⟩,⟨-728001030315,-727979969254⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3778128608,-3778117408⟩,⟨56539804272,56540058389⟩,⟨-59781505036,-59781236429⟩,⟨-1156180155138,-1156172282533⟩,⟨807147895060,807156841341⟩,⟨-364000515158,-363989984627⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3778117408,3778128608⟩,⟨-56540058389,-56539804272⟩,⟨59781236429,59781505036⟩,⟨1156172282533,1156180155138⟩,⟨-807156841341,-807147895060⟩,⟨363989984627,364000515158⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765901501024,765901531488⟩,⟨-56540058389,-56539804272⟩,⟨59781236429,59781505036⟩,⟨1156172282533,1156180155138⟩,⟨-807156841341,-807147895060⟩,⟨363989984627,364000515158⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272995318984,272995324526⟩,⟨28076287373,28076412992⟩,⟨-29686036281,-29685903500⟩,⟨-571243305286,-571239433492⟩,⟨397756896524,397761303517⟩,⟨-177525654760,-177520458167⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531803002048,1531803062976⟩,⟨-113080116778,-113079608544⟩,⟨119562472858,119563010072⟩,⟨2312344565066,2312360310276⟩,⟨-1614313682682,-1614295790120⟩,⟨727979969254,728001030316⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1198714149839,1198714308978⟩,⟨-806483753317,-806481117532⟩,⟨852716753857,852719539624⟩,⟨11480014346482,11480083860561⟩,⟨-6214322560509,-6214232913289⟩,⟨-410734454167,-410619734339⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1297916671902,1297916990180⟩,⟨-1612967506634,-1612962235064⟩,⟨1705433507714,1705439079248⟩,⟨22960028692968,22960167721111⟩,⟨-12428645121013,-12428465826580⟩,⟨-821468760602,-821239616410⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨182402725504,182402995200⟩,⟨-1366402456463,-1366397655654⟩,⟨1444733358386,1444738432515⟩,⟨17752179370932,17752313848563⟩,⟨-8733334194783,-8733167112237⟩,⟨-2594255786322,-2594048164872⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62759426565,62759532508⟩,⟨-463331830651,-463330113907⟩,⟨489892871815,489894686239⟩,⟨5867559077018,5867603889349⟩,⟨-2800655322261,-2800597268213⟩,⟨-1049620614679,-1049546138263⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380327991628,380328014478⟩,⟨11038535473,11038838797⟩,⟨-11671696381,-11671375762⟩,⟨-227485334764,-227475936258⟩,⟨159433385473,159444052592⟩,⟨-73030534176,-73017993856⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178639946557,3178640137530⟩,⟨-92258515924,-92255969768⟩,⟨97545013294,97547704630⟩,⟨1906514408240,1906593481187⟩,⟨-1338236741014,-1338147116920⟩,⟨616244063475,616349274152⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨181434752723,181435069902⟩,⟨-1344738170913,-1344732973181⟩,⟨1421826637836,1421832131367⟩,⟨17149431514510,17149569215261⟩,⟨-8255170945861,-8254994809948⟩,⟨-2912309244097,-2912084968760⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨363837478227,363838065102⟩,⟨-2711140627376,-2711130628835⟩,⟨2866559996222,2866570563882⟩,⟨34901610885442,34901883063824⟩,⟨-16988505140644,-16988161922185⟩,⟨-5506565030419,-5506133133632⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523050887855,523051114493⟩,⟨77635015736,77638420486⟩,⟨-82089437480,-82085838952⟩,⟨-1576539399687,-1576448174356⟩,⟨1096544731954,1096660806026⟩,⟨-487491655960,-487344395439⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360758026231,360758260707⟩,⟨80319493839,80323033723⟩,⟨-84927959812,-84924218454⟩,⟨-1625092826279,-1624997570759⟩,⟨1128158174138,1128279059904⟩,⟨-497684483483,-497531437891⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721516052462,721516521414⟩,⟨160638987678,160646067446⟩,⟨-169855919624,-169848436908⟩,⟨-3250185652558,-3249995141518⟩,⟨2256316348276,2256558119808⟩,⟨-995368966966,-995062875782⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524272650211,1524272733301⟩,⟨-774967284,-773956578⟩,⟨818327736,819396072⟩,⟨27371343922,27402576305⟩,⟨-23286096584,-23250576054⟩,⟨17877350214,17919197647⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000250618250,1000251322892⟩,⟨222188158455,222198648977⟩,⟨-234937315577,-234926227909⟩,⟨-4488055760920,-4487770594280⟩,⟨3112930159794,3113289144329⟩,⟨-1368419670429,-1367967445744⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67781406130,67781408883⟩,⟨13941999036,13942061700⟩,⟨-14741361354,-14741295116⟩,⟨-282231619344,-282229678114⟩,⟨196000279956,196002485938⟩,⟨-86551919352,-86549322719⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50530130161,50530132936⟩,⟨264056894952,264056957825⟩,⟨36585377665,36585430093⟩,⟨-1274822252065,-1274820282988⟩,⟨-210385308962,-210383353978⟩,⟨-171198818266,-171196784686⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134056955658,2134057125425⟩,⟨-315078922072,-315077493428⟩,⟨333140914982,333142425092⟩,⟨6466222374739,6466266711497⟩,⟨-4522609456904,-4522559202316⟩,⟨2054397713889,2054456711386⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2973097117517,2973097472288⟩,⟨-658436226208,-658433214509⟩,⟨696181250998,696184434442⟩,⟨13561395033072,13561488662154⟩,⟨-9502517245525,-9502411386123⟩,⟨4347517102098,4347641053364⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136634284289,136634308098⟩,⟨683754408966,683754804249⟩,⟨130921771512,130922073143⟩,⟨-3140158780912,-3140147186155⟩,⟨-860306684434,-860295505339⟩,⟨-216796307376,-216784767669⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8847893596003,8847895137780⟩,⟨-44277253248919,-44277212221030⟩,⟨-8477994966037,-8477972478972⟩,⟨646493311630298,646494877365128⟩,⟨140561367660043,140562399891041⟩,⟨30285152877969,30285988392688⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8049129100629,8049136173554⟩,⟨-38492074920173,-38491924490304⟩,⟨-9603196679044,-9603081235624⟩,⟨534117858663121,534122859913703⟩,⟨160669104981564,160673567961013⟩,⟨20162138144909,20166739259124⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16098258201258,16098272347108⟩,⟨-76984149840346,-76983848980608⟩,⟨-19206393358088,-19206162471248⟩,⟨1068235717326242,1068245719827406⟩,⟨321338209963128,321347135922026⟩,⟨40324276289818,40333478518248⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10805181447606,10805181447704⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230896,2087019636287702⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9705669819830,9705669819928⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230908,2087019636287687⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2394564936256,2394564994112⟩,⟨-12029251796733,-12029251796224⟩,⟨0,0⟩,⟨104822536628670,104822536664337⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7506106888238,7506106888379⟩,⟨-45487659260044,-45487659258333⟩,⟨-20406894880396,-20406894879581⟩,⟨551318326693318,551318326724400⟩,⟨298577532129775,298577532146211⟩,⟨110960679038256,110960679045019⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6406595260462,6406595260603⟩,⟨-45487659260044,-45487659258332⟩,⟨-20406894880397,-20406894879580⟩,⟨551318326693320,551318326724393⟩,⟨298577532129775,298577532146208⟩,⟨110960679038255,110960679045018⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1937847309184,1937847347840⟩,⟨-7806675502884,-7806675502383⟩,⟨-3502268723963,-3502268723729⟩,⟨39189851293661,39189851310871⟩,⟨26375860365164,26375860373606⟩,⟨7887516703837,7887516707436⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100498837339,100498837341⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137466682566,137466682570⟩,⟨690088738404,690088738410⟩,⟨309590965369,309590965374⟩,⟨-1732836851712,-1732836851712⟩,⟨-1554787388626,-1554787388618⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4332412245440,4332412341952⟩,⟨-19835927299617,-19835927298607⟩,⟨-3502268723963,-3502268723729⟩,⟨144012387922331,144012387975208⟩,⟨26375860365164,26375860373606⟩,⟨7887516703837,7887516707436⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨727674956454,727676130204⟩,⟨-5422281254752,-5422261257670⟩,⟨5733119992444,5733141127764⟩,⟨69803221770884,69803766127648⟩,⟨-33977010281288,-33976323844370⟩,⟨-11013130060838,-11012266267264⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5060087201894,5060088472156⟩,⟨-25258208554369,-25258188556277⟩,⟨2230851268481,2230872404035⟩,⟨213815609693215,213816154102856⟩,⟨-7601149916124,-7600463470764⟩,⟨-3125613357001,-3124749559828⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨462507960605,462508076721⟩,⟨1721600312211,1721603151901⟩,⟨203906855639,203908787500⟩,⟨-30812291449060,-30812207290956⟩,⟨1082069055595,1082148633028⟩,⟨-285690938069,-285611984271⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨223767796120,223767796122⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-223767796122,-223767796120⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨875743831654,875743831656⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1907233556649,1907233602736⟩,⟨-14370241087281,-14370240971140⟩,⟨0,0⟩,⟨131606519757458,131606519788094⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨807721928873,807721974960⟩,⟨-14370241087281,-14370240971140⟩,⟨0,0⟩,⟨131606519757458,131606519788094⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36124930664,36124932729⟩,⟨-733412300176,-733412289752⟩,⟨321668947845,321668966201⟩,⟨9113721952759,9113721980696⟩,⟨-6530558220472,-6530558128119⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨498632891269,498633009450⟩,⟨988188012035,988190862149⟩,⟨525575803484,525577753701⟩,⟨-21698569496301,-21698485310260⟩,⟨-5448489164877,-5448409495091⟩,⟨-285690938069,-285611984271⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504862395711,504862407910⟩,⟨2536208829314,2536208952001⟩,⟨0,0⟩,⟨3381169318170,3381172243620⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228957102141,228957161939⟩,⟨1603926747149,1603928395043⟩,⟨241328470360,241329371673⟩,⟨-3871107300098,-3871053344478⟩,⟨-1289451907707,-1289410708155⟩,⟨-131180618075,-131144361714⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-727676130204,-727674956454⟩,⟨5422261257670,5422281254752⟩,⟨-5733141127764,-5733119992444⟩,⟨-69803766127648,-69803221770884⟩,⟨33976323844370,33977010281288⟩,⟨11012266267264,11013130060838⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3604736115236,3604737385498⟩,⟨-14413666041947,-14413646043855⟩,⟨-9235409851727,-9235388716173⟩,⟨74208621794683,74209166204324⟩,⟨60352184209534,60352870654894⟩,⟨18899782971101,18900646768274⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450682923917,450683082746⟩,⟨460376162285,460379459882⟩,⟨-139668755470,-139665755271⟩,⟨-14496095860456,-14496000690264⟩,⟨-7406723666616,-7406617150789⟩,⟨-3981303907396,-3981183605550⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨322117933462,322117933468⟩,⟨1952062636032,1952062636032⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-322117933468,-322117933462⟩,⟨-1952062636032,-1952062636032⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨777393694308,777393694314⟩,⟨-1952062636032,-1952062636032⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1370126736848,1370126764190⟩,⟨-8960032311326,-8960032242297⟩,⟨-4019693263549,-4019693232570⟩,⟨55428410993241,55428411007404⟩,⟨34960152936311,34960153020567⟩,⟨11155758522829,11155758525804⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1370126764190,-1370126736848⟩,⟨8960032242297,8960032311326⟩,⟨4019693232570,4019693263549⟩,⟨-55428411007404,-55428410993241⟩,⟨-34960153020567,-34960152936311⟩,⟨-11155758525804,-11155758522829⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-270615136414,-270615109072⟩,⟨8960032242297,8960032311326⟩,⟨4019693232570,4019693263549⟩,⟨-55428411007404,-55428410993241⟩,⟨-34960153020567,-34960152936311⟩,⟨-11155758525804,-11155758522829⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12103117040,-12103115815⟩,⟨431123988432,431123994623⟩,⟨72008263041,72008275332⟩,⟨-4491513253292,-4491513236951⟩,⟨1823873433676,1823873495894⟩,⟨2702687526786,2702687551643⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438579806877,438579966931⟩,⟨891500150717,891503454505⟩,⟨-67660492429,-67657479939⟩,⟨-18987609113748,-18987513927215⟩,⟨-5582850232940,-5582743654895⟩,⟨-1278616380610,-1278496053907⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100498837341,-100498837339⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4494756674,4494756675⟩,⟨27880683313,27880683318⟩,⟨40022876823,40022876824⟩,⟨-295050412037,-295050412027⟩,⟨248259301866,248259301870⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9788879404,9788879644⟩,⟨11544713607,11544715100⟩,⟨87163587057,87163589166⟩,⟨-824123264338,-824123248412⟩,⟨102798145600,102798158703⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1474891176502,1474891197557⟩,⟨-7404014341185,-7404013963278⟩,⟨-1388631913596,-1388631846010⟩,⟨108451509128416,108451516631595⟩,⟨23023024798395,23023026319433⟩,⟨5124507209872,5124507498989⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13130858734,13130859244⟩,⟨-50431307531,-50431300326⟩,⟨104558834928,104558840333⟩,⟨-295429232725,-295429077061⟩,⟨-258665870992,-258665786121⟩,⟨-174543947794,-174543928056⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13130859244,-13130858734⟩,⟨50431300326,50431307531⟩,⟨-104558840333,-104558834928⟩,⟨295429077061,295429232725⟩,⟨258665786121,258665870992⟩,⟨174543928056,174543947794⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113629696585,-113629696073⟩,⟨-825312531330,-825312524123⟩,⟨-104558840333,-104558834928⟩,⟨2494452332613,2494452488277⟩,⟨258665786121,258665870992⟩,⟨174543928056,174543947794⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86669183020,86669184757⟩,⟨-566778721577,-566778717183⟩,⟨615095458521,615095473942⟩,⟨3506197615018,3506197616044⟩,⟨-3473827454350,-3473827414986⟩,⟨-2436737355553,-2436737355169⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨116258537046,116258541037⟩,⟨-1343902871938,-1343902813702⟩,⟨715633421896,715633461883⟩,⟨20885216773540,20885218053618⟩,⟨-6271201999218,-6271201367977⟩,⟨-4418387137098,-4418386944460⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-116258541037,-116258537046⟩,⟨1343902813702,1343902871938⟩,⟨-715633461883,-715633421896⟩,⟨-20885218053618,-20885216773540⟩,⟨6271201367977,6271201999218⟩,⟨4418386944460,4418387137098⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨983253086739,983253090730⟩,⟨1343902813702,1343902871938⟩,⟨-715633461883,-715633421896⟩,⟨-20885218053618,-20885216773540⟩,⟨6271201367977,6271201999218⟩,⟨4418386944460,4418387137098⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122931432958,122931433461⟩,⟨785142896029,785142905827⟩,⟨187383661235,187383667367⟩,⟨-2473838718533,-2473838479006⟩,⟨-677081226019,-677081099916⟩,⟨-162475618148,-162475570252⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11743129861,11743129968⟩,⟨170584846784,170584849044⟩,⟨21611392430,21611393646⟩,⟨723406416155,723406472293⟩,⟨103503392048,103503419318⟩,⟨-16190507937,-16190501636⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171934458733,171934611383⟩,⟨1675365667051,1675371115582⟩,⟨111288138218,111290901881⟩,⟨-1886878759400,-1886668025755⟩,⟨454461933640,454600887187⟩,⟨-561394561328,-561286855302⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171934611383,-171934458733⟩,⟨-1675371115582,-1675365667051⟩,⟨-111290901881,-111288138218⟩,⟨1886668025755,1886878759400⟩,⟨-454600887187,-454461933640⟩,⟨561286855302,561394561328⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57022490758,57022703206⟩,⟨-71444368433,-71437272008⟩,⟨130037568479,130041233455⟩,⟨-1984439274343,-1984174585078⟩,⟨-1744052794894,-1743872641795⟩,⟨430106237227,430250199614⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28372566100967,28372591598463⟩,⟨-249981457240898,-249980823835808⟩,⟨-85128280426632,-85127827760004⟩,⟨3549704989583266,3549727432975488⟩,⟨1334105218602350,1334123898705136⟩,⟨308907924609173,308925717027472⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13744408724,13744408837⟩,⟨175566567642,175566570552⟩,⟨41901042984,41901044528⟩,⟨568137379311,568137463125⟩,⟨116212294896,116212335816⟩,⟨27538182360,27538197401⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354670323795,354670645443⟩,⟨1405557391584,1405569481589⟩,⟨17100521279,17107200095⟩,⟨-20798927583534,-20798427724531⟩,⟨-3443743479279,-3443409086262⟩,⟨-1916161694933,-1915903482682⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354670645443,-354670323795⟩,⟨-1405569481589,-1405557391584⟩,⟨-17107200095,-17100521279⟩,⟨20798427724531,20798927583534⟩,⟨3443409086262,3443743479279⟩,⟨1915903482682,1916161694933⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83909161434,83909643136⟩,⟨-514069330872,-514053937079⟩,⟨-84767692524,-84758001218⟩,⟨1810818610783,1811413656319⟩,⟨-2139441146678,-2139000175616⟩,⟨637287102072,637665641026⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237965519905,237965519911⟩,⟨1565832570058,1565832570066⟩,⟨309590965369,309590965374⟩,⟨-3931860107264,-3931860107264⟩,⟨-1554787388626,-1554787388618⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1663685727494,-1663684258086⟩,⟨-4127700357127,-4127658505104⟩,⟨453995850291,454021144723⟩,⟨41694302250743,41695823504733⟩,⟨-7685303858057,-7684174256798⟩,⟨2040105971830,2041103636616⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186009193667,-186009028617⟩,⟨-1649509766383,-1649504021101⟩,⟨-232773502404,-232770414437⟩,⟨2509802607965,2510036225330⟩,⟨-214029811565,-213877194750⟩,⟨628682763162,628803224747⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51956326238,51956491294⟩,⟨-83677196325,-83671451035⟩,⟨76817462965,76820550937⟩,⟨-1422057499299,-1421823881934⟩,⟨-1768817200191,-1768664583368⟩,⟨279924623953,280045085540⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4351667832,4351709028⟩,⟨-32112888532,-32111417990⟩,⟨5527599890,5528455542⟩,⟨9266857907,9327773192⟩,⟨-299346442849,-299303936620⟩,⟨45823036083,45856823389⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2455144418,2455160018⟩,⟨-7908190170,-7907622068⟩,⟨7259865316,7260180222⟩,⟨-121661662642,-121637408077⟩,⟨-178860616480,-178844389100⟩,⟨37188833994,37201165644⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4327098398,4327125980⟩,⟨-31369839159,-31368726857⟩,⟨4974827174,4975432132⟩,⟨-14625135627,-14573760329⟩,⟨-282699401008,-282666374884⟩,⟨36904630405,36928483836⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4327125980,-4327098398⟩,⟨31368726857,31369839159⟩,⟨-4975432132,-4974827174⟩,⟨14573760329,14625135627⟩,⟨282666374884,282699401008⟩,⟨-36928483836,-36904630405⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨24541852,24610630⟩,⟨-744161675,-741578831⟩,⟨552167758,553628368⟩,⟨23840618236,23952908819⟩,⟨-16680067965,-16604535612⟩,⟨8894552247,8952192984⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57022490758,57022703206⟩,⟨-71444368433,-71437272008⟩,⟨130037568479,130041233455⟩,⟨-1984439274343,-1984174585078⟩,⟨-1744052794894,-1743872641795⟩,⟨430106237227,430250199614⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨24541852,24610630⟩,⟨-744161675,-741578831⟩,⟨552167758,553628368⟩,⟨23840618236,23952908819⟩,⟨-16680067965,-16604535612⟩,⟨8894552247,8952192984⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111669149696,112098646426⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121547574476,125413045044⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112098646426,-111669149696⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437657167462,438086664192⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨48381632183,49969260135⟩,⟨-125413045044,-121547574476⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160050781879,162067906561⟩,⟨974098582732,977964053300⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47952135453,50398756865⟩,⟨-125413045044,-121547574476⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2514672104640,-2510451267584⟩,⟨10784481866270,10825960642718⟩,⟨0,0⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-256378679420,-254967706864⟩,⟨-1419373165097,-1406710748927⟩,⟨0,0⟩,⟨10701364779618,10908759273099⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨254967706864,256378679420⟩,⟨1406710748927,1419373165097⟩,⟨0,0⟩,⟨-10908759273099,-10701364779618⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨987412981350,987842478080⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-118233797888,-117755645312⟩,⟨-1224336566816,-1223804246568⟩,⟨0,0⟩,⟨-1363332584190,-1362147335310⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106225677790,-105750089286⟩,⟨-982234238937,-980799781353⟩,⟨0,0⟩,⟨1222739374527,1225400975868⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105750089286,106225677790⟩,⟨980799781353,982234238937⟩,⟨0,0⟩,⟨-1225400975868,-1222739374527⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨360717796150,362604357210⟩,⟨2387510530280,2401607404034⟩,⟨0,0⟩,⟨-12134160248967,-11924104154145⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2118902136896,-2105131515136⟩,⟨6608542931420,6718385474451⟩,⟨2969182207723,3009553440463⟩,⟨-41051592582615,-39720216297090⟩,⟨-25942771738609,-25305454281826⟩,⟨-8237668144832,-8018144383333⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312325968057,-306434180816⟩,⟨-922689340851,-874725588841⟩,⟨-412040058123,-394333137837⟩,⟨5658511268829,6169491194396⟩,⟨3542189218619,3789018552693⟩,⟨1149515918081,1231073999506⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306434180816,312325968057⟩,⟨874725588841,922689340851⟩,⟨394333137837,412040058123⟩,⟨-6169491194396,-5658511268829⟩,⟨-3789018552693,-3542189218619⟩,⟨-1231073999506,-1149515918081⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162067906561,-160050781879⟩,⟨-977964053300,-974098582732⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937443721215,939460845897⟩,⟨-977964053300,-974098582732⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175333248064,-172969938816⟩,⟨-1147037228813,-1140050405496⟩,⟨-513824318572,-512218414109⟩,⟨-1196617089848,-1182083839987⟩,⟨750795375874,758494483335⟩,⟨-240120635096,-238622036479⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149810804524,-147474186725⟩,⟨-826827811581,-816056381649⟩,⟨-370179164284,-366858128864⟩,⟨997595693688,1032626897911⟩,⟨1372381965223,1389159330292⟩,⟨202606484450,206004582259⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147474186725,149810804524⟩,⟨816056381649,826827811581⟩,⟨366858128864,370179164284⟩,⟨-1032626897911,-997595693688⟩,⟨-1389159330292,-1372381965223⟩,⟨-206004582259,-202606484450⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨453908367541,462136772581⟩,⟨1690781970490,1749517152432⟩,⟨761191266701,782219222407⟩,⟨-7202118092307,-6656106962517⟩,⟨-5178177882985,-4914571183842⟩,⟨-1437078581765,-1352122402531⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨814626163691,824741129791⟩,⟨4078292500770,4151124556466⟩,⟨761191266701,782219222407⟩,⟨-19336278341274,-18580211116662⟩,⟨-5178177882985,-4914571183842⟩,⟨-1437078581765,-1352122402531⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95904270906,100797513730⟩,⟨-250826090088,-243095148952⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11993607529377,12605547262849⟩,⟨28925195681269,32968293314685⟩,⟨-115163216372479,-104151146287563⟩,⟨139518813359599,172449214844708⟩,⟨-340735612577460,-213329235893401⟩,⟨1808873809893116,2104242858910495⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8886041987781,9455391856315⟩,⟨65917139032608,72320748828261⟩,⟨-78080494744248,-68197502847666⟩,⟨96262849576091,175617228035763⟩,⟨-729716420448110,-574525457599182⟩,⟨1159855862397257,1419431029210381⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨88210847744,93805435136⟩,⟨-755919591552,-608884084567⟩,⟨629948063593,816122297564⟩,⟨6516875697452,11246745216462⟩,⟨-7795505631487,-1014202897783⟩,⟨-5895969575367,3432244452835⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1187722475520,1193317062912⟩,⟨-755919591552,-608884084567⟩,⟨629948063593,816122297564⟩,⟨6516875697452,11246745216462⟩,⟨-7795505631487,-1014202897783⟩,⟨-5895969575367,3432244452835⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨84850940352,90017864448⟩,⟨-699778271193,-561020328759⟩,⟨580428489914,755509788149⟩,⟨5559220634048,10125203937064⟩,⟨-6920381219571,-453637296541⟩,⟨-5977217435550,2870929168050⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨91658302085,97697787726⟩,⟨-821367956266,-653017960603⟩,⟨675608724551,886783079978⟩,⟨7129498974898,12872022871138⟩,⟨-9187854685800,-1211154651076⟩,⟨-6304779652103,4518432294233⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-93805435136,-88210847744⟩,⟨608884084567,755919591552⟩,⟨-816122297564,-629948063593⟩,⟨-11246745216462,-6516875697452⟩,⟨1014202897783,7795505631487⟩,⟨-3432244452835,5895969575367⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1005706192640,1011300780032⟩,⟨608884084567,755919591552⟩,⟨-816122297564,-629948063593⟩,⟨-11246745216462,-6516875697452⟩,⟨1014202897783,7795505631487⟩,⟨-3432244452835,5895969575367⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-98050194624,-91950731584⟩,⟨661994081452,826426631017⟩,⟨-892244636084,-684895368906⟩,⟨-12916932715117,-7483884533492⟩,⟨1515028761974,9193255798518⟩,⟨-4476430055419,6019278236217⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-90183892377,-84105904690⟩,⟨538105709106,709204468478⟩,⟨-767980519545,-553684516222⟩,⟨-10602450240049,-4706106938321⟩,⟨-536244841135,7612330848323⟩,⟨-3858277658178,7166995143866⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1474409708,13591883036⟩,⟨-283262247160,56186507875⟩,⟨-92371794994,333098563756⟩,⟨-3472951265151,8165915932817⟩,⟨-9724099526935,6401176197247⟩,⟨-10163057310281,11685427438099⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨737204854,6795941518⟩,⟨-141631123580,28093253938⟩,⟨-46185897497,166549281878⟩,⟨-1736475632576,4082957966409⟩,⟨-4862049763468,3200588098624⟩,⟨-5081528655141,5842713719050⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6795941518,-737204854⟩,⟨-28093253938,141631123580⟩,⟨-166549281878,46185897497⟩,⟨-4082957966409,1736475632576⟩,⟨-3200588098624,4862049763468⟩,⟨-5842713719050,5081528655141⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755327442098,761386198026⟩,⟨-28093253938,141631123580⟩,⟨-166549281878,46185897497⟩,⟨-4082957966409,1736475632576⟩,⟨-3200588098624,4862049763468⟩,⟨-5842713719050,5081528655141⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7076918027,8003061941⟩,⟨-128983385756,-97698250606⟩,⟨101078062878,139255839254⟩,⟨1720034485248,2958441214627⟩,⟨-2452331740096,-860434824830⟩,⟨-284197865298,1797195707646⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8003061941,-7076918027⟩,⟨97698250606,128983385756⟩,⟨-139255839254,-101078062878⟩,⟨-2958441214627,-1720034485248⟩,⟨860434824830,2452331740096⟩,⟨-1797195707646,284197865298⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091508565835,1092434709749⟩,⟨97698250606,128983385756⟩,⟨-139255839254,-101078062878⟩,⟨-2958441214627,-1720034485248⟩,⟨860434824830,2452331740096⟩,⟨-1797195707646,284197865298⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8032330176,-7099791232⟩,⟨98331151139,129929106256⟩,⟨-140276878523,-101732858225⟩,⟨-2995486534830,-1739970985166⟩,⟨875106959335,2486889003992⟩,⟨-1828269621382,276868752466⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4016165088,-3549895616⟩,⟨49165575569,64964553128⟩,⟨-70138439262,-50866429112⟩,⟨-1497743267415,-869985492583⟩,⟨437553479667,1243444501996⟩,⟨-914134810691,138434376233⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3549895616,4016165088⟩,⟨-64964553128,-49165575569⟩,⟨50866429112,70138439262⟩,⟨869985492583,1497743267415⟩,⟨-1243444501996,-437553479667⟩,⟨-138434376233,914134810691⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765673279232,766139567968⟩,⟨-64964553128,-49165575569⟩,⟨50866429112,70138439262⟩,⟨869985492583,1497743267415⟩,⟨-1243444501996,-437553479667⟩,⟨-138434376233,914134810691⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272877141458,273108677438⟩,⟨24424562651,32245846439⟩,⟨-34813959814,-25269515719⟩,⟨-739610303657,-430008621312⟩,⟨215108706207,613082935024⟩,⟨-449298926912,71049466325⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531346558464,1532279135936⟩,⟨-129929106256,-98331151138⟩,⟨101732858224,140276878524⟩,⟨1739970985166,2995486534830⟩,⟨-2486889003992,-875106959334⟩,⟨-276868752466,1828269621382⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1195416678682,1202066596052⟩,⟨-903510087695,-719736605020⟩,⟨744635460380,975467148732⟩,⟨8570006471371,14800842234909⟩,⟨-10783931187466,-2095507550945⟩,⟨-6119455936635,5685544574878⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1291321729588,1304621564328⟩,⟨-1807020175390,-1439473210040⟩,⟨1489270920760,1950934297463⟩,⟨17140012942748,29601684469809⟩,⟨-21567862374927,-4191015101891⟩,⟨-12234191608619,11371089149752⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨176801671936,188068059008⟩,⟨-1538609355781,-1213162173297⟩,⟨1255130789691,1661146789323⟩,⟨12292231270580,23866154925739⟩,⟨-16979352487003,-1207574788604⟩,⟨-12926619131436,8249276990241⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨60597880284,64958079395⟩,⟨-525853505438,-406199514103⟩,⟨418543851692,569086061187⟩,⟨3933790067248,7974886025233⟩,⟨-5723871535751,-62284383349⟩,⟨-4828541320081,2878846537764⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380050070321,380604186177⟩,⟨1744141251,20533947720⟩,⟨-23268633158,-350658557⟩,⟨-606515165040,140787735957⟩,⟨-313607805523,645435827912⟩,⟨-703797757106,548463897800⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176333481136,3180964599201⟩,⟨-171866198378,-14555736517⟩,⟨2926422134,194755123411⟩,⟨-1178239759577,5095016691619⟩,⟨-5423250417895,2624825547946⟩,⟨-4590558796652,5914534154666⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨175058699853,187928299954⟩,⟨-1531484925476,-1174255124574⟩,⟨1209275237152,1657912010437⟩,⟨11305308337534,23537309528793⟩,⟨-17062062378553,-31480586689⟩,⟨-14238288000120,8879733790783⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨351860371789,375996358962⟩,⟨-3070094281257,-2387417297871⟩,⟨2464406026843,3319058799760⟩,⟨23597539608114,47403464454532⟩,⟨-34041414865556,-1239055375293⟩,⟨-27164907131556,17129010781024⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518884503241,527242211815⟩,⟨-38907848296,196152509862⟩,⟨-230662998572,63965316982⟩,⟨-5661944163630,2441425667746⟩,⟨-4475572797280,6745611143884⟩,⟨-8105878464927,7088136855951⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356456170791,365102953850⟩,⟨-40414168354,203746567947⟩,⟨-239593132630,66441738686⟩,⟨-5888664467130,2573846050784⟩,⟨-4693413414909,7019127272432⟩,⟨-8434231900104,7414964323212⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712912341582,730205907700⟩,⟨-80828336708,407493135894⟩,⟨-479186265260,132883477372⟩,⟨-11777328934260,5147692101568⟩,⟨-9386826829818,14038254544864⟩,⟨-16868463800208,14829928646424⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523343496523,1525202217909⟩,⟨-32230855650,30652234618⟩,⟨-37522981030,39198815646⟩,⟨-1218470229461,1275452049582⟩,⟨-1626454179162,1577224780762⟩,⟨-2074064460112,2112467486680⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨987720685898,1012914863127⟩,⟨-133527209641,585616251057⟩,⟨-689629320723,210363742710⟩,⟨-17170177740236,8010461153784⟩,⟨-14128485451903,20549390366558⟩,⟨-24810905952714,22007168168639⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67722734757,67837708859⟩,⟨12123391274,16019149324⟩,⟨-17294941284,-12542792710⟩,⟨-366339795785,-211547974273⟩,⟨104729484972,303445763484⟩,⟨-222042012464,37500717698⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50175650912,50884908567⟩,⟨260178379007,268132162466⟩,⟨33911514800,38968458073⟩,⟨-1377865233884,-1180196937307⟩,⟨-298792275303,-110218652334⟩,⟨-279826208230,-72519443241⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132785341127,2135383829614⟩,⟨-362138341492,-273901732516⟩,⟨283377198364,390979647304⟩,⟨4864282519056,8379726008481⟩,⟨-6964608808014,-2455809480164⟩,⟨-752862685395,5131545546389⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2970440156857,2975870383428⟩,⟨-757013856389,-572215606706⟩,⟨592011061773,817303711492⟩,⟨10198848987250,17581166919683⟩,⟨-14628118700715,-5168513146345⟩,⟨-1534462441949,10801803337465⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135554517660,137721956315⟩,⟨667863536437,699597213133⟩,⟨118631456382,143294077951⟩,⟨-3633043870691,-2645578717744⟩,⟨-1372417272963,-351965999245⟩,⟨-791856585122,361917263636⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8778018058715,8918373511143⟩,⟨-46027748552983,-42567781786313⟩,⟨-9427572988068,-7561242189088⟩,⟨581475012895665,714123093211141⟩,⟨95767734839479,187605237144040⟩,⟨-10784919907549,72029348185568⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7885528264322,8215968668406⟩,⟨-43485703058713,-33489717827261⟩,⟨-14278794578125,-5086160754723⟩,⟨334053443225758,734033249902875⟩,⟨-42395956432513,369524236068810⟩,⟨-214789516744550,256687421388623⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15771056528644,16431937336812⟩,⟨-86971406117426,-66979435654522⟩,⟨-28557589156250,-10172321509446⟩,⟨668106886451516,1468066499805750⟩,⟨-84791912865026,739048472137620⟩,⟨-429579033489100,513374842777246⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10784481866270,10825960642718⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533866,2099083303790624⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9684970238494,9726449014942⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533869,2099083303790615⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2392217469760,2396916459264⟩,⟨-12101371604921,-11957606413725⟩,⟨0,0⟩,⟨101381360168522,108260423343400⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7459378264749,7553389027044⟩,⟨-46153744844711,-44834106578763⟩,⟨-20674931814479,-20143718961091⟩,⟨538944947252543,564029776717143⟩,⟨292751417148157,304551585003680⟩,⟨108794432774915,113181726507896⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6359866636973,6453877399268⟩,⟨-46153744844712,-44834106578763⟩,⟨-20674931814479,-20143718961090⟩,⟨538944947252550,564029776717142⟩,⟨292751417148159,304551585003682⟩,⟨108794432774915,113181726507897⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1929798267136,1945932197696⟩,⟨-7979189190415,-7638140369645⟩,⟨-3574340348800,-3431774707525⟩,⟨33911871433514,44450052159033⟩,⟨23935354049882,28811716455764⟩,⟨6915088193431,8855985420478⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100284130918,100713627649⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136459312259,138476436942⟩,⟨686364740809,693811395629⟩,⟨308572612196,310608717220⟩,⟨-1739706366693,-1725980926276⟩,⟨-1558725168992,-1550849608250⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4322015736896,4342848656960⟩,⟨-20080560795336,-19595746783370⟩,⟨-3574340348800,-3431774707525⟩,⟨135293231602036,152710475502433⟩,⟨23935354049882,28811716455764⟩,⟨6915088193431,8855985420478⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨703720743578,751992717924⟩,⟨-6140188562514,-4774834595742⟩,⟨4928812053686,6638117599520⟩,⟨47195079216228,94806928909064⟩,⟨-68082829731112,-2478110750586⟩,⟨-54329814263112,34258021562048⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5025736480474,5094841374884⟩,⟨-26220749357850,-24370581379112⟩,⟨1354471704886,3206342891995⟩,⟨182488310818264,247517404411497⟩,⟨-44147475681230,26333605705178⟩,⟨-47414726069681,43114006982526⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458386798679,466679882412⟩,⟨1599175809500,1837162518724⟩,⟨123538500499,293696233839⟩,⟨-35334629036512,-26181782373377⟩,⟨-2965556566658,4967173557150⟩,⟨-4343118295275,3949178831767⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨223338299392,224197292852⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-224197292852,-223338299392⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨875314334924,876173328384⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1904429376315,1910042803476⟩,⟨-14437113416200,-14303810670437⟩,⟨0,0⟩,⟨128539492851485,134675511271456⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨804917748539,810531175700⟩,⟨-14437113416200,-14303810670437⟩,⟨0,0⟩,⟨128539492851485,134675511271456⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35104244403,37152643614⟩,⟨-754210988583,-712801981308⟩,⟨320394994437,322946015318⟩,⟨8768374898668,9466642094215⟩,⟨-6562818552468,-6498504886492⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨493491043082,503832526026⟩,⟨844964820917,1124360537416⟩,⟨443933494936,616642249157⟩,⟨-26566254137844,-16715140279162⟩,⟨-9528375119126,-1531331329342⟩,⟨-4343118295275,3949178831767⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504367106722,505357825907⟩,⟨2516159178967,2556424289217⟩,⟨0,0⟩,⟨2234856254543,4531068346710⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226373822072,231571639210⟩,⟨1516923002596,1688216892904⟩,⟨203640822672,283421274068⟩,⟨-7340032342921,-362872156036⟩,⟨-3363522042941,731275642002⟩,⟨-1996185182504,1815122621829⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-751992717924,-703720743578⟩,⟨4774834595742,6140188562514⟩,⟨-6638117599520,-4928812053686⟩,⟨-94806928909064,-47195079216228⟩,⟨2478110750586,68082829731112⟩,⟨-34258021562048,54329814263112⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3570023018972,3639127913382⟩,⟨-15305726199594,-13455558220856⟩,⟨-10212457948320,-8360586761211⟩,⟨40486302692972,105515396286205⟩,⟨26413464800468,96894546186876⟩,⟨-27342933368617,63185799683590⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443072063642,458324818302⟩,⟨300911319908,626398282819⟩,⟨-284283906276,-9581587201⟩,⟨-20049679269543,-9114261936948⟩,⟨-12648932819162,-1827525920342⟩,⟨-10369085065600,2133851547332⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨320101563758,324135813122⟩,⟨1948197165464,1955928106600⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-324135813122,-320101563758⟩,⟨-1955928106600,-1948197165464⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨775375814654,779410064018⟩,⟨-1955928106600,-1948197165464⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1360894114894,1379411641011⟩,⟨-9117833393908,-8805779385062⟩,⟨-4084404945884,-3956388533234⟩,⟨50982318293171,59897737455412⟩,⟨32900164504860,37032439127198⟩,⟨10340550336730,11974341326903⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1379411641011,-1360894114894⟩,⟨8805779385062,9117833393908⟩,⟨3956388533234,4084404945884⟩,⟨-59897737455412,-50982318293171⟩,⟨-37032439127198,-32900164504860⟩,⟨-11974341326903,-10340550336730⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-279900013235,-261382487118⟩,⟨8805779385062,9117833393908⟩,⟨3956388533234,4084404945884⟩,⟨-59897737455412,-50982318293171⟩,⟨-37032439127198,-32900164504860⟩,⟨-11974341326903,-10340550336730⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12829889523,-11399468737⟩,⟨412934544475,449863893049⟩,⟨61024198425,83176030668⟩,⟨-4825562434278,-4170354517329⟩,⟨1603147202057,2040571380987⟩,⟨2600783482662,2803785906052⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430242174119,446925349565⟩,⟨713845864383,1076262175868⟩,⟨-223259707851,73594443467⟩,⟨-24875241703821,-13284616454277⟩,⟨-11045785617105,213045460645⟩,⟨-7768301582938,4937637453384⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100713627649,-100284130918⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4373612891,4616451073⟩,⟨26686747179,29075412092⟩,⟨39917784923,40128086017⟩,⟨-300674554269,-289430799641⟩,⟨247702508009,248816179610⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9515709429,10063784030⟩,⟨7253322911,15819198095⟩,⟨86849488477,87478538129⟩,⟨-892208569761,-755627939850⟩,⟨97273538155,108293929972⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1465824579308,1484025278709⟩,⟨-7562209577162,-7248409438176⟩,⟨-1424988726468,-1352876469937⟩,⟨104708731906927,112295526077840⟩,⟨22114516304363,23955967947120⟩,⟨4900410096638,5354564196886⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12685960219,13583221426⟩,⟨-59546750863,-41379888147⟩,⟨102741374685,106362479116⟩,⟨-515627458823,-75169913136⟩,⟨-301090006656,-216036719041⟩,⟨-184337279936,-164715021237⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13583221426,-12685960219⟩,⟨41379888147,59546750863⟩,⟨-106362479116,-102741374685⟩,⟨75169913136,515627458823⟩,⟨216036719041,301090006656⟩,⟨164715021237,184337279936⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114296849075,-112970091137⟩,⟨-834793440237,-815767584061⟩,⟨-106362479116,-102741374685⟩,⟨2274193168688,2714650714375⟩,⟨216036719041,301090006656⟩,⟨164715021237,184337279936⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨84162773330,89196477082⟩,⟨-587703196608,-546449373552⟩,⟨604311692928,625665070051⟩,⟨3167716862044,3857727459131⟩,⟨-3701894658892,-3241783736619⟩,⟨-2546720165324,-2326079029189⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨112202416685,120389656115⟩,⟨-1406705317444,-1283338100300⟩,⟨690043597181,740911622669⟩,⟨19442879510556,22400854386225⟩,⟨-6934549778847,-5600601511929⟩,⟨-4683985336385,-4153783894676⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-120389656115,-112202416685⟩,⟨1283338100300,1406705317444⟩,⟨-740911622669,-690043597181⟩,⟨-22400854386225,-19442879510556⟩,⟨5600601511929,6934549778847⟩,⟨4153783894676,4683985336385⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨979121971661,987309211091⟩,⟨1283338100300,1406705317444⟩,⟨-740911622669,-690043597181⟩,⟨-22400854386225,-19442879510556⟩,⟨5600601511929,6934549778847⟩,⟨4153783894676,4683985336385⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121517869838,124345262259⟩,⟨770485924351,800175186535⟩,⟨181472771926,193271237420⟩,⟨-2781182570403,-2174721389437⟩,⟨-811941775623,-541045521071⟩,⟨-216564036256,-107663621978⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11607191019,11881429336⟩,⟨167633221858,173557527610⟩,⟨21112468786,22113265410⟩,⟨646106360749,800290360227⟩,⟨89857065104,117115654604⟩,⟨-19123727165,-13269334880⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166489977072,177565109263⟩,⟨1464657909276,1886695203242⟩,⟨-5765322279,223091513057⟩,⟨-11136271719781,7400642275117⟩,⟨-5884353070302,6899489583005⟩,⟨-6076566854986,4966595812357⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177565109263,-166489977072⟩,⟨-1886695203242,-1464657909276⟩,⟨-223091513057,5765322279⟩,⟨-7400642275117,11136271719781⟩,⟨-6899489583005,5884353070302⟩,⟨-4966595812357,6076566854986⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48808712809,65081662138⟩,⟨-369772200646,223558983628⟩,⟨-19450690385,289186596347⟩,⟨-14740674618038,10773399563745⟩,⟨-10263011625946,6615628712304⟩,⟨-6962780994861,7891689476815⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27680432649395,29081489569058⟩,⟨-273170368216836,-227117509351257⟩,⟨-103959308816814,-67078182226056⟩,⟨2589635383559204,4524809764153225⟩,⟨472975863143167,2228537004825731⟩,⟨-597588218239754,1226601598231042⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13430137814,14062374473⟩,⟨170307991114,180985795712⟩,⟨40112690254,43714613102⟩,⟨450785016284,683963332289⟩,⟨70687935280,161715705416⟩,⟨10920584946,44148177427⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338106497322,371942220730⟩,⟨793784115459,2012818258288⟩,⟨-319758427918,336892147364⟩,⟨-46950689049039,5602840526387⟩,⟨-20416238411655,14103725991520⟩,⟨-15634491061072,11961176889574⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371942220730,-338106497322⟩,⟨-2012818258288,-793784115459⟩,⟨-336892147364,319758427918⟩,⟨-5602840526387,46950689049039⟩,⟨-14103725991520,20416238411655⟩,⟨-11961176889574,15634491061072⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58299953389,108818852243⟩,⟨-1298972393905,282478060409⟩,⟨-560151855215,393352871385⟩,⟨-30478082230208,33666072594762⟩,⟨-25149511608625,20629283872300⟩,⟨-19729478472512,20572128514456⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236743443177,239190064591⟩,⟨1561679075733,1569984724013⟩,⟨308572612196,310608717220⟩,⟨-3938729622245,-3925004181828⟩,⟨-1558725168992,-1550849608250⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1708138972204,-1620408232490⟩,⟨-5593938612002,-2660234716692⟩,⟨-544399430352,1494938651150⟩,⟨-20599728785430,103989071438526⟩,⟨-59921126134162,43409384537064⟩,⟨-49102855356553,52935738994808⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-193175754679,-179087289034⟩,⟨-1875732945775,-1429514478219⟩,⟨-361822115142,-98381346982⟩,⟨-7266684388125,12352618694470⟩,⟨-7358681505902,6819494356840⟩,⟨-5585827157751,6848574325377⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43567688498,60102775557⟩,⟨-314053870042,140470245794⟩,⟨-53249502946,212227370238⟩,⟨-11205414010370,8427614512642⟩,⟨-8917406674894,5268644748590⟩,⟨-5934927468279,6500158189719⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2588008721,6441143138⟩,⟨-113484446896,38845949982⟩,⟨-35081225716,51903964210⟩,⟨-3791157214281,3932692105767⟩,⟨-2978301859336,2138504587035⟩,⟨-2151578796914,2205649857062⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1726351439,3285407393⟩,⟨-34334351338,15357093900⟩,⟨-5821571766,23202035666⟩,⟨-1305291712209,1100766634088⟩,⟨-1096144331104,630228539514⟩,⟨-669400134122,792566434831⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3029990707,5814563364⟩,⟨-84607751808,15186514125⟩,⟨-20983450803,35675056143⟩,⟨-2479773390781,2579303632517⟩,⟨-2120693013114,1355342022218⟩,⟨-1324709361315,1467008243743⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5814563364,-3029990707⟩,⟨-15186514125,84607751808⟩,⟨-35675056143,20983450803⟩,⟨-2579303632517,2479773390781⟩,⟨-1355342022218,2120693013114⟩,⟨-1467008243743,1324709361315⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3226554643,3411152431⟩,⟨-128670961021,123453701790⟩,⟨-70756281859,72887415013⟩,⟨-6370460846798,6412465496548⟩,⟨-4333643881554,4259197600149⟩,⟨-3618587040657,3530359218377⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48808712809,65081662138⟩,⟨-369772200646,223558983628⟩,⟨-19450690385,289186596347⟩,⟨-14740674618038,10773399563745⟩,⟨-10263011625946,6615628712304⟩,⟨-6962780994861,7891689476815⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3226554643,3411152431⟩,⟨-128670961021,123453701790⟩,⟨-70756281859,72887415013⟩,⟨-6370460846798,6412465496548⟩,⟨-4333643881554,4259197600149⟩,⟨-3618587040657,3530359218377⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (521/5120) u, BivariateJet2.affineZ (115/1024) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000037

end


