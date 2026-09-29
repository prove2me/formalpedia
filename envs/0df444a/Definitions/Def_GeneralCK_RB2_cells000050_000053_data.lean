-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000050_000053_data
-- name    : GeneralCK_RB2_cells000050_000053_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T04:27:53.351444+00:00
-- url     : https://prove2.me/theorems/41518f17-56a1-44f3-8ca2-a0ca2e3f6237
-- title:
--   Exact certificate data for RB2 cells 000050–000053
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000050 through 000053. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000050Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2098973751424,-2098973712640⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2098973751424,-2098973712640⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-176401331520,-176401331456⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-176401331520,-176401331456⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨89493424256,89493424320⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-97428246400,-97428246336⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨89493549120,89493549184⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-97428394368,-97428394304⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7934845248,-7934845184⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7934822080,-7934822016⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨186921670592,186921670656⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨186921943424,186921943488⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1922572381184,1922572419776⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1922572381184,1922572419776⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2506246686912,-2506246629056⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2105796470144,-2105796431296⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2092188046272,-2092188007552⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-177586488320,-177586488256⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-175218336256,-175218336192⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨86929573632,86929573696⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-94397011456,-94397011392⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨92079218368,92079218432⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-100501110592,-100501110528⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8421892224,-8421892160⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7467437760,-7467437696⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨181326585088,181326585152⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨192580328960,192580329024⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1914601519296,1914601557888⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1930578095104,1930578133696⟩



end LaneCBRB2Cell000050Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000050
open Set LaneCBRB2Cell000050Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112313394790,112313394791⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨127345780326,127345780327⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112313394791,-112313394790⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437442419097,437442419098⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50664717680,50664717681⟩,⟨-127345780327,-127345780326⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨162978112470,162978112472⟩,⟨972165847449,972165847450⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨50664717679,50664717682⟩,⟨-127345780327,-127345780326⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2098973751424,-2098973712640⟩,⟨6558596348822,6558596348911⟩,⟨2951151040985,2951151041029⟩,⟨-39122083824574,-39122083823520⟩,⟨-25021360295363,-25021360294774⟩,⟨-7921055354897,-7921055354663⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311126114080,-311126108326⟩,⟨-883704108170,-883704073848⟩,⟨-397637567561,-397637552115⟩,⟨5798977669979,5798977670378⟩,⟨3608809889957,3608809928960⟩,⟨1174120052792,1174120052883⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨311126108326,311126114080⟩,⟨883704073848,883704108170⟩,⟨397637552115,397637567561⟩,⟨-5798977670378,-5798977669979⟩,⟨-3608809928960,-3608809889957⟩,⟨-1174120052883,-1174120052792⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162978112472,-162978112470⟩,⟨-972165847450,-972165847449⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨936533515304,936533515306⟩,⟨-972165847450,-972165847449⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-176401331520,-176401331456⟩,⟨-1141344795388,-1141344795383⟩,⟨-513567340006,-513567340002⟩,⟨-1184769591382,-1184769591370⟩,⟨757744575816,757744575826⟩,⟨-239880512455,-239880512451⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150253762616,-150253762560⟩,⟨-816195373332,-816195373267⟩,⟨-367260873754,-367260873721⟩,⟨1009153884501,1009153884526⟩,⟨1377196106440,1377196106524⟩,⟨204323568664,204323568675⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150253762560,150253762616⟩,⟨816195373267,816195373332⟩,⟨367260873721,367260873754⟩,⟨-1009153884526,-1009153884501⟩,⟨-1377196106524,-1377196106440⟩,⟨-204323568675,-204323568664⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨461379870886,461379876696⟩,⟨1699899447115,1699899481502⟩,⟨764898425836,764898441315⟩,⟨-6808131554904,-6808131554480⟩,⟨-4986006035484,-4986005996397⟩,⟨-1378443621558,-1378443621456⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨823974716484,823974728266⟩,⟨4089773433471,4089773525802⟩,⟨764898425836,764898441315⟩,⟨-18796595897867,-18796595896946⟩,⟨-4986006035484,-4986005996397⟩,⟨-1378443621558,-1378443621456⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨101329435358,101329435364⟩,⟨-254691560654,-254691560652⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11930647943234,11930647943942⟩,⟨29987686532902,29987686536698⟩,⟨-103009978878620,-103009978866156⟩,⟨150748114917870,150748114947078⟩,⟨-258915607246350,-258915607118172⟩,⟨1778789516963968,1778789517288796⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8940835192785,8940835321162⟩,⟨66850354879800,66850356208489⟩,⟨-68895938533583,-68895937251967⟩,⟨132097515665910,132097522389909⟩,⟨-610431152443281,-610431140024042⟩,⟨1174746573994907,1174746596218950⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨93236387840,93236523264⟩,⟨-689915332079,-689913286307⟩,⟨711024235670,711026343137⟩,⟨8793830920946,8793881177729⟩,⟨-4168155377247,-4168089122210⟩,⟨-1335499915887,-1335414964205⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1192748015616,1192748151040⟩,⟨-689915332079,-689913286307⟩,⟨711024235670,711026343137⟩,⟨8793830920946,8793881177729⟩,⟨-4168155377247,-4168089122210⟩,⟨-1335499915887,-1335414964205⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨89493424256,89493549184⟩,⟨-635985069664,-635983111598⟩,⟨655443828664,655445845811⟩,⟨7738551882787,7738601396618⟩,⟨-3463209240428,-3463145394237⟩,⟨-1621832041603,-1621751185832⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨97082287713,97082434258⟩,⟨-746070316050,-746067868708⟩,⟨768897115963,768899637214⟩,⟨9908652682948,9908717262279⟩,⟨-4918696243470,-4918615719872⟩,⟨-1020346555131,-1020246455418⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-93236523264,-93236387840⟩,⟨689913286307,689915332079⟩,⟨-711026343137,-711024235670⟩,⟨-8793881177729,-8793830920946⟩,⟨4168089122210,4168155377247⟩,⟨1335414964205,1335499915887⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1006275104512,1006275239936⟩,⟨689913286307,689915332079⟩,⟨-711026343137,-711024235670⟩,⟨-8793881177729,-8793830920946⟩,⟨4168089122210,4168155377247⟩,⟨1335414964205,1335499915887⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-97428394368,-97428246336⟩,⟨753837171328,753839508104⟩,⟨-776906562062,-776904154770⟩,⟨-10125521338130,-10125461927423⟩,⟨5086937202551,5087013510987⟩,⟨910191504843,910287926049⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-89166661310,-89166513829⟩,⟨628779376081,628781881717⟩,⟨-648022244390,-648019663068⟩,⟨-7541647690577,-7541580695673⟩,⟨3311253823759,3311336632081⟩,⟨1719475044270,1719577200373⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7915626403,7915920429⟩,⟨-117290939969,-117285986991⟩,⟨120874871573,120879974146⟩,⟨2367004992371,2367136566606⟩,⟨-1607442419711,-1607279087791⟩,⟨699128489139,699330744955⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3957813201,3957960215⟩,⟨-58645469985,-58642993495⟩,⟨60437435786,60439987073⟩,⟨1183502496185,1183568283303⟩,⟨-803721209856,-803639543895⟩,⟨349564244569,349665372478⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3957960215,-3957813201⟩,⟨58642993495,58645469985⟩,⟨-60439987073,-60437435786⟩,⟨-1183568283303,-1183502496185⟩,⟨803639543895,803721209856⟩,⟨-349665372478,-349564244569⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758165423401,758165589679⟩,⟨58642993495,58645469985⟩,⟨-60439987073,-60437435786⟩,⟨-1183568283303,-1183502496185⟩,⟨803639543895,803721209856⟩,⟨-349665372478,-349564244569⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7906259286,7906282254⟩,⟨-117007051650,-117006534742⟩,⟨120586867342,120587399912⟩,⟨2357201761637,2357217585898⟩,⟨-1599205082026,-1599187528016⟩,⟨693104256667,693124444488⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7906282254,-7906259286⟩,⟨117006534742,117007051650⟩,⟨-120587399912,-120586867342⟩,⟨-2357217585898,-2357201761637⟩,⟨1599187528016,1599205082026⟩,⟨-693124444488,-693104256667⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091605345522,1091605368490⟩,⟨117006534742,117007051650⟩,⟨-120587399912,-120586867342⟩,⟨-2357217585898,-2357201761637⟩,⟨1599187528016,1599205082026⟩,⟨-693124444488,-693104256667⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7934845248,-7934822016⟩,⟨117853987519,117854510652⟩,⟨-121460790670,-121460251686⟩,⟨-2386923043571,-2386906942590⟩,⟨1623789124139,1623806954745⟩,⟨-711562132172,-711541664363⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3967422624,-3967411008⟩,⟨58926993759,58927255326⟩,⟨-60730395335,-60730125843⟩,⟨-1193461521786,-1193453471295⟩,⟨811894562069,811903477373⟩,⟨-355781066086,-355770832181⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3967411008,3967422624⟩,⟨-58927255326,-58926993759⟩,⟨60730125843,60730395335⟩,⟨1193453471295,1193461521786⟩,⟨-811903477373,-811894562069⟩,⟨355770832181,355781066086⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766090794624,766090825504⟩,⟨-58927255326,-58926993759⟩,⟨60730125843,60730395335⟩,⟨1193453471295,1193461521786⟩,⟨-811903477373,-811894562069⟩,⟨355770832181,355781066086⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272901336380,272901342123⟩,⟨29251633685,29251762913⟩,⟨-30146849978,-30146716835⟩,⟨-589304396475,-589300440409⟩,⟨399796882004,399801270507⟩,⟨-173281111122,-173276064166⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532181589248,1532181651008⟩,⟨-117854510652,-117853987518⟩,⟨121460251686,121460790670⟩,⟨2386906942590,2386923043572⟩,⟨-1623806954746,-1623789124138⟩,⟨711541664362,711562132172⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1201386829006,1201386990689⟩,⟨-823686585230,-823683921088⟩,⟨848888174861,848890919444⟩,⟨11628362839792,11628432821288⟩,⟨-6140361953574,-6140274140885⟩,⟨-394814752242,-394705303956⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1303262030236,1303262353602⟩,⟨-1647373170460,-1647367842176⟩,⟨1697776349722,1697781838888⟩,⟨23256725679589,23256865642570⟩,⟨-12280723907146,-12280548281773⟩,⟨-789629356728,-789410755669⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨186921670592,186921943488⟩,⟨-1389824850404,-1389820010291⟩,⟨1432347702457,1432352688852⟩,⟨17864000679565,17864135865419⟩,⟨-8550234347761,-8550071000471⟩,⟨-2532130120281,-2531932538089⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨64290912144,64291019626⟩,⟨-470756643781,-470754911562⟩,⟨485159740877,485161525393⟩,⟨5889802136075,5889847170888⟩,⟨-2730148800494,-2730092032847⟩,⟨-1028711731904,-1028640801819⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380291024414,380291047747⟩,⟨11510710878,11511023062⟩,⟨-11863253686,-11862932043⟩,⟨-235037253422,-235027643190⟩,⟨160551413795,160562042993⟩,⟨-71523380306,-71511194733⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178948930764,3178949125811⟩,⟨-96223561302,-96220939868⟩,⟨99165245559,99167946424⟩,⟨1970480300013,1970561192499⟩,⟨-1348182266563,-1348092923025⟩,⟨603966931466,604069203750⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨185880277438,185880599600⟩,⟨-1366695625699,-1366690371244⟩,⟨1408510309920,1408515723066⟩,⟨17226427315845,17226566037515⟩,⟨-8057257304822,-8057084710378⟩,⟨-2851421146480,-2851207143733⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨372801948030,372802543088⟩,⟨-2756520476103,-2756510381535⟩,⟨2840858012377,2840868411918⟩,⟨35090427995410,35090701902934⟩,⟨-16607491652583,-16607155710849⟩,⟨-5383551266761,-5383139681822⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522791023505,522791252819⟩,⟨80874251566,80877684620⟩,⟨-83352494476,-83348957726⟩,⟨-1625997801512,-1625906188502⟩,⟨1101847708214,1101961120832⟩,⟨-475577634773,-475437503066⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360489209639,360489446824⟩,⟨83649949165,83653518394⟩,⟨-86213267140,-86209590096⟩,⟨-1675334088950,-1675238413976⟩,⟨1132995640979,1133113761559⟩,⟨-485027886945,-484882255144⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720978419278,720978893648⟩,⟨167299898330,167307036788⟩,⟨-172426534280,-172419180192⟩,⟨-3350668177900,-3350476827952⟩,⟨2265991281958,2266227523118⟩,⟨-970055773890,-969764510288⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524275306994,1524275391722⟩,⟨-847975910,-846935868⟩,⟨872851774,873923328⟩,⟨29689356692,29721281935⟩,⟨-24619426730,-24584042112⟩,⟨18417219874,18457875505⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨999507029865,999507743053⟩,⟨231375207616,231385799048⟩,⟨-238466069087,-238455157653⟩,⟨-4625889604192,-4625602799118⟩,⟨3125511762760,3125862994040⟩,⟨-1333005549722,-1332574675637⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67734744696,67734747548⟩,⟨14520646662,14520711118⟩,⟨-14965036498,-14964970090⟩,⟨-290977009434,-290975025715⟩,⟨196856953826,196859150650⟩,⟨-84364407038,-84361885291⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50760460960,50760463824⟩,⟨262829785330,262829850087⟩,⟨35906293951,35906346817⟩,⟨-1267988473296,-1267986452819⟩,⟨-205197918768,-205195961698⟩,⟨-168962411648,-168960424544⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135111956186,2135112128313⟩,⟨-328463136084,-328461664856⟩,⟨338512402702,338513918508⟩,⟨6677627307104,6677672673343⟩,⟨-4551624302420,-4551574194576⟩,⟨2009917135832,2009974498172⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2975302077403,2975302437195⟩,⟨-686575536030,-686572433096⟩,⟨707581154281,707584351243⟩,⟨14010831550995,14010927412125⟩,⟨-9568535411744,-9568429804186⟩,⟨4257354475704,4257475047719⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137358897467,137358921829⟩,⟨679526341296,679526747578⟩,⟨129829656126,129829960369⟩,⟨-3112616484386,-3112604575612⟩,⟨-850294036232,-850282832541⟩,⟨-214454999582,-214443712834⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8801218031688,8801219592674⟩,⟨-43540420277228,-43540378800196⟩,⟨-8318805785336,-8318783340236⟩,⟨630234854592401,630236432743538⟩,⟨136788998938385,136790022021090⟩,⟨29465981380623,29466791518880⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8000715110071,8000722237910⟩,⟨-37728208147671,-37728057091710⟩,⟨-9471025837079,-9470912356640⟩,⟨517558353330627,517563355378202⟩,⟨157058321655379,157062682280483⟩,⟨19723933797832,19728315103310⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16001430220142,16001444475820⟩,⟨-75456416295342,-75456114183420⟩,⟨-18942051674158,-18941824713280⟩,⟨1035116706661254,1035126710756404⟩,⟨314116643310758,314125364560966⟩,⟨39447867595664,39456630206620⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10763861442032,10763861442129⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311394,2063168215367208⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9664349814256,9664349814353⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311405,2063168215367197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2389873986368,2389874044224⟩,⟨-11988464342936,-11988464342527⟩,⟨0,0⟩,⟨104010778944236,104010778977589⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7417718865914,7417718866006⟩,⟨-44246757053619,-44246757052474⟩,⟨-19909574578809,-19909574578268⟩,⟨527864575363499,527864575384236⟩,⟨287564288960337,287564288971209⟩,⟨106876835602157,106876835606625⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6318207238138,6318207238230⟩,⟨-44246757053619,-44246757052473⟩,⟨-19909574578809,-19909574578267⟩,⟨527864575363498,527864575384228⟩,⟨287564288960336,287564288971206⟩,⟨106876835602155,106876835606625⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1922572381184,1922572419776⟩,⟨-7699941144429,-7699941144068⟩,⟨-3464718381094,-3464718380926⟩,⟨37937314227104,37937314238739⟩,⟨25779104868139,25779104873858⟩,⟨7681174841154,7681174843598⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100840757001,100840757003⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138820236851,138820236854⟩,⟨683961974339,683961974345⟩,⟨307760225695,307760225700⟩,⟨-1719138590394,-1719138590390⟩,⟨-1547110805672,-1547110805664⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4312446367552,4312446464000⟩,⟨-19688405487365,-19688405486595⟩,⟨-3464718381094,-3464718380926⟩,⟨141948093171340,141948093216328⟩,⟨25779104868139,25779104873858⟩,⟨7681174841154,7681174843598⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨745603896060,745605086176⟩,⟨-5513040952206,-5513020763070⟩,⟨5681716024754,5681736823836⟩,⟨70180855990820,70181403805868⟩,⟨-33214983305166,-33214311421698⟩,⟨-10767102533522,-10766279363644⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5058050263612,5058051550176⟩,⟨-25201446439571,-25201426249665⟩,⟨2216997643660,2217018442910⟩,⟨212128949162160,212129497022196⟩,⟨-7435878437027,-7435206547840⟩,⟨-3085927692368,-3085104520046⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463894700744,463894818750⟩,⟨1713377559935,1713380435415⟩,⟨203330019445,203331927035⟩,⟨-30766619558980,-30766534608520⟩,⟨1082096800180,1082174971962⟩,⟨-283023186562,-282947690019⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36961056113,36961058238⟩,⟨-752711320884,-752711310162⟩,⟨319124126993,319124145312⟩,⟨9340144078713,9340144107289⟩,⟨-6498957778804,-6498957686573⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨500855756857,500855876988⟩,⟨960666239051,960669125253⟩,⟨522454146438,522456072347⟩,⟨-21426475480267,-21426390501231⟩,⟨-5416860978624,-5416782714611⟩,⟨-283023186562,-282947690019⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505853361827,505853374074⟩,⟨2537541677330,2537541800300⟩,⟨0,0⟩,⟨3442964323895,3442967248197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨230429185100,230429245948⟩,⟨1597889971865,1597891643689⟩,⟨240365976766,240366868641⟩,⟨-3855134468487,-3855079888265⟩,⟨-1286378603115,-1286338032578⟩,⟨-130210750162,-130176013242⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-745605086176,-745603896060⟩,⟨5513020763070,5513040952206⟩,⟨-5681736823836,-5681716024754⟩,⟨-70181403805868,-70180855990820⟩,⟨33214311421698,33214983305166⟩,⟨10766279363644,10767102533522⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3566841281376,3566842567940⟩,⟨-14175384724295,-14175364534389⟩,⟨-9146455204930,-9146434405680⟩,⟨71766689365472,71767237225508⟩,⟨58993416289837,58994088179024⟩,⟨18447454204798,18448277377120⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450336075564,450336238012⟩,⟨429057345208,429060694690⟩,⟨-156415990340,-156413004144⟩,⟨-14151806803909,-14151710502517⟩,⟨-7227997975264,-7227892744766⟩,⟨-3920355542575,-3920239560791⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨325956224940,325956224944⟩,⟨1944331694898,1944331694900⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-325956224944,-325956224940⟩,⟨-1944331694900,-1944331694898⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨773555402832,773555402836⟩,⟨-1944331694900,-1944331694898⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1352615302312,1352615329471⟩,⟨-8817050516249,-8817050447717⟩,⟨-3967380583524,-3967380552680⟩,⟨53923116520156,53923116529786⟩,⟨34235627710120,34235627792028⟩,⟨10917823109265,10917823111295⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1352615329471,-1352615302312⟩,⟨8817050447717,8817050516249⟩,⟨3967380552680,3967380583524⟩,⟨-53923116529786,-53923116520156⟩,⟨-34235627792028,-34235627710120⟩,⟨-10917823111295,-10917823109265⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-253103701695,-253103674536⟩,⟨8817050447717,8817050516249⟩,⟨3967380552680,3967380583524⟩,⟨-53923116529786,-53923116520156⟩,⟨-34235627792028,-34235627710120⟩,⟨-10917823111295,-10917823109265⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11662839453,-11662838200⟩,⟨435597991446,435597997776⟩,⟨82116384941,82116397180⟩,⟨-4527126140479,-4527126123995⟩,⟨1723924212748,1723924274627⟩,⟨2653771541417,2653771566092⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438673236111,438673399812⟩,⟨864655336654,864658692466⟩,⟨-74299605399,-74296606964⟩,⟨-18678932944388,-18678836626512⟩,⟨-5504073762516,-5503968470139⟩,⟨-1266584001158,-1266467994699⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100840757003,-100840757001⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4646670717,4646670718⟩,⟨28634666195,28634666199⟩,⟨40119652736,40119652738⟩,⟨-303988306088,-303988306079⟩,⟨247233542879,247233542884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10099899982,10099900229⟩,⟨11574955015,11574956546⟩,⟨87203183662,87203185778⟩,⟨-845612949973,-845612933611⟩,⟨99938903425,99938916483⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1467187983008,1467188003988⟩,⟨-7282343178794,-7282342806117⟩,⟨-1361995453157,-1361995386641⟩,⟨105761015375530,105761022699721⟩,⟨22398639843656,22398641326029⟩,⟨4983177311480,4983177592683⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13477303476,13477303999⟩,⟨-51448573357,-51448566032⟩,⟨103852876199,103852881605⟩,⟨-310213281979,-310213124842⟩,⟨-252798948181,-252798864027⟩,⟨-170267496854,-170267477357⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13477303999,-13477303476⟩,⟨51448566032,51448573357⟩,⟨-103852881605,-103852876199⟩,⟨310213124842,310213281979⟩,⟨252798864027,252798948181⟩,⟨170267477357,170267496854⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114318061002,-114318060477⟩,⟨-823436272164,-823436264837⟩,⟨-103852881605,-103852876199⟩,⟨2509236380394,2509236537531⟩,⟨252798864027,252798948181⟩,⟨170267477357,170267496854⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨88590774712,88590776497⟩,⟨-577480777141,-577480772629⟩,⟨605246654857,605246670231⟩,⟨3531743770260,3531743770999⟩,⟨-3396838361302,-3396838322201⟩,⟨-2402944142403,-2402944142128⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨118215502937,118215507010⟩,⟨-1357349270332,-1357349211440⟩,⟨697901108634,697901148270⟩,⟨20883824805137,20883826086583⟩,⟨-6021378295551,-6021377675255⟩,⟨-4304450801304,-4304450613018⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-118215507010,-118215502937⟩,⟨1357349211440,1357349270332⟩,⟨-697901148270,-697901108634⟩,⟨-20883826086583,-20883824805137⟩,⟨6021377675255,6021378295551⟩,⟨4304450613018,4304450801304⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨981296120766,981296124839⟩,⟨1357349211440,1357349270332⟩,⟨-697901148270,-697901108634⟩,⟨-20883826086583,-20883824805137⟩,⟨6021377675255,6021378295551⟩,⟨4304450613018,4304450801304⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123894787889,123894788407⟩,⟨781798709059,781798719039⟩,⟨186556565401,186556571553⟩,⟨-2482312290818,-2482312049312⟩,⟨-674740031959,-674739906735⟩,⟨-157880583936,-157880536662⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11885839695,11885839805⟩,⟨171228087714,171228090026⟩,⟨21595514012,21595515236⟩,⟨711581791041,711581848065⟩,⟨102985248102,102985275328⟩,⟨-15787427761,-15787421500⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172977192494,172977348201⟩,⟨1676227312543,1676232839656⟩,⟨109518549610,109521302787⟩,⟨-1956285330980,-1956072612456⟩,⟨462496074788,462633517819⟩,⟨-547404260255,-547300278070⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172977348201,-172977192494⟩,⟨-1676232839656,-1676227312543⟩,⟨-109521302787,-109518549610⟩,⟨1956072612456,1956285330980⟩,⟨-462633517819,-462496074788⟩,⟨547300278070,547404260255⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57451836899,57452053454⟩,⟨-78342867791,-78335668854⟩,⟨130844673979,130848319031⟩,⟨-1899061856031,-1898794557285⟩,⟨-1749012120934,-1748834107366⟩,⟨417089527908,417228247013⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27979611150556,27979636639238⟩,⟨-243999789340000,-243999158589315⟩,⟨-83544332412328,-83543889966504⟩,⟨3418930058813646,3418952311507349⟩,⟨1294847290230601,1294865426723916⟩,⟨300139927703840,300156781125793⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13960669517,13960669635⟩,⟨176188741952,176188744940⟩,⟨42043004394,42043005958⟩,⟨552360989705,552361074856⟩,⟨113237380914,113237421910⟩,⟨27726438117,27726453097⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355261458468,355261785106⟩,⟨1385426038665,1385438234005⟩,⟨9105942680,9112583884⟩,⟨-20731599706199,-20731098349180⟩,⟨-3394946081224,-3394616400686⟩,⟨-1872631795874,-1872382675132⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355261785106,-355261458468⟩,⟨-1385438234005,-1385426038665⟩,⟨-9112583884,-9105942680⟩,⟨20731098349180,20731599706199⟩,⟨3394616400686,3394946081224⟩,⟨1872382675132,1872631795874⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83411451005,83411941344⟩,⟨-520782897351,-520767346199⟩,⟨-83412189283,-83402549644⟩,⟨2052165404792,2052763079687⟩,⟨-2109457361830,-2109022388915⟩,⟨605798673974,606163801175⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239660993852,239660993857⟩,⟨1558846812533,1558846812541⟩,⟨307760225695,307760225700⟩,⟨-3918161845946,-3918161845942⟩,⟨-1547110805672,-1547110805664⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1663696917337,-1663695427509⟩,⟨-4138358384653,-4138316154676⟩,⟨458018389018,458043420741⟩,⟨41913421251851,41914950224356⟩,⟨-7668258449348,-7667148027759⟩,⟨1953816220207,1954772854517⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187468119791,-187467951130⟩,⟨-1649275104922,-1649269269996⟩,⟨-230672869153,-230669786228⟩,⟨2593823477307,2594059642827⟩,⟨-219602340877,-219451118207⟩,⟨614477765524,614594346542⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52192874061,52193042727⟩,⟨-90428292389,-90422457455⟩,⟨77087356542,77090439472⟩,⟨-1324338368639,-1324102203115⟩,⟨-1766713146549,-1766561923871⟩,⟨266403465639,266520046660⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4358426921,4358468971⟩,⟨-33155427036,-33153930817⟩,⟨5567692419,5568547416⟩,⟨37367092539,37428886891⟩,⟨-298943019282,-298900781018⟩,⟨43442559965,43475314979⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2477550972,2477566986⟩,⟨-8585134726,-8584553022⟩,⟨7318541414,7318857754⟩,⟨-110858360582,-110833613627⟩,⟨-180409718352,-180393494210⟩,⟨36101160856,36113175232⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4332169802,4332197892⟩,⟨-32362243673,-32361114072⟩,⟨4989809636,4990413500⟩,⟨11877554440,11929530088⟩,⟨-281573573143,-281540773909⟩,⟨34307990977,34331105765⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4332197892,-4332169802⟩,⟨32361114072,32362243673⟩,⟨-4990413500,-4989809636⟩,⟨-11929530088,-11877554440⟩,⟨281540773909,281573573143⟩,⟨-34331105765,-34307990977⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨26229029,26299169⟩,⟨-794312964,-791687144⟩,⟨577278919,578737780⟩,⟨25437562451,25551332451⟩,⟨-17402245373,-17327207875⟩,⟨9111454200,9167324002⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57451836899,57452053454⟩,⟨-78342867791,-78335668854⟩,⟨130844673979,130848319031⟩,⟨-1899061856031,-1898794557285⟩,⟨-1749012120934,-1748834107366⟩,⟨417089527908,417228247013⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨26229029,26299169⟩,⟨-794312964,-791687144⟩,⟨577278919,578737780⟩,⟨25437562451,25551332451⟩,⟨-17402245373,-17327207875⟩,⟨9111454200,9167324002⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112098646425,112528143156⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨125413045043,129278515610⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112528143156,-112098646425⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437227670732,437657167463⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49871281192,51458909144⟩,⟨-129278515610,-125413045043⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161969927617,163987052300⟩,⟨970233112166,974098582733⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49441784461,51888405875⟩,⟨-129278515610,-125413045043⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2105796470144,-2092188007552⟩,⟨6505285469294,6612540575111⟩,⟨2931554053887,2970978327181⟩,⟨-39768285985231,-38488668939880⟩,⟨-25331564061410,-24716686933220⟩,⟨-8027847998689,-7816205807891⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-314069762574,-308201870342⟩,⟨-907305312015,-859962751452⟩,⟨-406356157750,-388864019399⟩,⟨5549557262439,6046799064911⟩,⟨3487837736964,3728963990237⟩,⟨1134185342010,1213765817368⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨308201870342,314069762574⟩,⟨859962751452,907305312015⟩,⟨388864019399,406356157750⟩,⟨-6046799064911,-5549557262439⟩,⟨-3728963990237,-3487837736964⟩,⟨-1213765817368,-1134185342010⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-163987052300,-161969927617⟩,⟨-974098582733,-970233112166⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨935524575476,937541700159⟩,⟨-974098582733,-970233112166⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-177586488320,-175218336192⟩,⟨-1144847229450,-1137850815914⟩,⟨-514373600887,-512763227356⟩,⟨-1192052130845,-1177526864262⟩,⟨753881013702,761600870074⟩,⟨-240634291267,-239129919763⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151426082253,-149085335198⟩,⟨-821582385734,-810815122283⟩,⟨-368924152363,-365599226946⟩,⟨991678912376,1026621982880⟩,⟨1368803650823,1385596231347⟩,⟨202620740779,206024805898⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149085335198,151426082253⟩,⟨810815122283,821582385734⟩,⟨365599226946,368924152363⟩,⟨-1026621982880,-991678912376⟩,⟨-1385596231347,-1368803650823⟩,⟨-206024805898,-202620740779⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨457287205540,465495844827⟩,⟨1670777873735,1728887697749⟩,⟨754463246345,775280310113⟩,⟨-7073421047791,-6541236174815⟩,⟨-5114560221584,-4856641387787⟩,⟨-1419790623266,-1336806082789⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨818940188968,829033930543⟩,⟨4053621399674,4125780299238⟩,⟨754463246345,775280310113⟩,⟨-19166004781746,-18425344665715⟩,⟨-5114560221584,-4856641387787⟩,⟨-1419790623266,-1336806082789⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98883568922,103776811750⟩,⟨-258557031220,-250826090086⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11649286572100,12225750271699⟩,⟨28156049062387,31967431284578⟩,⟨-108221968368534,-98160472416109⟩,⟨136105004181499,167174470314479⟩,⟨-319101899234274,-202620590469025⟩,⟨1654260676877961,1915955123780244⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8676642161570,9218239758033⟩,⟨63919212588500,69979109704579⟩,⟨-73606065819037,-64491516575461⟩,⟨95870742093389,170741608992960⟩,⟨-684242876236001,-541724351478466⟩,⟨1063724833630681,1295758950162207⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨90458368000,96044753152⟩,⟨-766598793687,-620741518026⟩,⟨626299359421,806330939378⟩,⟨6592506351960,11256543494864⟩,⟨-7558376812155,-1043037243187⟩,⟨-5579474324621,3153460567463⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1189969995776,1195556380928⟩,⟨-766598793687,-620741518026⟩,⟨626299359421,806330939378⟩,⟨6592506351960,11256543494864⟩,⟨-7558376812155,-1043037243187⟩,⟨-5579474324621,3153460567463⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨86929573632,92079218432⟩,⟨-708323983370,-570874387691⟩,⟨575985741146,745035796558⟩,⟨5606584548028,10104448756007⟩,⟨-6684753059977,-479280421976⟩,⟨-5660178268711,2612009270773⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨94081391914,100122540196⟩,⟨-834396883744,-666918084067⟩,⟨672889369741,877642945207⟩,⟨7233649762666,12917491890804⟩,⟨-8940565468085,-1251534405296⟩,⟨-5965682139496,4197011878699⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-96044753152,-90458368000⟩,⟨620741518026,766598793687⟩,⟨-806330939378,-626299359421⟩,⟨-11256543494864,-6592506351960⟩,⟨1043037243187,7558376812155⟩,⟨-3153460567463,5579474324621⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1003466874624,1009053259776⟩,⟨620741518026,766598793687⟩,⟨-806330939378,-626299359421⟩,⟨-11256543494864,-6592506351960⟩,⟨1043037243187,7558376812155⟩,⟨-3153460567463,5579474324621⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-100501110592,-94397011392⟩,⟨676388991661,839972209162⟩,⟨-883507234870,-682445075599⟩,⟨-12975637235987,-7599598975904⟩,⟨1556363407053,8956766785067⟩,⟨-4165225465831,5689922018620⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-92232742877,-86151225328⟩,⟨547233791937,717573631508⟩,⟨-757049808832,-549129137835⟩,⟨-10578397172610,-4735563693916⟩,⟨-502456988190,7359768586508⟩,⟨-3555076430320,6805893542405⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1848649037,13971314868⟩,⟨-287163091807,50655547441⟩,⟨-84160439091,328513807372⟩,⟨-3344747409944,8181928196888⟩,⟨-9443022456275,6108234181212⟩,⟨-9520758569816,11002905421104⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨924324518,6985657434⟩,⟨-143581545904,25327773721⟩,⟨-42080219546,164256903686⟩,⟨-1672373704972,4090964098444⟩,⟨-4721511228138,3054117090606⟩,⟨-4760379284908,5501452710552⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6985657434,-924324518⟩,⟨-25327773721,143581545904⟩,⟨-164256903686,42080219546⟩,⟨-4090964098444,1672373704972⟩,⟨-3054117090606,4721511228138⟩,⟨-5501452710552,4760379284908⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755137726182,761199078362⟩,⟨-25327773721,143581545904⟩,⟨-164256903686,42080219546⟩,⟨-4090964098444,1672373704972⟩,⟨-3054117090606,4721511228138⟩,⟨-5501452710552,4760379284908⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7442137158,8389719923⟩,⟨-133928173286,-102138555430⟩,⟨103053058286,140869553492⟩,⟨1785642594455,3035539797186⟩,⟨-2444857747092,-878792819796⟩,⟨-261258440542,1733574982747⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8389719923,-7442137158⟩,⟨102138555430,133928173286⟩,⟨-140869553492,-103053058286⟩,⟨-3035539797186,-1785642594455⟩,⟨878792819796,2444857747092⟩,⟨-1733574982747,261258440542⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091121907853,1092069490618⟩,⟨102138555430,133928173286⟩,⟨-140869553492,-103053058286⟩,⟨-3035539797186,-1785642594455⟩,⟨878792819796,2444857747092⟩,⟨-1733574982747,261258440542⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8421892224,-7467437696⟩,⟨102834600091,134957957269⟩,⟨-141952710279,-103755335019⟩,⟨-3075445513579,-1807429096878⟩,⟨894485517817,2481080224754⟩,⟨-1765231412005,253476412039⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4210946112,-3733718848⟩,⟨51417300045,67478978635⟩,⟨-70976355140,-51877667509⟩,⟨-1537722756790,-903714548439⟩,⟨447242758908,1240540112377⟩,⟨-882615706003,126738206020⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3733718848,4210946112⟩,⟨-67478978635,-51417300045⟩,⟨51877667509,70976355140⟩,⟨903714548439,1537722756790⟩,⟨-1240540112377,-447242758908⟩,⟨-126738206020,882615706003⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765857102464,766334348992⟩,⟨-67478978635,-51417300045⟩,⟨51877667509,70976355140⟩,⟨903714548439,1537722756790⟩,⟨-1240540112377,-447242758908⟩,⟨-126738206020,882615706003⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272780476963,273017372655⟩,⟨25534638857,33482043322⟩,⟨-35217388373,-25763264571⟩,⟨-758884949297,-446410648613⟩,⟨219698204949,611214436773⟩,⟨-433393745687,65314610136⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531714204928,1532668697984⟩,⟨-134957957270,-102834600090⟩,⟨103755335018,141952710280⟩,⟨1807429096878,3075445513580⟩,⟨-2481080224754,-894485517816⟩,⟨-253476412040,1765231412006⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1198079296511,1204749105513⟩,⟨-920368409101,-737025081705⟩,⟨743624074022,968070299608⟩,⟨8734275840342,14920689172279⟩,⟨-10553602733839,-2153343224055⟩,⟨-5775537896207,5341779585966⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1296646965246,1309986583250⟩,⟨-1840736818202,-1474050163409⟩,⟨1487248148043,1936140599216⟩,⟨17468551680685,29841378344552⟩,⟨-21107205467673,-4306686448109⟩,⟨-11546385689602,10683559171930⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨181326585088,192580329024⟩,⟨-1560880941025,-1237215186258⟩,⟨1248292656634,1641780036438⟩,⟨12446040543507,23912288394071⟩,⟨-16493548084604,-1284040878254⟩,⟨-12242424293981,7642081342902⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62126242779,66492409661⟩,⟨-532933786420,-413779238747⟩,⟨415790291675,561903973184⟩,⟨3970122397456,7974382001582⟩,⟨-5547410727113,-84098250885⟩,⟨-4584187288952,2660710285314⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380006650985,380573675170⟩,⟨2060825992,21159947650⟩,⟨-23350511593,-642469155⟩,⟨-617660746121,136992487933⟩,⟨-305194073895,638735202669⟩,⟨-676164654051,524504092408⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176588131258,3181328054341⟩,⟨-177146202344,-17201387836⟩,⟨5362588181,195485098542⟩,⟨-1146683226371,5190641435680⟩,⟨-5369114259346,2554956332985⟩,⟨-4391009207711,5684718759019⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨179488311415,192389205273⟩,⟨-1552703982907,-1196417430365⟩,⟨1201558609938,1637635386025⟩,⟨11413642924606,23558712043397⟩,⟨-16560860320764,-96980693507⟩,⟨-13525380370589,8242087124758⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨360814896503,384969534297⟩,⟨-3113584923932,-2433632616623⟩,⟨2449851266572,3279415422463⟩,⟨23859683468113,47471000437468⟩,⟨-33054408405368,-1381021571761⟩,⟨-25767804664570,15884168467660⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518623879091,526983091640⟩,⟨-35069166214,198804883280⟩,⟨-227432253634,58264821448⟩,⟨-5671017247102,2353090136651⟩,⟨-4271669922194,6548456328000⟩,⟨-7629956052359,6640360251794⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356187644502,364833834891⟩,⟨-36417919093,206450877969⟩,⟨-236179251064,60505674429⟩,⟨-5895992745040,2482531393704⟩,⟨-4480506889752,6811721516038⟩,⟨-7936458924857,6946711557393⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712375289004,729667669782⟩,⟨-72835838186,412901755938⟩,⟨-472358502128,121011348858⟩,⟨-11791985490080,4965062787408⟩,⟨-8961013779504,13623443032076⟩,⟨-15872917849714,13893423114786⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523324485005,1525226560826⟩,⟨-32819401840,31093573196⟩,⟨-37114218474,38899651994⟩,⟨-1228110700308,1289802919125⟩,⟨-1602287404958,1550372229276⟩,⟨-1987051394787,2026489852548⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨986964296546,1012184393883⟩,⟨-122816719747,593405912030⟩,⟨-679878920881,193680118052⟩,⟨-17197330202700,7766766713705⟩,⟨-13521207970521,19955821619408⟩,⟨-23370768963890,20649481045716⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67674762805,67792357888⟩,⟨12669899600,16627708646⟩,⟨-17489508256,-12783340202⟩,⟨-375688172833,-219463004076⟩,⟨106866047662,302342057696⟩,⟨-214022795211,34692289227⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50405636138,51115571224⟩,⟨258936558290,266919695849⟩,⟨33249967116,38279985535⟩,⟨-1371562526156,-1172750997624⟩,⟨-292684572505,-106363509778⟩,⟨-273577512388,-73665496862⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133809544446,2136469754787⟩,⟨-376250385038,-286514873942⟩,⟨289080199734,395751113758⟩,⟨5055043906509,8607189959096⟩,⟨-6951871265260,-2511598381030⟩,⟨-687087218225,4957956665452⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2972580104905,2978140689586⟩,⟨-786713627920,-598709769757⟩,⟨604070348748,827488307890⟩,⟨10603361534708,18066314548325⟩,⟨-14608747609481,-5288864073052⟩,⟨-1395741977916,10443386050101⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136273948700,138451798679⟩,⟨663473060852,695532490003⟩,⟨117585605892,142154676776⟩,⟨-3610890151930,-2612689049679⟩,⟨-1357047770167,-347242133828⟩,⟨-769365061769,343966834397⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8731745135485,8871290743002⟩,⟨-45278433617598,-41843282116189⟩,⟨-9254119956072,-7415776118812⟩,⟨565807859276202,697260926539674⟩,⟨92973621837988,182807115744500⟩,⟨-9795603265797,69391795739931⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7837953212640,8166700393909⟩,⟨-42673188287316,-32772322015030⟩,⟨-14004653508738,-5094001264357⟩,⟨320262787851689,714662538796437⟩,⟨-38607962496154,358330742977038⟩,⟨-200842370042324,241933053020154⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15675906425280,16333400787818⟩,⟨-85346376574632,-65544644030060⟩,⟨-28009307017476,-10188002528714⟩,⟨640525575703378,1429325077592874⟩,⟨-77215924992308,716661485954076⟩,⟨-401684740084648,483866106040308⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10743319721704,10784481866367⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239228,2075048233589864⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9643808093928,9684970238591⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239235,2075048233589852⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2387534470720,2392217527616⟩,⟨-12060075023605,-11917323006543⟩,⟨0,0⟩,⟨100606314842521,107411991083576⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7372080921382,7463890596243⟩,⟨-44888365133231,-43617083880538⟩,⟨-20168097032988,-19655684546403⟩,⟨516122930968928,539923595704492⟩,⟨282015439778595,293252362770973⟩,⟨104813264831956,108991988209671⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6272569293606,6364378968467⟩,⟨-44888365133232,-43617083880537⟩,⟨-20168097032989,-19655684546402⟩,⟨516122930968935,539923595704490⟩,⟨282015439778598,293252362770974⟩,⟨104813264831957,108991988209672⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1914601519296,1930578133696⟩,⟨-7868431117416,-7535297808913⟩,⟨-3535243081419,-3395720747880⟩,⟨32856695211786,43000843093145⟩,⟨23421807223231,28131938749043⟩,⟨6740751090277,8617773123753⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100626050579,101055547311⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137812865226,139829989910⟩,⟨680245070851,687677542764⟩,⟨306742660756,308777189903⟩,⟨-1725980926281,-1712309844048⟩,⟨-1551045566142,-1543176045194⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4302135990016,4322795661312⟩,⟨-19928506141021,-19452620815456⟩,⟨-3535243081419,-3395720747880⟩,⟨133463010054307,150412834176721⟩,⟨23421807223231,28131938749043⟩,⟨6740751090277,8617773123753⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨721629793006,769939068594⟩,⟨-6227169847864,-4867265233246⟩,⟨4899702533144,6558830844926⟩,⟨47719366936226,94942000874936⟩,⟨-66108816810736,-2762043143522⟩,⟨-51535609329140,31768336935320⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5023765783022,5092734729906⟩,⟨-26155675988885,-24319886048702⟩,⟨1364459451725,3163110097046⟩,⟨181182376990533,245354835051657⟩,⟨-42687009587505,25369895605521⟩,⟨-44794858238863,40386110059073⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459769316675,468070625576⟩,⟨1591509017890,1828566045743⟩,⟨124873773349,290719819588⟩,⟨-35248605254174,-26180913813670⟩,⟨-2838169403880,4849866214984⟩,⟨-4117072345296,3711866571195⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35943252221,37985865877⟩,⟨-773519145053,-732091090907⟩,⟨317856335867,320395012775⟩,⟨8992995966050,9694788939212⟩,⟨-6530975501168,-6467144718132⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨495712568896,506056491453⟩,⟨817989872837,1096474954836⟩,⟨442730109216,611114832363⟩,⟨-26255609288124,-16486124874458⟩,⟨-9369144905048,-1617278503148⟩,⟨-4117072345296,3711866571195⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505357813684,506349053570⟩,⟨2517543755956,2557704464203⟩,⟨0,0⟩,⟨2303354216540,4586136051397⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227839536849,233050036969⟩,⟨1510994167187,1682148652411⟩,⟨203487725271,281431691283⟩,⟨-7306926531416,-365280656695⟩,⟨-3300979400049,678252769292⟩,⟨-1896001490896,1709395405945⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-769939068594,-721629793006⟩,⟨4867265233246,6227169847864⟩,⟨-6558830844926,-4899702533144⟩,⟨-94942000874936,-47719366936226⟩,⟨2762043143522,66108816810736⟩,⟨-31768336935320,51535609329140⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3532196921422,3601165868306⟩,⟨-15061240907775,-13225450967592⟩,⟨-10094073926345,-8295423281024⟩,⟨38521009179371,102693467240495⟩,⟨26183850366753,94240755559779⟩,⟨-25027585845043,60153382452893⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442725812066,457976954776⟩,⟨269889261203,594630913523⟩,⟨-298294956594,-28429143121⟩,⟨-19664555321958,-8805440968514⟩,⟨-12341057762925,-1794295343686⟩,⟨-9993483158901,1904360316083⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨323939855234,327974104600⟩,⟨1940466224332,1948197165466⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-327974104600,-323939855234⟩,⟨-1948197165466,-1940466224332⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨771537523176,775571772542⟩,⟨-1948197165466,-1940466224332⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1343493671871,1361788149718⟩,⟨-8970964624166,-8666560997089⟩,⟨-4030605358042,-3905515314308⟩,⟨49653094738829,58215619444837⟩,⟨32250335822403,36232836386446⟩,⟨10131365973161,11707561016176⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1361788149718,-1343493671871⟩,⟨8666560997089,8970964624166⟩,⟨3905515314308,4030605358042⟩,⟨-58215619444837,-49653094738829⟩,⟨-36232836386446,-32250335822403⟩,⟨-11707561016176,-10131365973161⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-262276521942,-243982044095⟩,⟨8666560997089,8970964624166⟩,⟨3905515314308,4030605358042⟩,⟨-58215619444837,-49653094738829⟩,⟨-36232836386446,-32250335822403⟩,⟨-11707561016176,-10131365973161⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12377414007,-10971150583⟩,⟨417538805705,454197809582⟩,⟨71221117371,93192271289⟩,⟨-4856903315543,-4209811975024⟩,⟨1506474813454,1937465942171⟩,⟨2553599233534,2753162185022⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430348398059,447005804193⟩,⟨687428066908,1048828723105⟩,⟨-227073839223,64763128168⟩,⟨-24521458637501,-13015252943538⟩,⟨-10834582949471,143170598485⟩,⟨-7439883925367,4657522501105⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101055547311,-100626050579⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4524855743,4769036655⟩,⟨27439747430,29830376721⟩,⟨40014577925,40224844809⟩,⟨-309612448324,-298368693693⟩,⟨246677084567,247790085082⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9825497783,10376036768⟩,⟨7274505156,15858479493⟩,⟨86889653291,87517563587⟩,⟨-913991631595,-776827150904⟩,⟨94437742819,105411467849⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1458234428140,1476207708329⟩,⟨-7437061659270,-7130142767225⟩,⟨-1397507150489,-1327067855793⟩,⟨102136073603493,109483415468676⟩,⟨21520208446992,23300563850608⟩,⟨4766782580637,5205295177519⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13031130166,13930899021⟩,⟨-60535322843,-42425010434⟩,⟨102049760517,105642356819⟩,⟨-528948209447,-91430294940⟩,⟨-294564167121,-210832391807⟩,⟨-179876979142,-160622764830⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13930899021,-13031130166⟩,⟨42425010434,60535322843⟩,⟨-105642356819,-102049760517⟩,⟨91430294940,528948209447⟩,⟨210832391807,294564167121⟩,⟨160622764830,179876979142⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114986446332,-113657180745⟩,⟨-832889324492,-813920018621⟩,⟨-105642356819,-102049760517⟩,⟨2290453550492,2727971464999⟩,⟨210832391807,294564167121⟩,⟨160622764830,179876979142⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86093965042,91108287757⟩,⟨-598322569944,-557224281416⟩,⟨594517255000,615765078923⟩,⟨3196458173810,3879616442158⟩,⟨-3622048787321,-3167783605512⟩,⟨-2511273291115,-2293967223994⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨114182679571,122322268617⟩,⟨-1419563289836,-1297326792612⟩,⟨672681422433,722816023374⟩,⟨19463788946473,22374924727071⟩,⟨-6670365740591,-5365408900783⟩,⟨-4563700694088,-4046183612269⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-122322268617,-114182679571⟩,⟨1297326792612,1419563289836⟩,⟨-722816023374,-672681422433⟩,⟨-22374924727071,-19463788946473⟩,⟨5365408900783,6670365740591⟩,⟨4046183612269,4563700694088⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨977189359159,985328948205⟩,⟨1297326792612,1419563289836⟩,⟨-722816023374,-672681422433⟩,⟨-22374924727071,-19463788946473⟩,⟨5365408900783,6670365740591⟩,⟨4046183612269,4563700694088⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122480983422,125308849316⟩,⟨767173848798,796795675716⟩,⟨180693229445,192397191811⟩,⟨-2787004775769,-2185704845167⟩,⟨-807619105370,-540710511637⟩,⟨-211063296485,-103990336731⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11748811389,12025232391⟩,⟨168270807386,174206404356⟩,⟨21097890704,22096063172⟩,⟨634438133158,788310232888⟩,⟨89475099566,116462208002⟩,⟨-18679676918,-12906863156⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167504611401,178636528480⟩,⟨1465639269235,1887484688163⟩,⟨-5538700452,219376429851⟩,⟨-11154919583512,7280735060436⟩,⟨-5721772819418,6751222542402⟩,⟨-5796433316982,4716989555620⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178636528480,-167504611401⟩,⟨-1887484688163,-1465639269235⟩,⟨-219376429851,5538700452⟩,⟨-7280735060436,11154919583512⟩,⟨-6751222542402,5721772819418⟩,⟨-4716989555620,5796433316982⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49203008369,65545425568⟩,⟨-376490520976,216509383176⟩,⟨-15888704580,286970391735⟩,⟨-14587661591852,10789638926817⟩,⟨-10052201942451,6400025588710⟩,⟨-6612991046516,7505828722927⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27296768401522,28679011311265⟩,⟨-266742142609714,-221566095552411⟩,⟨-101696694218022,-66153885027429⟩,⟨2482198892780544,4369992817005943⟩,⟨470597681447685,2151110233894274⟩,⟨-546265409309018,1157730624967862⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13643867805,14281165675⟩,⟨170919897674,181617996104⟩,⟨40256935680,43854144166⟩,⟨435319366786,667889380446⟩,⟨68068947266,158387584168⟩,⟨11281271056,44164772968⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338726294625,372501483009⟩,⟨778684016863,1987797119737⟩,⟨-321472806642,322960326669⟩,⟨-46512233293342,5295887381196⟩,⟨-19907805242444,13675320257065⟩,⟨-14927543405484,11345072831896⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372501483009,-338726294625⟩,⟨-1987797119737,-778684016863⟩,⟨-322960326669,321472806642⟩,⟨-5295887381196,46512233293342⟩,⟨-13675320257065,19907805242444⟩,⟨-11345072831896,14927543405484⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57846915050,108279509568⟩,⟨-1300369052829,270144706242⟩,⟨-550034165892,386235934810⟩,⟨-29817346018697,33496980349804⟩,⟨-24509903206536,20050975840929⟩,⟨-18784956757263,19585065906589⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238438915805,240885537221⟩,⟨1554700412315,1562991877690⟩,⟨306742660756,308777189903⟩,⟨-3925004181833,-3911333099600⟩,⟨-1551045566142,-1543176045194⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1708139928367,-1620427910820⟩,⟨-5597299328140,-2678696091547⟩,⟨-516192184713,1474261972886⟩,⟨-19783219629741,103614085685165⟩,⟨-58317104242784,41868465435076⟩,⟨-46421310040779,50062446474242⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-194672837911,-180508872364⟩,⟨-1875768836297,-1429033771841⟩,⟨-357726798149,-98282071917⟩,⟨-7145939118661,12400327984829⟩,⟨-7202898992959,6654480770956⟩,⟨-5317924619163,6549344955534⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43766077894,60376664857⟩,⟨-321068423982,133958105849⟩,⟨-50984137393,210495117986⟩,⟨-11070943300494,8488994885229⟩,⟨-8753944559101,5111304725762⟩,⟨-5666340754824,6201612323656⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2588642242,6454889931⟩,⟨-114595833959,37425961240⟩,⟨-34354020155,51285507648⟩,⟨-3726217692087,3949957215815⟩,⟨-2922698620313,2084423211605⟩,⟨-2058192378476,2108313754139⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1742109429,3315418926⟩,⟨-35261183496,14711883818⟩,⟨-5599308092,23117523948⟩,⟨-1294095184185,1119810134763⟩,⟨-1084331074910,612637558708⟩,⟨-641824351507,761685193603⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3033569882,5821380258⟩,⟨-85639490200,13892647841⟩,⟨-20491564635,35210604535⟩,⟨-2430743548607,2600561088916⟩,⟨-2079551670226,1313972881601⟩,⟨-1264926200615,1399397786401⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5821380258,-3033569882⟩,⟨-13892647841,85639490200⟩,⟨-35210604535,20491564635⟩,⟨-2600561088916,2430743548607⟩,⟨-1313972881601,2079551670226⟩,⟨-1399397786401,1264926200615⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3232738016,3421320049⟩,⟨-128488481800,123065451440⟩,⟨-69564624690,71777072283⟩,⟨-6326778781003,6380700764422⟩,⟨-4236671501914,4163974881831⟩,⟨-3457590164877,3373239954754⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49203008369,65545425568⟩,⟨-376490520976,216509383176⟩,⟨-15888704580,286970391735⟩,⟨-14587661591852,10789638926817⟩,⟨-10052201942451,6400025588710⟩,⟨-6612991046516,7505828722927⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3232738016,3421320049⟩,⟨-128488481800,123065451440⟩,⟨-69564624690,71777072283⟩,⟨-6326778781003,6380700764422⟩,⟨-4236671501914,4163974881831⟩,⟨-3457590164877,3373239954754⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (523/5120) u, BivariateJet2.affineZ (593/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000050

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000051Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2088647255872,-2088647217152⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2088647255872,-2088647217088⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-178208325760,-178208325696⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-178208325760,-178208325696⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨91787759872,91787759936⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-100153960256,-100153960192⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨91787882560,91787882624⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-100154106368,-100154106304⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8366223744,-8366223680⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8366200320,-8366200256⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨191941720128,191941720192⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨191941988928,191941988992⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1910438891392,1910438929984⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1910438891392,1910438929984⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2506246686912,-2506246629056⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2095411076672,-2095411037888⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2081919774528,-2081919735808⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-179396321728,-179396321664⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-177022498816,-177022498752⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨89224904384,89224904448⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-97110052032,-97110051968⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨94372299584,94372299648⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-103239404736,-103239404672⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8867105088,-8867105024⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7885147584,-7885147520⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨186334956352,186334956416⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨197611704320,197611704384⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1902523414144,1902523452736⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1918388539136,1918388577728⟩



end LaneCBRB2Cell000051Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000051
open Set LaneCBRB2Cell000051Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112313394790,112313394791⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨131211250892,131211250893⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112313394791,-112313394790⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437442419097,437442419098⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨52202601184,52202601186⟩,⟨-131211250893,-131211250892⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨164515995974,164515995977⟩,⟨968300376883,968300376884⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52202601183,52202601187⟩,⟨-131211250893,-131211250892⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2088647255872,-2088647217088⟩,⟨6471452926143,6471452926269⟩,⟨2923563896770,2923563896831⟩,⟨-38089367969328,-38089367967847⟩,⟨-24555751061433,-24555751060606⟩,⟨-7773656633484,-7773656633162⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312516825529,-312516819719⟩,⟨-871096200623,-871096166427⟩,⟨-393529155173,-393529139721⟩,⟨5699176023991,5699176024552⟩,⟨3563813247494,3563813286584⟩,⟨1163144464347,1163144464473⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨312516819719,312516825529⟩,⟨871096166427,871096200623⟩,⟨393529139721,393529155173⟩,⟨-5699176024552,-5699176023991⟩,⟨-3563813286584,-3563813247494⟩,⟨-1163144464473,-1163144464347⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164515995977,-164515995974⟩,⟨-968300376884,-968300376883⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨934995631799,934995631802⟩,⟨-968300376884,-968300376883⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-178208325760,-178208325696⟩,⟨-1138676467949,-1138676467942⟩,⟨-514412057045,-514412057040⟩,⟨-1179236368136,-1179236368121⟩,⟨760239306715,760239306727⟩,⟨-240670273736,-240670273732⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151543650770,-151543650714⟩,⟨-811358708810,-811358708742⟩,⟨-366541958273,-366541958239⟩,⟨1002791444118,1002791444150⟩,⟨1374327513958,1374327514046⟩,⟨204659640657,204659640668⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151543650714,151543650770⟩,⟨811358708742,811358708810⟩,⟨366541958239,366541958273⟩,⟨-1002791444150,-1002791444118⟩,⟨-1374327514046,-1374327513958⟩,⟨-204659640668,-204659640657⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨464060470433,464060476299⟩,⟨1682454875169,1682454909433⟩,⟨760071097960,760071113446⟩,⟨-6701967468702,-6701967468109⟩,⟨-4938140800630,-4938140761452⟩,⟨-1367804105141,-1367804105004⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨826655316031,826655327869⟩,⟨4072328861525,4072328953733⟩,⟨760071097960,760071113446⟩,⟨-18690431811665,-18690431810575⟩,⟨-4938140800630,-4938140761452⟩,⟨-1367804105141,-1367804105004⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨104405202366,104405202374⟩,⟨-262422501786,-262422501784⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11579172226341,11579172227230⟩,⟨29104252231981,29104252236673⟩,⟨-97030052055754,-97030052040632⟩,⟨146307090252247,146307090288178⟩,⟨-243885059718793,-243885059564159⟩,⟨1626166502228958,1626166502610954⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8705668984606,8705669109943⟩,⟨64768193693972,64768194985209⟩,⟨-64946484915485,-64946483695729⟩,⟨128757144644875,128757151189991⟩,⟨-574623714998414,-574623703233384⟩,⟨1074060187515973,1074060208068140⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨95727877120,95728010496⟩,⟨-704429497531,-704427491922⟩,⟨706366597703,706368608016⟩,⟨8910071306679,8910120368358⟩,⟨-4089198470363,-4089135529897⟩,⟨-1314357443885,-1314278938331⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1195239504896,1195239638272⟩,⟨-704429497531,-704427491922⟩,⟨706366597703,706368608016⟩,⟨8910071306679,8910120368358⟩,⟨-4089198470363,-4089135529897⟩,⟨-1314357443885,-1314278938331⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨91787759872,91787882624⟩,⟨-648011064152,-648009146862⟩,⟨649792947604,649794869421⟩,⟨7814540739505,7814589046388⟩,⟨-3378728099797,-3378667514797⟩,⟨-1593108311946,-1593033687535⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨99779169126,99779313701⟩,⟨-763235768273,-763233359374⟩,⟨765334342423,765336757068⟩,⟨10069046953637,10069110325473⟩,⟨-4846877316391,-4846800502849⟩,⟨-1006632575868,-1006539715262⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-95728010496,-95727877120⟩,⟨704427491922,704429497531⟩,⟨-706368608016,-706366597703⟩,⟨-8910120368358,-8910071306679⟩,⟨4089135529897,4089198470363⟩,⟨1314278938331,1314357443885⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1003783617280,1003783750656⟩,⟨704427491922,704429497531⟩,⟨-706368608016,-706366597703⟩,⟨-8910120368358,-8910071306679⟩,⟨4089135529897,4089198470363⟩,⟨1314278938331,1314357443885⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-100154106368,-100153960192⟩,⟨771606651120,771608950526⟩,⟨-773732988505,-773730683664⟩,⟨-10301348694278,-10301290429581⟩,⟨5022086902974,5022159676630⟩,⟨895137232058,895226659610⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-91434289547,-91434143947⟩,⟨640261176662,640263645815⟩,⟨-642026124389,-642023649330⟩,⟨-7604162989268,-7604097132855⟩,⟨3220937158920,3221016258694⟩,⟨1691624506413,1691719373170⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8344879579,8345169754⟩,⟨-122974591611,-122969713559⟩,⟨123308218034,123313107738⟩,⟨2464883964369,2465013192618⟩,⟨-1625940157471,-1625784244155⟩,⟨684991930545,685179657908⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4172439789,4172584877⟩,⟨-61487295806,-61484856779⟩,⟨61654109017,61656553869⟩,⟨1232441982184,1232506596309⟩,⟨-812970078736,-812892122077⟩,⟨342495965272,342589828954⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4172584877,-4172439789⟩,⟨61484856779,61487295806⟩,⟨-61656553869,-61654109017⟩,⟨-1232506596309,-1232441982184⟩,⟨812892122077,812970078736⟩,⟨-342589828954,-342495965272⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757950798739,757950963091⟩,⟨61484856779,61487295806⟩,⟨-61656553869,-61654109017⟩,⟨-1232506596309,-1232441982184⟩,⟨812892122077,812970078736⟩,⟨-342589828954,-342495965272⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8334451611,8334474836⟩,⟨-122661066296,-122660546160⟩,⟨122998198760,122998720186⟩,⟨2454108294025,2454124138486⟩,⟨-1617150187864,-1617133083216⟩,⟨678724877008,678744031904⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8334474836,-8334451611⟩,⟨122660546160,122661066296⟩,⟨-122998720186,-122998198760⟩,⟨-2454124138486,-2454108294025⟩,⟨1617133083216,1617150187864⟩,⟨-678744031904,-678724877008⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091177152940,1091177176165⟩,⟨122660546160,122661066296⟩,⟨-122998720186,-122998198760⟩,⟨-2454124138486,-2454108294025⟩,⟨1617133083216,1617150187864⟩,⟨-678744031904,-678724877008⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8366223744,-8366200256⟩,⟨123597431946,123597958686⟩,⟨-123938191596,-123937663549⟩,⟨-2486762737257,-2486746600715⟩,⟨1643416788151,1643434176864⟩,⟨-697898771304,-697879336498⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4183111872,-4183100128⟩,⟨61798715973,61798979343⟩,⟨-61969095798,-61968831774⟩,⟨-1243381368629,-1243373300357⟩,⟨821708394075,821717088432⟩,⟨-348949385652,-348939668249⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4183100128,4183111872⟩,⟨-61798979343,-61798715973⟩,⟨61968831774,61969095798⟩,⟨1243373300357,1243381368629⟩,⟨-821717088432,-821708394075⟩,⟨348939668249,348949385652⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766306483744,766306514752⟩,⟨-61798979343,-61798715973⟩,⟨61968831774,61969095798⟩,⟨1243373300357,1243381368629⟩,⟨-821717088432,-821708394075⟩,⟨348939668249,348949385652⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272794288235,272794294042⟩,⟨30665136540,30665266574⟩,⟨-30749680047,-30749549690⟩,⟨-613531034622,-613527073506⟩,⟨404283270804,404287546966⟩,⟨-169686007976,-169681219252⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532612967488,1532613029504⟩,⟨-123597958686,-123597431946⟩,⟨123937663548,123938191596⟩,⟨2486746600714,2486762737258⟩,⟨-1643434176864,-1643416788150⟩,⟨697879336498,697898771304⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1204368788421,1204368948450⟩,⟨-845195118345,-845192487347⟩,⟨847519082571,847521719831⟩,⟨11876826482469,11876895416936⟩,⟨-6095877791701,-6095793723707⟩,⟨-384199446320,-384097569080⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1309225949066,1309226269124⟩,⟨-1690390236690,-1690384974694⟩,⟨1695038165141,1695043439662⟩,⟨23753652964949,23753790833870⟩,⟨-12191755583402,-12191587447418⟩,⟨-768398747948,-768195282855⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨191941720128,191941988992⟩,⟨-1419620289414,-1419615523248⟩,⟨1423523355777,1423528133417⟩,⟨18115817970329,18115950939431⟩,⟨-8400899120071,-8400743074146⟩,⟨-2488344646842,-2488161244343⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨65990226107,65990332360⟩,⟨-480247036894,-480245329215⟩,⟨481567319816,481569031556⟩,⟨5956083741285,5956128018555⟩,⟨-2669124826966,-2669070583574⟩,⟨-1015103809046,-1015037914104⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380248878723,380248902205⟩,⟨12078970054,12079284379⟩,⟨-12112535461,-12112220353⟩,⟨-245123117028,-245113485699⟩,⟨162700824184,162711189223⟩,⟨-70310861112,-70299292037⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179301275044,3179301471381⟩,⟨-100996186310,-100993545730⟩,⟨101271554996,101274202156⟩,⟨2055836082915,2055917199740⟩,⟨-1366879936185,-1366792768960⟩,⟨594231500147,594328639907⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨190814544114,190814863135⟩,⟨-1394723661112,-1394718469259⟩,⟨1398557766808,1398562971061⟩,⟨17433970313614,17434107095022⟩,⟨-7888435559008,-7888270243536⟩,⟨-2810856512974,-2810657270984⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨382756264242,382756852127⟩,⟨-2814343950526,-2814333992507⟩,⟨2822081122585,2822091104478⟩,⟨35549788283943,35550058034453⟩,⟨-16289334679079,-16289013317682⟩,⟨-5299201159816,-5298818515327⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522495077629,522495304223⟩,⟨84769446958,84772828040⟩,⟨-85006184938,-85002795776⟩,⟨-1692386238713,-1692296240888⟩,⟨1113842042196,1113950311412⟩,⟨-465415835866,-465285774783⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360183149883,360183384188⟩,⟨87654011663,87657526807⟩,⟨-87898824509,-87895300957⟩,⟨-1742865255383,-1742771248909⟩,⟨1144613631459,1144726402834⟩,⟨-474103594262,-473968433433⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720366299766,720366768376⟩,⟨175308023326,175315053614⟩,⟨-175797649018,-175790601914⟩,⟨-3485730510766,-3485542497818⟩,⟨2289227262918,2289452805668⟩,⟨-948207188524,-947936866866⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524278492652,1524278577893⟩,⟨-937412526,-936365650⟩,⟨938943362,939992836⟩,⟨32622462228,32654443233⟩,⟨-26301093648,-26266600286⟩,⟨19135304594,19173894296⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨998660523295,998661228789⟩,⟨242419417839,242429863964⟩,⟨-243097208374,-243086737197⟩,⟨-4811275092398,-4810992862735⟩,⟨3156676626901,3157012436475⟩,⟨-1302285430364,-1301884965069⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67681615922,67681618805⟩,⟨15216344938,15216409788⟩,⟨-15258296592,-15258231580⟩,⟨-302729704097,-302727717562⟩,⟨198894158472,198896299164⟩,⟨-82479964383,-82477571794⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50885653399,50885656296⟩,⟨262116800828,262116866105⟩,⟨35315213565,35315265556⟩,⟨-1265398061751,-1265396032929⟩,⟨-200430575970,-200428661896⟩,⟨-167303805033,-167301911393⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136314386109,2136314558998⟩,⟨-344567237158,-344565754764⟩,⟨345514254720,345515740798⟩,⟨6960356426668,6960401929607⟩,⟨-4609441275680,-4609392376442⟩,⟨1973493390877,1973547888178⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2977815830292,2977816191778⟩,⟨-720440180715,-720437052092⟩,⟨722420228024,722423364432⟩,⟨14611196038833,14611292265333⟩,⟨-9695934020007,-9695830889942⟩,⟨4184708529777,4184823142880⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137814007963,137814032540⟩,⟨676550814634,676551224295⟩,⟨129078241420,129078540898⟩,⟨-3094375301518,-3094363321701⟩,⟨-842477163805,-842466190430⟩,⟨-213034129483,-213023360772⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8772153294794,8772154859173⟩,⟨-43063925049425,-43063883614061⟩,⟨-8216123792420,-8216101799575⟩,⟨619777528560093,619779099600156⟩,⟨134293024870295,134294021639849⟩,⟨28949980243410,28950750181443⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7967540295615,7967547345097⟩,⟨-37179899674283,-37179750721363⟩,⟨-9402002106173,-9401892971464⟩,⟨505553669276859,505558588976008⟩,⟨154869138851218,154873316206201⟩,⟨19537586659807,19541667625141⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15935080591230,15935094690194⟩,⟨-74359799348566,-74359501442726⟩,⟨-18804004212346,-18803785942928⟩,⟨1011107338553718,1011117177952016⟩,⟨309738277702436,309746632412402⟩,⟨39075173319614,39083335250282⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10763861442032,10763861442129⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311394,2063168215367208⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9664349814256,9664349814353⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311405,2063168215367197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2389873986368,2389874044224⟩,⟨-11988464342936,-11988464342527⟩,⟨0,0⟩,⟨104010778944236,104010778977589⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7348378572158,7348378572293⟩,⟨-43250734975116,-43250734973480⟩,⟨-19539087856358,-19539087855594⟩,⟨509126212640652,509126212669782⟩,⟨279115958796200,279115958811454⟩,⟨103907535650150,103907535656357⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6248866944382,6248866944517⟩,⟨-43250734975116,-43250734973479⟩,⟨-19539087856358,-19539087855593⟩,⟨509126212640651,509126212669773⟩,⟨279115958796198,279115958811450⟩,⟨103907535650149,103907535656356⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1910438891392,1910438929984⟩,⟨-7610129394396,-7610129393911⟩,⟨-3437975953956,-3437975953732⟩,⟨36910131592222,36910131608344⟩,⟨25315990363710,25315990371617⟩,⟨7532986357859,7532986361233⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100840757001,100840757003⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139900055361,139900055365⟩,⟨678533726155,678533726164⟩,⟨306536526985,306536526990⟩,⟨-1705494687256,-1705494687251⟩,⟨-1540959271654,-1540959271644⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4300312877760,4300312974208⟩,⟨-19598593737332,-19598593736438⟩,⟨-3437975953956,-3437975953732⟩,⟨140920910536458,140920910585933⟩,⟨25315990363710,25315990371617⟩,⟨7532986357859,7532986361233⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨765512528484,765513704254⟩,⟨-5628687901052,-5628667985014⟩,⟨5644162245170,5644182208956⟩,⟨71099576567886,71100116068906⟩,⟨-32578669358158,-32578026635364⟩,⟨-10598402319632,-10597637030654⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5065825406244,5065826678462⟩,⟨-25227281638384,-25227261721452⟩,⟨2206186291214,2206206255224⟩,⟨212020487104344,212021026654839⟩,⟨-7262678994448,-7262036263747⟩,⟨-3065415961773,-3064650669421⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨464607791218,464607907909⟩,⟨1717194812334,1717197651363⟩,⟨202338465616,202340296602⟩,⟨-30833231616141,-30833147890889⟩,⟨1089379010176,1089453843110⟩,⟨-281141970949,-281071782817⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38082976871,38082979061⟩,⟨-775559219330,-775559208270⟩,⟨319124126993,319124145312⟩,⟨9623656040551,9623656070101⟩,⟨-6498957778804,-6498957686573⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨502690768089,502690886970⟩,⟨941635593004,941638443093⟩,⟨521462592609,521464441914⟩,⟨-21209575575590,-21209491820788⟩,⟨-5409578768628,-5409503843463⟩,⟨-281141970949,-281071782817⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505853361827,505853374074⟩,⟨2537541677330,2537541800300⟩,⟨0,0⟩,⟨3442964323895,3442967248197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨231273420465,231273480759⟩,⟨1593369511439,1593371163757⟩,⟨239909791651,239910648272⟩,⟨-3837439965446,-3837386120854⟩,⟨-1285316657701,-1285277800256⟩,⟨-129345257482,-129312962829⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-765513704254,-765512528484⟩,⟨5628667985014,5628687901052⟩,⟨-5644182208956,-5644162245170⟩,⟨-71100116068906,-71099576567886⟩,⟨32578026635364,32578669358158⟩,⟨10597637030654,10598402319632⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3534799173506,3534800445724⟩,⟨-13969925752318,-13969905835386⟩,⟨-9082158162912,-9082138198902⟩,⟨69820794467552,69821334018047⟩,⟨57894016999074,57894659729775⟩,⟨18130623388513,18131388680865⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449762046685,449762208574⟩,⟨403894835666,403898155060⟩,⟨-170120408794,-170117513869⟩,⟨-13841401522990,-13841306315195⟩,⟨-7087192424807,-7087090988462⟩,⟨-3876197675948,-3876088766829⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨329031991948,329031991954⟩,⟨1936600753766,1936600753768⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-329031991954,-329031991948⟩,⟨-1936600753768,-1936600753766⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨770479635822,770479635828⟩,⟨-1936600753768,-1936600753766⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1338734601904,1338734628958⟩,⟨-8697686276932,-8697686208571⟩,⟨-3929294066559,-3929294035671⟩,⟨52672539266792,52672539280029⟩,⟨33671793274370,33671793358036⟩,⟨10749935115787,10749935118564⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1338734628958,-1338734601904⟩,⟨8697686208571,8697686276932⟩,⟨3929294035671,3929294066559⟩,⟨-52672539280029,-52672539266792⟩,⟨-33671793358036,-33671793274370⟩,⟨-10749935118564,-10749935115787⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-239223001182,-239222974128⟩,⟨8697686208571,8697686276932⟩,⟨3929294035671,3929294066559⟩,⟨-52672539280029,-52672539266792⟩,⟨-33671793358036,-33671793274370⟩,⟨-10749935118564,-10749935115787⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11357827067,-11357825780⟩,⟨441496549717,441496556225⟩,⟨91379734961,91379747208⟩,⟨-4576679342868,-4576679325714⟩,⟨1632035989848,1632036051895⟩,⟨2616166239779,2616166264537⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438404219618,438404382794⟩,⟨845391385383,845394711285⟩,⟨-78740673833,-78737766661⟩,⟨-18418080865858,-18417985640909⟩,⟨-5455156434959,-5455054936567⟩,⟨-1260031436169,-1259922502292⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100840757003,-100840757001⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4787716371,4787716372⟩,⟨29503846618,29503846624⟩,⟨40119652736,40119652738⟩,⟨-313215607116,-313215607105⟩,⟨247233542879,247233542884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10406473674,10406473929⟩,⟨11926302722,11926304302⟩,⟨87203183662,87203185778⟩,⟨-871280796714,-871280779813⟩,⟨99938903425,99938916483⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1462430324777,1462430345721⟩,⟨-7204329693659,-7204329324178⟩,⟨-1344636681885,-1344636615973⟩,⟨104046085270141,104046092483245⟩,⟨21984122262163,21984123720800⟩,⟨4892434516881,4892434793432⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13841365830,13841366368⟩,⟨-52323487008,-52323479509⟩,⟨103260075438,103260080852⟩,⟨-330398221150,-330398060950⟩,⟨-244968918530,-244968834535⟩,⟨-166983421648,-166983402264⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13841366368,-13841365830⟩,⟨52323479509,52323487008⟩,⟨-103260080852,-103260075438⟩,⟨330398060950,330398221150⟩,⟨244968834535,244968918530⟩,⟨166983402264,166983421648⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114682123371,-114682122831⟩,⟨-822561358687,-822561351186⟩,⟨-103260080852,-103260075438⟩,⟨2529421316502,2529421476702⟩,⟨244968834535,244968918530⟩,⟨166983402264,166983421648⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨90703797042,90703798882⟩,⟨-589297661933,-589297657273⟩,⟨596842912793,596842928174⟩,⟨3568742680336,3568742681367⟩,⟨-3325914399896,-3325914360604⟩,⟨-2377957165339,-2377957164965⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨120642638072,120642642248⟩,⟨-1378127176474,-1378127116512⟩,⟨682919125786,682919165302⟩,⟨21052438846097,21052440141735⟩,⟨-5800154034736,-5800153419628⟩,⟨-4219062358107,-4219062172132⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-120642642248,-120642638072⟩,⟨1378127116512,1378127176474⟩,⟨-682919165302,-682919125786⟩,⟨-21052440141735,-21052438846097⟩,⟨5800153419628,5800154034736⟩,⟨4219062172132,4219062358107⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨978868985528,978868989704⟩,⟨1378127116512,1378127176474⟩,⟨-682919165302,-682919125786⟩,⟨-21052440141735,-21052438846097⟩,⟨5800153419628,5800154034736⟩,⟨4219062172132,4219062358107⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124549683520,124549684056⟩,⟨779433030458,779433040680⟩,⟨186008646925,186008653126⟩,⟨-2496091790721,-2496091545274⟩,⟨-671109634618,-671109509351⟩,⟨-153842343127,-153842296081⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11961664583,11961664697⟩,⟨171590876402,171590878776⟩,⟨21540626502,21540627736⟩,⟨703089882546,703089940900⟩,⟨103398981878,103399009154⟩,⟨-15438436427,-15438430184⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨173358866173,173359021209⟩,⟨1677878988122,1677884471477⟩,⟨107615438487,107618109105⟩,⟨-2019629254590,-2019418940783⟩,⟨476851830238,476984498718⟩,⟨-535427660845,-535329979647⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-173359021209,-173358866173⟩,⟨-1677884471477,-1677878988122⟩,⟨-107618109105,-107615438487⟩,⟨2019418940783,2019629254590⟩,⟨-476984498718,-476851830238⟩,⟨535329979647,535427660845⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57914399256,57914614586⟩,⟨-84514960038,-84507824365⟩,⟨132291682546,132295209785⟩,⟨-1818021024663,-1817756866264⟩,⟨-1762301156419,-1762129630494⟩,⟨405984722165,406114698016⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27687745113281,27687770170022⟩,⟨-239495409919645,-239494792096922⟩,⟨-82498785610140,-82498361611405⟩,⟨3321106814647968,3321128543856865⟩,⟨1267739044652178,1267756339102506⟩,⟨294661188786097,294676833420644⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14108649033,14108649156⟩,⟨176584103006,176584106084⟩,⟨42141106144,42141107732⟩,⟨539563925592,539564012622⟩,⟨111676473178,111676514468⟩,⟨28081924936,28081939945⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355281989248,355282313868⟩,⟨1373572487917,1373584544132⟩,⟨2588225231,2594675445⟩,⟨-20724225442500,-20723731971283⟩,⟨-3349142580006,-3348824584130⟩,⟨-1835709507001,-1835474968616⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355282313868,-355281989248⟩,⟨-1373584544132,-1373572487917⟩,⟨-2594675445,-2588225231⟩,⟨20723731971283,20724225442500⟩,⟨3348824584130,3349142580006⟩,⟨1835474968616,1835709507001⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83121905750,83122393546⟩,⟨-528193158749,-528177776632⟩,⟨-81335349278,-81325991892⟩,⟨2305651105425,2306239801591⟩,⟨-2106331850829,-2105912356561⟩,⟨575443532447,575787004709⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨240740812362,240740812368⟩,⟨1553418564349,1553418564360⟩,⟨306536526985,306536526990⟩,⟨-3904517942808,-3904517942803⟩,⟨-1540959271654,-1540959271644⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1662074733022,-1662073254633⟩,⟨-4165383562456,-4165341797164⟩,⟨464750813171,464774991077⟩,⟨42455186797901,42456695077829⟩,⟨-7706301485344,-7705233792390⟩,⟨1875464301997,1876359237930⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-188275301185,-188275132906⟩,⟨-1650071835387,-1650066038829⟩,⟨-228533932194,-228530933680⟩,⟨2676817463551,2677051356800⟩,⟨-233685114207,-233538840480⟩,⟨602250102787,602359943364⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52465511177,52465679462⟩,⟨-96653271038,-96647474469⟩,⟨78002594791,78005593310⟩,⟨-1227700479257,-1227466586003⟩,⟨-1774644385861,-1774498112124⟩,⟨254175802902,254285643482⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4378266782,4378308755⟩,⟨-34210815089,-34209324481⟩,⟨5716930319,5717764478⟩,⟨65194807702,65256264632⟩,⟨-301478239369,-301437189627⟩,⟨41429426443,41460410660⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2503502276,2503518337⟩,⟨-9224058044,-9223475266⟩,⟨7444115924,7444425966⟩,⟨-100174303043,-100149567669⟩,⟨-183076589132,-183060736750⟩,⟨35324534513,35335945815⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4349920448,4349948443⟩,⟨-33354897884,-33353773796⟩,⟨5106351390,5106940583⟩,⟨37663440345,37715028872⟩,⟨-283144765714,-283112877250⟩,⟨31974830672,31996708381⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4349948443,-4349920448⟩,⟨33353773796,33354897884⟩,⟨-5106940583,-5106351390⟩,⟨-37715028872,-37663440345⟩,⟨283112877250,283144765714⟩,⟨-31996708381,-31974830672⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨28318339,28388307⟩,⟨-857041293,-854426597⟩,⟨609989736,611413088⟩,⟨27479778830,27592824287⟩,⟨-18365362119,-18292423913⟩,⟨9432718062,9485579988⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57914399256,57914614586⟩,⟨-84514960038,-84507824365⟩,⟨132291682546,132295209785⟩,⟨-1818021024663,-1817756866264⟩,⟨-1762301156419,-1762129630494⟩,⟨405984722165,406114698016⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨28318339,28388307⟩,⟨-857041293,-854426597⟩,⟨609989736,611413088⟩,⟨27479778830,27592824287⟩,⟨-18365362119,-18292423913⟩,⟨9432718062,9485579988⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112098646425,112528143156⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨129278515609,133143986176⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112528143156,-112098646425⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437227670732,437657167463⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨51408409722,52997547623⟩,⟨-133143986176,-129278515609⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163507056147,165525690779⟩,⟨966367641600,970233112167⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨50978912991,53427044354⟩,⟨-133143986176,-129278515609⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2095411076672,-2081919735808⟩,⟨6419139250500,6524382577850⟩,⟨2904303891998,2943048183637⟩,⟨-38714977583503,-37476046343098⟩,⟨-24857450888404,-24259382959326⟩,⟨-7877618019124,-7671570617347⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-315453113156,-309599788248⟩,⟨-894454068059,-847600796976⟩,⟨-402176280614,-384827974944⟩,⟨5455307026942,5941497887182⟩,⟨3444982970457,3681847510129⟩,⟨1123895242274,1202112194597⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309599788248,315453113156⟩,⟨847600796976,894454068059⟩,⟨384827974944,402176280614⟩,⟨-5941497887182,-5455307026942⟩,⟨-3681847510129,-3444982970457⟩,⟨-1202112194597,-1123895242274⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-165525690779,-163507056147⟩,⟨-970233112167,-966367641600⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨933985936997,936004571629⟩,⟨-970233112167,-966367641600⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-179396321728,-177022498752⟩,⟨-1142182709851,-1135178706228⟩,⟨-515220974475,-513605299083⟩,⟨-1186509819202,-1172002789711⟩,⟨756364857073,764106463892⟩,⟨-241427781056,-239915974131⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152718509772,-150372692920⟩,⟨-816743907697,-805980285852⟩,⟨-368208977954,-364876578250⟩,⟨985365953245,1020210080945⟩,⟨1365923600315,1382739125526⟩,⟨202951369283,206366311172⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150372692920,152718509772⟩,⟨805980285852,816743907697⟩,⟨364876578250,368208977954⟩,⟨-1020210080945,-985365953245⟩,⟨-1382739125526,-1365923600315⟩,⟨-206366311172,-202951369283⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨459972481168,468171622928⟩,⟨1653581082828,1711197975756⟩,⟨749704553194,770385258568⟩,⟨-6961707968127,-6440672980187⟩,⟨-5064586635655,-4810906570772⟩,⟨-1408478505769,-1326846611557⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨821625464596,831709708644⟩,⟨4036424608767,4108090577245⟩,⟨749704553194,770385258568⟩,⟨-19054291702082,-18324781471087⟩,⟨-5064586635655,-4810906570772⟩,⟨-1408478505769,-1326846611557⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨101957825982,106854088708⟩,⟨-266287972352,-258557031218⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11313800288150,11857116488813⟩,⟨27376234729689,30967779837765⟩,⟨-101794089208791,-92588062973097⟩,⟨132485673935757,161759967355478⟩,⟨-298886245266214,-192340548161785⟩,⟨1515414659403009,1747817288903870⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8454395736496,8969144710381⟩,⟨61991443981635,67726715921898⟩,⟨-69286329278450,-60879904143993⟩,⟨94522749525792,165210900860128⟩,⟨-642369956537029,-511435376370920⟩,⟨974579459944903,1182195361049101⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨92945133568,98540741888⟩,⟨-780774610579,-635390634441⟩,⟨623997739595,798754317620⟩,⟨6722465447368,11350382448757⟩,⟨-7360860911916,-1066939737344⟩,⟨-5308249462212,2904015860732⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1192456761344,1198052369664⟩,⟨-780774610579,-635390634441⟩,⟨623997739595,798754317620⟩,⟨6722465447368,11350382448757⟩,⟨-7360860911916,-1066939737344⟩,⟨-5308249462212,2904015860732⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨89224904384,94372299648⟩,⟨-719917728537,-583129259152⟩,⟨572673438793,736496021014⟩,⟨5698163109891,10156421202750⟩,⟨-6483405157335,-496953975513⟩,⟨-5387835929829,2379391343023⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨96767362731,102830160562⟩,⟨-851453147465,-683984668664⟩,⟨671720456722,871060442508⟩,⟨7399334394234,13063320831071⟩,⟨-8742240490288,-1287422859085⟩,⟨-5676308727999,3911966673740⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-98540741888,-92945133568⟩,⟨635390634441,780774610579⟩,⟨-798754317620,-623997739595⟩,⟨-11350382448757,-6722465447368⟩,⟨1066939737344,7360860911916⟩,⟨-2904015860732,5308249462212⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1000970885888,1006566494208⟩,⟨635390634441,780774610579⟩,⟨-798754317620,-623997739595⟩,⟨-11350382448757,-6722465447368⟩,⟨1066939737344,7360860911916⟩,⟨-2904015860732,5308249462212⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-103239404736,-97110051968⟩,⟨694061837710,857638094282⟩,⟨-877387816511,-681616936723⟩,⟨-13136745250624,-7781333238460⟩,⟨1595727330937,8769879741383⟩,⟨-3890039728113,5408268207391⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-94512257137,-88406827441⟩,⟨558547059449,729020896262⟩,⟨-748107345869,-545529281867⟩,⟨-10630344932425,-4800164969667⟩,⟨-484522898055,7146509685146⟩,⟨-3285958255726,6498544327213⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2255105594,14423333121⟩,⟨-292906088016,45036227598⟩,⟨-76386889147,325531160641⟩,⟨-3231010538191,8263155861404⟩,⟨-9226763388343,5859086826061⟩,⟨-8962266983725,10410511000953⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1127552797,7211666561⟩,⟨-146453044008,22518113799⟩,⟨-38193444574,162765580321⟩,⟨-1615505269096,4131577930702⟩,⟨-4613381694172,2929543413031⟩,⟨-4481133491863,5205255500477⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7211666561,-1127552797⟩,⟨-22518113799,146453044008⟩,⟨-162765580321,38193444574⟩,⟨-4131577930702,1615505269096⟩,⟨-2929543413031,4613381694172⟩,⟨-5205255500477,4481133491863⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754911717055,760995850083⟩,⟨-22518113799,146453044008⟩,⟨-162765580321,38193444574⟩,⟨-4131577930702,1615505269096⟩,⟨-2929543413031,4613381694172⟩,⟨-5205255500477,4481133491863⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7856940877,8831446223⟩,⟨-139949605680,-107423088384⟩,⟨105496934798,143172370454⟩,⟨1870906466586,3143366665861⟩,⟨-2453801765084,-901580599106⟩,⟨-243209180761,1681059688577⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8831446223,-7856940877⟩,⟨107423088384,139949605680⟩,⟨-143172370454,-105496934798⟩,⟨-3143366665861,-1870906466586⟩,⟨901580599106,2453801765084⟩,⟨-1681059688577,243209180761⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090680181553,1091654686899⟩,⟨107423088384,139949605680⟩,⟨-143172370454,-105496934798⟩,⟨-3143366665861,-1870906466586⟩,⟨901580599106,2453801765084⟩,⟨-1681059688577,243209180761⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8867105088,-7885147520⟩,⟨108196242078,141082804429⟩,⟨-144331664546,-106256225432⟩,⟨-3186922015378,-1895018831314⟩,⟨918525552102,2492190450035⟩,⟨-1713617807249,234909946316⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4433552544,-3942573760⟩,⟨54098121039,70541402215⟩,⟨-72165832273,-53128112716⟩,⟨-1593461007689,-947509415657⟩,⟨459262776051,1246095225018⟩,⟨-856808903625,117454973158⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3942573760,4433552544⟩,⟨-70541402215,-54098121039⟩,⟨53128112716,72165832273⟩,⟨947509415657,1593461007689⟩,⟨-1246095225018,-459262776051⟩,⟨-117454973158,856808903625⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766065957376,766556955424⟩,⟨-70541402215,-54098121039⟩,⟨53128112716,72165832273⟩,⟨947509415657,1593461007689⟩,⟨-1246095225018,-459262776051⟩,⟨-117454973158,856808903625⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272670045388,272913671725⟩,⟨26855772096,34987401420⟩,⟨-35793092614,-26374233699⟩,⟨-785841666466,-467726616646⟩,⟨225395149776,613450441271⟩,⟨-420264922145,60802295191⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532131914752,1533113910848⟩,⟨-141082804430,-108196242078⟩,⟨106256225432,144331664546⟩,⟨1895018831314,3186922015378⟩,⟨-2492190450036,-918525552102⟩,⟨-234909946316,1713617807250⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1201039202646,1207753229049⟩,⟨-942068416157,-758150668980⟩,⟨744556620876,963762403007⟩,⟨8978431392111,15164823941409⟩,⟨-10384983330990,-2213072928275⟩,⟨-5481695569088,5042058031148⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1302566777516,1315994830322⟩,⟨-1884136832314,-1516301337960⟩,⟨1489113241753,1927524806014⟩,⟨17956862784228,30329647882808⟩,⟨-20769966661974,-4426145856550⟩,⟨-10958693108527,10084116062293⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨186334956352,197611704384⟩,⟨-1590421613089,-1266867402427⟩,⟨1244151790460,1627045901695⟩,⟨12702417739712,24141909034945⟩,⟨-16098645086840,-1344548552519⟩,⟨-11658044789897,7104299289608⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨63815032602,68202185177⟩,⟨-542409170649,-423126260318⟩,⟨413842066333,556258174865⟩,⟨4037288401784,8032611886999⟩,⟨-5400644022991,-97112224951⟩,⟨-4376947773168,2467034023446⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379956398988,380539628698⟩,⟨2403939423,21953199015⟩,⟨-23557730300,-926521042⟩,⟨-634774697812,133990692793⟩,⟨-299324308808,636768691873⟩,⟨-653705035466,505025781638⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176872337188,3181748808113⟩,⟨-183835737433,-20068891850⟩,⟨7734908130,197272056751⟩,⟨-1121782360581,5336836565052⟩,⟨-5355086892273,2506439248877⟩,⟨-4229040152847,5498577696900⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨184383872483,197362370635⟩,⟨-1581018051393,-1223724037598⟩,⟨1196182907653,1621927522343⟩,⟨11610996064433,23757061710891⟩,⟨-16150792012501,-135648134968⟩,⟨-12922442764966,7679742308437⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨370718828835,394974075019⟩,⟨-3171439664482,-2490591440025⟩,⟨2440334698113,3248973424038⟩,⟨24313413804145,47898970745836⟩,⟨-32249437099341,-1480196687487⟩,⟨-24580487554863,14784041598045⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518313482231,526701736675⟩,⟨-31170550124,202726657740⟩,⟨-225307178264,52869023096⟩,⟨-5725108177777,2275267069617⟩,⟨-4098561284362,6396217705212⟩,⟨-7216648396309,6251169225132⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355867924412,364541698074⟩,⟨-32360720921,210467276577⟩,⟨-233909978742,54887696717⟩,⟨-5949935148031,2402646806246⟩,⟨-4300070555661,6651004640747⟩,⟨-7503938020354,6539884578317⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711735848824,729083396148⟩,⟨-64721441842,420934553154⟩,⟨-467819957484,109775393434⟩,⟨-11899870296062,4805293612492⟩,⟨-8600141111322,13302009281494⟩,⟨-15007876040708,13079769156634⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523300468529,1525256969971⟩,⟨-33659716046,31753363602⟩,⟨-36916145022,38834729748⟩,⟨-1248347834547,1316015548792⟩,⟨-1590609850930,1535276212982⟩,⟨-1915969634893,1956826988011⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨986062834256,1011394062212⟩,⟨-112102107200,604981515857⟩,⟨-673444991871,178033079120⟩,⟨-17361205086374,7562925781483⟩,⟨-13012601396497,19499948696782⟩,⟨-22122644174593,19473408753266⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67619979428,67740868158⟩,⟨13320031204,17368693418⟩,⟨-17768660342,-13081195902⟩,⟨-388801167165,-229758224179⟩,⟨109514436952,303245018478⟩,⟨-207365597448,32514295725⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50529976773,51241602450⟩,⟨258193745897,266237596514⟩,⟨32665993010,37688298628⟩,⟨-1370238682300,-1168875516890⟩,⟨-287499300158,-102338392988⟩,⟨-268534645679,-74845001481⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134973514513,2137711147621⟩,⟨-393440150316,-301535538790⟩,⟨296128844866,402500304866⟩,⟨5302581953058,8923632471616⟩,⟨-6987055828060,-2580780050590⟩,⟨-634560494384,4816689265797⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2975012702095,2980736733473⟩,⟨-822895209516,-630269217816⟩,⟨618968152727,841844871289⟩,⟨11127958786824,18739846451324⟩,⟨-14691165721613,-5438053688499⟩,⟨-1284290252032,10153544540035⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136721903560,138914153199⟩,⟨660259688138,692795488090⟩,⟨116832043669,141404940553⟩,⟨-3601777789717,-2585350456343⟩,⟨-1346923829912,-341697487159⟩,⟨-751062320352,328395312410⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8702682856820,8842224896936⟩,⟨-44805209361253,-41363896598616⟩,⟨-9145091264466,-7319284609602⟩,⟨555172459076626,687010790345384⟩,⟨90983832245444,179789475683567⟩,⟨-8926743220261,67490167128381⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7804730670092,8133587250545⟩,⟨-42115929998018,-32230690061811⟩,⟨-13827996624157,-5132338630753⟩,⟨308964992370511,701909122140452⟩,⟨-35337500872288,350573798519310⟩,⟨-189082227468861,229888288069740⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15609461340184,16267174501090⟩,⟨-84231859996036,-64461380123622⟩,⟨-27655993248314,-10264677261506⟩,⟨617929984741022,1403818244280904⟩,⟨-70675001744576,701147597038620⟩,⟨-378164454937722,459776576139480⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10743319721704,10784481866367⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239228,2075048233589864⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9643808093928,9684970238591⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239235,2075048233589852⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2387534470720,2392217527616⟩,⟨-12060075023605,-11917323006543⟩,⟨0,0⟩,⟨100606314842521,107411991083576⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7303553991680,7393722620312⟩,⟨-43873546973752,-42639412728148⟩,⟨-19790679223678,-19291965403189⟩,⟨497872548042369,520681725000062⟩,⟨273773844662339,284590950875697⟩,⟨101917485526038,105946896914551⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6204042363904,6294210992536⟩,⟨-43873546973752,-42639412728148⟩,⟨-19790679223679,-19291965403188⟩,⟨497872548042372,520681725000058⟩,⟨273773844662340,284590950875697⟩,⟨101917485526038,105946896914552⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1902523414144,1918388577728⟩,⟨-7775490917051,-7448515811066⟩,⟨-3507403826685,-3370039598067⟩,⟨31984983614836,41818718418818⟩,⟨23020959661577,27606693405843⟩,⟨6615079326297,8447159444112⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100626050579,101055547311⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138891929092,140910563725⟩,⟨674822587020,682243535540⟩,⟨305518361311,307554091929⟩,⟨-1712309844053,-1698693120000⟩,⟨-1544894032124,-1537024511176⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4290057884864,4310606105344⟩,⟨-19835565940656,-19365838817609⟩,⟨-3507403826685,-3370039598067⟩,⟨132591298457357,149230709502394⟩,⟨23020959661577,27606693405843⟩,⟨6615079326297,8447159444112⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨741437657670,789948150038⟩,⟨-6342879328964,-4981182880050⟩,⟨4880669396226,6497946848076⟩,⟨48626827608290,95797941491672⟩,⟨-64498874198682,-2960393374974⟩,⟨-49160975109726,29568083196090⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5031495542534,5100554255382⟩,⟨-26178445269620,-24347021697659⟩,⟨1373265569541,3127907250009⟩,⟨181218126065647,245028650994066⟩,⟨-41477914537105,24646300030869⟩,⟨-42545895783429,38015242640202⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨460476735453,468789314134⟩,⟨1595563879389,1832307697449⟩,⟨125679699212,287484344052⟩,⟨-35297225554701,-26269515383020⟩,⟨-2720038485071,4755336151960⟩,⟨-3910371364538,3493961368046⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37060715902,39112254594⟩,⟨-796479605795,-754827146557⟩,⟨317856335867,320395012775⟩,⟨9271714624854,9983104170053⟩,⟨-6530975501168,-6467144718132⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497537451355,507901568728⟩,⟨799084273594,1077480550892⟩,⟨443536035079,607879356827⟩,⟨-26025510929847,-16286411212967⟩,⟨-9251013986239,-1711808566172⟩,⟨-3910371364538,3493961368046⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505357813684,506349053570⟩,⟨2517543755956,2557704464203⟩,⟨0,0⟩,⟨2303354216540,4586136051397⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228678289788,233899735242⟩,⟨1506483190919,1677693368853⟩,⟨203858145121,279941684325⟩,⟨-7283714325788,-354162546701⟩,⟨-3244732216300,627278414148⟩,⟨-1800811187005,1609045313599⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-789948150038,-741437657670⟩,⟨4981182880050,6342879328964⟩,⟨-6497946848076,-4880669396226⟩,⟨-95797941491672,-48626827608290⟩,⟨2960393374974,64498874198682⟩,⟨-29568083196090,49160975109726⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3500109734826,3569168447674⟩,⟨-14854383060606,-13022959488645⟩,⟨-10005350674761,-8250708994293⟩,⟨36793356965685,100603881894104⟩,⟨25981353036551,92105567604525⟩,⟨-22953003869793,57608134553838⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442139019563,457415388147⟩,⟨244484558835,569578455557⟩,⟨-309693690047,-43878142357⟩,⟨-19344802764289,-8499989272185⟩,⟨-12096278535709,-1771354647221⟩,⟨-9669974747297,1690756254897⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨327014112294,331051381558⟩,⟨1932735283200,1940466224334⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-331051381558,-327014112294⟩,⟨-1940466224334,-1932735283200⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨768460246218,772497515482⟩,⟨-1940466224334,-1932735283200⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1329693633368,1347826046207⟩,⟨-8848579141436,-8550125515976⟩,⟨-3991457346229,-3868456788998⟩,⟨48540830007346,56826148541846⟩,⟨31742433234808,35612793439087⟩,⟨9983817783710,11519270064310⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1347826046207,-1329693633368⟩,⟨8550125515976,8848579141436⟩,⟨3868456788998,3991457346229⟩,⟨-56826148541846,-48540830007346⟩,⟨-35612793439087,-31742433234808⟩,⟨-11519270064310,-9983817783710⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-248314418431,-230182005592⟩,⟨8550125515976,8848579141436⟩,⟨3868456788998,3991457346229⟩,⟨-56826148541846,-48540830007346⟩,⟨-35612793439087,-31742433234808⟩,⟨-11519270064310,-9983817783710⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12065998315,-10672400490⟩,⟨423491376517,460036064173⟩,⟨80520419072,102418040592⟩,⟨-4904289522876,-4261213525211⟩,⟨1416369213167,1843878253699⟩,⟨2516892118101,2714674023343⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430073021248,446742987657⟩,⟨667975935352,1029614519730⟩,⟨-229173270975,58539898235⟩,⟨-24249092287165,-12761202797396⟩,⟨-10679909322542,72523606478⟩,⟨-7153082629196,4405430278240⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101055547311,-100626050579⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4665531993,4910452125⟩,⟨28306971555,30701513739⟩,⟨40014577925,40224844809⟩,⟨-318844279198,-307591464872⟩,⟨246677084567,247790085082⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10130969219,10683715702⟩,⟨7606512845,16229066691⟩,⟨86889653291,87517563587⟩,⟨-940315667999,-801838206943⟩,⟨94437742819,105411467849⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1453542993487,1471383095714⟩,⟨-7356849673585,-7054284262686⟩,⟨-1379621123601,-1310226139186⟩,⟨100496639676136,107690640283755⟩,⟨21125300592471,22865849524009⟩,⟨4680952452183,5109494772283⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13393036465,14297109996⟩,⟨-61429179300,-43280635817⟩,⟨101461743621,105044821752⟩,⟨-549540184998,-111219497526⟩,⟨-286449388017,-203288144138⟩,⟨-176496154030,-157435170336⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14297109996,-13393036465⟩,⟨43280635817,61429179300⟩,⟨-105044821752,-101461743621⟩,⟨111219497526,549540184998⟩,⟨203288144138,286449388017⟩,⟨157435170336,176496154030⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115352657307,-114019087044⟩,⟨-832033699109,-813026162164⟩,⟨-105044821752,-101461743621⟩,⟨2310242753078,2748563440550⟩,⟨203288144138,286449388017⟩,⟨157435170336,176496154030⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨88210595634,93217596833⟩,⟨-610128518359,-569045953248⟩,⟨586119914317,607356519665⟩,⟨3234550451277,3915165720295⟩,⟨-3549787526807,-3098293814013⟩,⟨-2485513773052,-2269773508658⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨116613494569,124745198449⟩,⟨-1440203627645,-1318217414244⟩,⟨657878926282,707658080459⟩,⟨19640402038990,22534203643491⟩,⟨-6441290445961,-5152209285845⟩,⟨-4474784067558,-3964321714629⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-124745198449,-116613494569⟩,⟨1318217414244,1440203627645⟩,⟨-707658080459,-657878926282⟩,⟨-22534203643491,-19640402038990⟩,⟨5152209285845,6441290445961⟩,⟨3964321714629,4474784067558⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨974766429327,982898133207⟩,⟨1318217414244,1440203627645⟩,⟨-707658080459,-657878926282⟩,⟨-22534203643491,-19640402038990⟩,⟨5152209285845,6441290445961⟩,⟨3964321714629,4474784067558⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123133931795,125965680159⟩,⟨764779691239,794457994312⟩,⟨180164118415,191830867733⟩,⟨-2800523103562,-2199688537800⟩,⟨-803018974601,-538061673774⟩,⟨-206574946331,-100409973516⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11823751456,12101950732⟩,⟨168621228572,174581688338⟩,⟨21043116024,22041057174⟩,⟨625654945394,780106905764⟩,⟨89946031822,116819324856⟩,⟨-18307791749,-12580494172⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167858516986,179047260064⟩,⟨1466757320296,1889725764884⟩,⟨-5656840297,215712798784⟩,⟨-11221612495054,7221351707591⟩,⟨-5580737268857,6637731736207⟩,⟨-5541986231166,4489099542866⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-179047260064,-167858516986⟩,⟨-1889725764884,-1466757320296⟩,⟨-215712798784,5656840297⟩,⟨-7221351707591,11221612495054⟩,⟨-6637731736207,5580737268857⟩,⟨-4489099542866,5541986231166⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49631029724,66041218256⟩,⟨-383242573965,210936048557⟩,⟨-11854653663,285598524622⟩,⟨-14505066033379,10867449948353⟩,⟨-9882463952507,6208015683005⟩,⟨-6289910729871,7151031544765⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27009596744279,28382384475480⟩,⟨-262002418527563,-217284291091173⟩,⟨-100144908763255,-65604846576718⟩,⟨2396680290604770,4259372326138419⟩,⟨470624107232735,2096049241003533⟩,⟨-502972223497520,1103619999220055⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13789726980,14431273101⟩,⟨171294833014,182034348858⟩,⟨40353036216,43954252270⟩,⟨422220507224,655394990360⟩,⟨66635088908,156702148138⟩,⟨11710209847,44447382581⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338745817265,372523519785⟩,⟨769046809357,1973856183978⟩,⟨-323142824015,311823500308⟩,⟨-46323572686289,5120896420515⟩,⟨-19514453768449,13360829634454⟩,⟨-14320749542481,10817034135565⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372523519785,-338745817265⟩,⟨-1973856183978,-769046809357⟩,⟨-311823500308,323142824015⟩,⟨-5120896420515,46323572686289⟩,⟨-13360829634454,19514453768449⟩,⟨-10817034135565,14320749542481⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57549501463,107997170392⟩,⟨-1305880248626,260567710373⟩,⟨-540996771283,381682722250⟩,⟨-29369988707680,33562369888893⟩,⟨-24040738956996,19586977374927⟩,⟨-17970116764761,18726179820721⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239517979671,241966111036⟩,⟨1549277928484,1557557870466⟩,⟨305518361311,307554091929⟩,⟨-3911333099605,-3897716375552⟩,⟨-1544894032124,-1537024511176⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1706632070252,-1618697325517⟩,⟨-5625233518825,-2705320699899⟩,⟨-489684058010,1461038798060⟩,⟨-19149359044453,104067149102891⟩,⟨-57134643495967,40628138341227⟩,⟨-44106880081874,47569852790535⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-195520505723,-181277360822⟩,⟨-1877591655842,-1428874034320⟩,⟨-353855372277,-97852926679⟩,⟨-7084559512206,12505918768359⟩,⟨-7088758209649,6513383822508⟩,⟨-5076156257153,6280298267475⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43997473948,60688750214⟩,⟨-328313727358,128683836146⟩,⟨-48337010966,209701165250⟩,⟨-10995892611811,8608202392807⟩,⟨-8633652241773,4976359311332⟩,⟨-5424572392814,5932565635597⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2597736072,6486756958⟩,⟨-116079751095,36369515701⟩,⟨-33658902704,50977746007⟩,⟨-3689865808559,3993674412749⟩,⟨-2886911145763,2042494747083⟩,⟨-1978220756064,2025451017797⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1760579574,3349782131⟩,⟨-36243272538,14205690948⟩,⟨-5336028672,23149371624⟩,⟨-1290710588355,1146347037105⟩,⟨-1078321175612,598436922902⟩,⟨-617268317892,734898226610⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3046392395,5844580099⟩,⟨-86924847520,12858736646⟩,⟨-19995800467,34993961186⟩,⟨-2401688819101,2640118628409⟩,⟨-2053576844131,1281588084492⟩,⟨-1214086756714,1342002835603⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5844580099,-3046392395⟩,⟨-12858736646,86924847520⟩,⟨-34993961186,19995800467⟩,⟨-2640118628409,2401688819101⟩,⟨-1281588084492,2053576844131⟩,⟨-1342002835603,1214086756714⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3246844027,3440364563⟩,⟨-128938487741,123294363221⟩,⟨-68652863890,70973546474⟩,⟨-6329984436968,6395363231850⟩,⟨-4168499230255,4096071591214⟩,⟨-3320223591667,3239537774511⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49631029724,66041218256⟩,⟨-383242573965,210936048557⟩,⟨-11854653663,285598524622⟩,⟨-14505066033379,10867449948353⟩,⟨-9882463952507,6208015683005⟩,⟨-6289910729871,7151031544765⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3246844027,3440364563⟩,⟨-128938487741,123294363221⟩,⟨-68652863890,70973546474⟩,⟨-6329984436968,6395363231850⟩,⟨-4168499230255,4096071591214⟩,⟨-3320223591667,3239537774511⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (523/5120) u, BivariateJet2.affineZ (611/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000051

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000052Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2080914179328,-2080914140608⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2080914179328,-2080914140608⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-179574634368,-179574634304⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-179574634304,-179574634240⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨94320720448,94320720512⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-103177673344,-103177673280⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨94320842880,94320842944⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-103177819840,-103177819776⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8856976960,-8856976896⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8856952832,-8856952768⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨197498393792,197498393856⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨197498662720,197498662784⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1901339506304,1901339544896⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1901339506304,1901339544896⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2087640532864,-2087640494144⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2074223744704,-2074223705984⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-180765888064,-180765888000⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-178385557824,-178385557760⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨91751514496,91751514560⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-100110803136,-100110803072⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨96911471424,96911471488⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-106286244480,-106286244416⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9374772992,-9374772928⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8359288640,-8359288576⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨191862317568,191862317632⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨203197715840,203197715904⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1893457817984,1893457856576⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1909254936320,1909254974912⟩



end LaneCBRB2Cell000052Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000052
open Set LaneCBRB2Cell000052Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111883898060,111883898061⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨135076721459,135076721460⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111883898061,-111883898060⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437871915827,437871915828⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨53793249034,53793249035⟩,⟨-135076721460,-135076721459⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨165677147094,165677147096⟩,⟨964434906316,964434906317⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨53793249033,53793249036⟩,⟨-135076721460,-135076721459⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2080914179328,-2080914140608⟩,⟨6400444553242,6400444553328⟩,⟨2905924391909,2905924391952⟩,⟨-37258078446230,-37258078445242⟩,⟨-24212758420178,-24212758419618⟩,⟨-7680133941669,-7680133941445⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313557324792,-313557318953⟩,⟨-860835714666,-860835680675⟩,⟨-390835898956,-390835883521⟩,⟨5614139939027,5614139939408⟩,⟨3530329552601,3530329591532⟩,⟨1157261686508,1157261686597⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨313557318953,313557324792⟩,⟨860835680675,860835714666⟩,⟨390835883521,390835898956⟩,⟨-5614139939408,-5614139939027⟩,⟨-3530329591532,-3530329552601⟩,⟨-1157261686597,-1157261686508⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-165677147096,-165677147094⟩,⟨-964434906317,-964434906316⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨933834480680,933834480682⟩,⟨-964434906317,-964434906316⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-179574634368,-179574634240⟩,⟨-1135541057509,-1135541057503⟩,⟨-515557385051,-515557385047⟩,⟨-1172751120329,-1172751120316⟩,⟨762131079953,762131079964⟩,⟨-241743161751,-241743161748⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152515881772,-152515881662⟩,⟨-806921296483,-806921296361⟩,⟨-366357720671,-366357720613⟩,⟨996038064295,996038064322⟩,⟨1372157348135,1372157348284⟩,⟨205316700799,205316700808⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨152515881662,152515881772⟩,⟨806921296361,806921296483⟩,⟨366357720613,366357720671⟩,⟨-996038064322,-996038064295⟩,⟨-1372157348284,-1372157348135⟩,⟨-205316700808,-205316700799⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨466073200615,466073206564⟩,⟨1667756977036,1667757011149⟩,⟨757193604134,757193619627⟩,⟨-6610178003730,-6610178003322⟩,⟨-4902486939816,-4902486900736⟩,⟨-1362578387405,-1362578387307⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨827733585974,827733597871⟩,⟨4062321913280,4062322005337⟩,⟨757193604134,757193619627⟩,⟨-18639429800455,-18639429799542⟩,⟨-4902486939816,-4902486900736⟩,⟨-1362578387405,-1362578387307⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨107586498066,107586498072⟩,⟨-270153442920,-270153442918⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11236780091174,11236780091802⟩,⟨28215946083786,28215946087150⟩,⟨-91466318078637,-91466318068203⟩,⟨141702446242315,141702446268174⟩,⟨-229675109682705,-229675109575559⟩,⟨1489054208246881,1489054208503358⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8459265045229,8459265167287⟩,⟨62757593907613,62757595158575⟩,⟨-61119250432191,-61119249275877⟩,⟨124681912371057,124681918693399⟩,⟨-541511940622055,-541511929557554⟩,⟨981084450254381,981084469153235⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨98484541440,98484674816⟩,⟨-722207901284,-722205901097⟩,⟨703352052704,703353999961⟩,⟨9095880402387,9095929212350⟩,⟨-4024190803177,-4024129928949⟩,⟨-1302162076895,-1302088352125⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1197996169216,1197996302592⟩,⟨-722207901284,-722205901097⟩,⟨703352052704,703353999961⟩,⟨9095880402387,9095929212350⟩,⟨-4024190803177,-4024129928949⟩,⟨-1302162076895,-1302088352125⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨94320720448,94320842944⟩,⟨-662836831652,-662834922099⟩,⟨645531007645,645532866693⟩,⟨7948538903078,7948586932251⟩,⟨-3304216182861,-3304157659938⟩,⟨-1574112269430,-1574042289430⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨102769137606,102769282516⟩,⟨-784162085958,-784159672911⟩,⟨763688464401,763690813679⟩,⟨10311537820415,10311601236481⟩,⟨-4793420623614,-4793345996667⟩,⟨-1000926735981,-1000839162397⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-98484674816,-98484541440⟩,⟨722205901097,722207901284⟩,⟨-703353999961,-703352052704⟩,⟨-9095929212350,-9095880402387⟩,⟨4024129928949,4024190803177⟩,⟨1302088352125,1302162076895⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1001026952960,1001027086336⟩,⟨722205901097,722207901284⟩,⟨-703353999961,-703352052704⟩,⟨-9095929212350,-9095880402387⟩,⟨4024129928949,4024190803177⟩,⟨1302088352125,1302162076895⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-103177819840,-103177673280⟩,⟨793259040383,793261343050⟩,⟨-772552526297,-772550284527⟩,⟨-10563131704778,-10563073438950⟩,⟨4977405797455,4977476484927⟩,⟨887371894053,887456212972⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-93936061939,-93935915990⟩,⟨654434046169,654436522776⟩,⟨-637351855536,-637349444364⟩,⟨-7721333946885,-7721267914773⟩,⟨3139050975806,3139127940095⟩,⟨1674087430684,1674177001085⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8833075667,8833366526⟩,⟨-129728039789,-129723150135⟩,⟨126336608865,126341369315⟩,⟨2590203873530,2590333321708⟩,⟨-1654369647808,-1654218056572⟩,⟨673160694703,673337838688⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4416537833,4416683263⟩,⟨-64864019895,-64861575067⟩,⟨63168304432,63170684658⟩,⟨1295101936765,1295166660854⟩,⟨-827184823904,-827109028286⟩,⟨336580347351,336668919344⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4416683263,-4416537833⟩,⟨64861575067,64864019895⟩,⟨-63170684658,-63168304432⟩,⟨-1295166660854,-1295101936765⟩,⟨827109028286,827184823904⟩,⟨-336668919344,-336580347351⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757706700353,757706865047⟩,⟨64861575067,64864019895⟩,⟨-63170684658,-63168304432⟩,⟨-1295166660854,-1295101936765⟩,⟨827109028286,827184823904⟩,⟨-336668919344,-336580347351⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8821375470,8821399364⟩,⟨-129378186662,-129377653128⟩,⟨126000130660,126000650138⟩,⟨2578208248453,2578224454384⟩,⟨-1644891997460,-1644874998890⟩,⟨666588860152,666607365908⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8821399364,-8821375470⟩,⟨129377653128,129378186662⟩,⟨-126000650138,-126000130660⟩,⟨-2578224454384,-2578208248453⟩,⟨1644874998890,1644891997460⟩,⟨-666607365908,-666588860152⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090690228412,1090690252306⟩,⟨129377653128,129378186662⟩,⟨-126000650138,-126000130660⟩,⟨-2578224454384,-2578208248453⟩,⟨1644874998890,1644891997460⟩,⟨-666607365908,-666588860152⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8856976960,-8856952768⟩,⟨130424044487,130424585194⟩,⟨-127019731474,-127019205011⟩,⟨-2614547915309,-2614531393087⟩,⟨1673245571145,1673262868441⟩,⟨-686672621809,-686653830018⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4428488480,-4428476384⟩,⟨65212022243,65212292597⟩,⟨-63509865737,-63509602505⟩,⟨-1307273957655,-1307265696543⟩,⟨836622785572,836631434221⟩,⟨-343336310905,-343326915009⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4428476384,4428488480⟩,⟨-65212292597,-65212022243⟩,⟨63509602505,63509865737⟩,⟨1307265696543,1307273957655⟩,⟨-836631434221,-836622785572⟩,⟨343326915009,343336310905⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766551860000,766551891360⟩,⟨-65212292597,-65212022243⟩,⟨63509602505,63509865737⟩,⟨1307265696543,1307273957655⟩,⟨-836631434221,-836622785572⟩,⟨343326915009,343336310905⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272672557103,272672563077⟩,⟨32344413282,32344546666⟩,⟨-31500162535,-31500032665⟩,⟨-644556113596,-644552062113⟩,⟨411218749722,411222999365⟩,⟨-166651841477,-166647215038⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533103720000,1533103782720⟩,⟨-130424585194,-130424044486⟩,⟨127019205010,127019731474⟩,⟨2614531393086,2614547915310⟩,⟨-1673262868442,-1673245571144⟩,⟨686653830018,686672621810⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1207685422419,1207685583331⟩,⟨-871305281012,-871302635707⟩,⟨848556480112,848559055499⟩,⟨12230919765752,12230989043120⟩,⟨-6079386083218,-6079304077659⟩,⟨-378545893403,-378449450480⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1315859217062,1315859538886⟩,⟨-1742610562024,-1742605271414⟩,⟨1697112960224,1697118110997⟩,⟨24461839531509,24461978086230⟩,⟨-12158772166432,-12158608155319⟩,⟨-757091642155,-756899045611⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨197498393792,197498662784⟩,⟨-1456098457030,-1456093680153⟩,⟨1418081017214,1418085667947⟩,⟨18511598776821,18511732202238⟩,⟨-8281703987531,-8281552137665⟩,⟨-2461577873884,-2461404792035⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨67868674641,67868781307⟩,⟨-491885677837,-491883964412⟩,⟨479042881765,479044549897⟩,⟨6067025282132,6067069683271⟩,⟨-2616123765863,-2616070966199⟩,⟨-1008335476928,-1008273232580⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380200901087,380200924972⟩,⟨12754875924,12755198556⟩,⟨-12422212338,-12421898205⟩,⟨-258021376355,-258011515321⟩,⟨165896238481,165906547945⟩,⟨-69362792842,-69351608299⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179702468382,3179702668138⟩,⟨-106674494367,-106671782722⟩,⟨103887018126,103889658343⟩,⟨2164963230701,2165046335221⟩,⟨-1394483174782,-1394396426270⟩,⟨586790860750,586884817009⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨196270950511,196271271312⟩,⟨-1429079993766,-1429074771578⟩,⟨1391767462192,1391772546383⟩,⟨17774444794845,17774582400182⟩,⟨-7744657761828,-7744496417747⟩,⟨-2789283476227,-2789094814852⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨393769344303,393769934096⟩,⟨-2885178450796,-2885168451731⟩,⟨2809848479406,2809858214330⟩,⟨36286043571666,36286314602420⟩,⟨-16026361749359,-16026048555412⟩,⟨-5250861350111,-5250499606887⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522158592284,522158819276⟩,⟨89396144218,89399533262⟩,⟨-87065675754,-87062376256⟩,⟨-1777424852461,-1777334680899⟩,⟨1132518351564,1132623627228⟩,⟨-456759365535,-456636642400⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359835270519,359835505161⟩,⟨92408378067,92411901394⟩,⟨-89999403229,-89995972990⟩,⟨-1829405807962,-1829311599469⟩,⟨1162974485559,1163084146478⟩,⟨-464647370770,-464519841662⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨719670541038,719671010322⟩,⟨184816756134,184823802788⟩,⟨-179998806458,-179991945980⟩,⟨-3658811615924,-3658623198938⟩,⟨2325948971118,2326168292956⟩,⟨-929294741540,-929039683324⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524282320636,1524282407250⟩,⟨-1046932066,-1045857824⟩,⟨1018554872,1019600814⟩,⟨36306938702,36339666857⟩,⟨-28387869552,-28353573684⟩,⟨20046464110,20083761658⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨997698482375,997699189649⟩,⟨255531146898,255541634002⟩,⟨-248870483188,-248860273100⟩,⟨-5048896254547,-5048612946982⟩,⟨3206286656318,3206613716036⟩,⟨-1275518870779,-1275140427207⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67621225204,67621228168⟩,⟨16042456768,16042523278⟩,⟨-15623718458,-15623653698⟩,⟨-317789465901,-317787433711⟩,⟨202106474786,202108602314⟩,⟨-80852501378,-80850190022⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50906564161,50906567125⟩,⟨261914524541,261914591400⟩,⟨34806437303,34806489220⟩,⟨-1267041539988,-1267039462222⟩,⟨-196035398825,-196033492768⟩,⟨-166186433269,-166184599042⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137682728314,2137682903222⟩,⟨-363714980124,-363713457370⟩,⟨354218383494,354219866136⟩,⟨7322083977080,7322130607442⟩,⟨-4696361663960,-4696312986268⟩,⟨1944218492268,1944271218547⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2980677293597,2980677659421⟩,⟨-760718847041,-760715631042⟩,⟨740856450775,740859582068⟩,⟨15379034034900,15379132729210⟩,⟨-9885582782519,-9885480044983⟩,⟨4127761449754,4127872405754⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨138003124347,138003149321⟩,⟨674806043308,674806462651⟩,⟨128658224443,128658523742⟩,⟨-3085220087957,-3085207798141⟩,⟨-836731764607,-836720820227⟩,⟨-212498788327,-212488344084⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8760132109758,8760133695053⟩,⟨-42835224630461,-42835182507979⟩,⟨-8166959076624,-8166937121891⟩,⟨614751970229362,614753569312963⟩,⟨132982341814700,132983334557960⟩,⟨28716107160872,28716854136843⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7948956873688,7948963947248⟩,⟨-36832882230792,-36832732532235⟩,⟨-9393540638598,-9393433757748⟩,⟨497689811657227,497694759290498⟩,⟨154010879170758,154014966236006⟩,⟨19591564615093,19595439520275⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15897913747376,15897927894496⟩,⟨-73665764461584,-73665465064470⟩,⟨-18787081277196,-18786867515496⟩,⟨995379623314454,995389518580996⟩,⟨308021758341516,308029932472012⟩,⟨39183129230186,39190879040550⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10805181447606,10805181447704⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230896,2087019636287702⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9705669819830,9705669819928⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230908,2087019636287687⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2394564936256,2394564994112⟩,⟨-12029251796733,-12029251796224⟩,⟨0,0⟩,⟨104822536628670,104822536664337⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7296877335255,7296877335344⟩,⟨-42476366431676,-42476366430594⟩,⟨-19285083757366,-19285083756850⟩,⟨494524334794265,494524334813395⟩,⟨272949034685082,272949034695231⟩,⟨101937976594953,101937976599152⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6197365707479,6197365707568⟩,⟨-42476366431677,-42476366430594⟩,⟨-19285083757366,-19285083756849⟩,⟨494524334794271,494524334813395⟩,⟨272949034685084,272949034695232⟩,⟨101937976594954,101937976599153⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1901339506304,1901339544896⟩,⟨-7535985610959,-7535985610612⟩,⟨-3421481777059,-3421481776896⟩,⟨36085327319314,36085327331659⟩,⟨24974889496847,24974889502919⟩,⟨7438390778516,7438390781148⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100498837339,100498837341⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨140712502449,140712502452⟩,⟨673788004906,673788004913⟩,⟨305912656869,305912656874⟩,⟨-1691905142294,-1691905142289⟩,⟨-1536314667176,-1536314667168⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4295904442560,4295904539008⟩,⟨-19565237407692,-19565237406836⟩,⟨-3421481777059,-3421481776896⟩,⟨140907863947984,140907863995996⟩,⟨24974889496847,24974889502919⟩,⟨7438390778516,7438390781148⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨787538688606,787539868192⟩,⟨-5770356901592,-5770336903462⟩,⟨5619696958812,5619716428660⟩,⟨72572087143332,72572629204840⟩,⟨-32052723498718,-32052097110824⟩,⟨-10501722700222,-10500999213774⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5083443131166,5083444407200⟩,⟨-25335594309284,-25335574310298⟩,⟨2198215181753,2198234651764⟩,⟨213479951091316,213480493200836⟩,⟨-7077834001871,-7077207607905⟩,⟨-3063331921706,-3062608432626⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨464642766347,464642882991⟩,⟨1733129642393,1733132486763⟩,⟨200923814179,200925593804⟩,⟨-31012956665349,-31012872704516⟩,⟨1103907650747,1103980412713⟩,⟨-279998218067,-279932088873⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨39517532849,39517535107⟩,⟨-802289281406,-802289270020⟩,⟨321668947845,321668966201⟩,⟨9969619318865,9969619349288⟩,⟨-6530558220472,-6530558128119⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨504160299196,504160418098⟩,⟨930840360987,930843216743⟩,⟨522592762024,522594560005⟩,⟨-21043337346484,-21043253355228⟩,⟨-5426650569725,-5426577715406⟩,⟨-279998218067,-279932088873⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504862395711,504862407910⟩,⟨2536208829314,2536208952001⟩,⟨0,0⟩,⟨3381169318170,3381172243620⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨231495120237,231495180428⟩,⟨1590344342623,1590345994752⟩,⟨239958748185,239959579563⟩,⟨-3817810960476,-3817757071412⟩,⟨-1286305174597,-1286267456234⟩,⟨-128566693624,-128536325996⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-787539868192,-787538688606⟩,⟨5770336903462,5770356901592⟩,⟨-5619716428660,-5619696958812⟩,⟨-72572629204840,-72572087143332⟩,⟨32052097110824,32052723498718⟩,⟨10500999213774,10501722700222⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3508364574368,3508365850402⟩,⟨-13794900504230,-13794880505244⟩,⟨-9041198205719,-9041178735708⟩,⟨68335234743144,68335776852664⟩,⟨57026986607671,57027613001637⟩,⟨17939389992290,17940113481370⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨448990939514,448991102828⟩,⟨384515256900,384518598340⟩,⟨-180949879434,-180947032647⟩,⟨-13560454421745,-13560358569109⟩,⟨-6982581441406,-6982481998356⟩,⟨-3847988970211,-3847885141035⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨331354294188,331354294192⟩,⟨1928869812632,1928869812634⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-331354294192,-331354294188⟩,⟨-1928869812634,-1928869812632⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨768157333584,768157333588⟩,⟨-1928869812634,-1928869812632⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1328342373563,1328342400532⟩,⟨-8600417517837,-8600417449860⟩,⟨-3904754246026,-3904754215156⟩,⟨51651185568141,51651185578144⟩,⟨33255601139323,33255601221425⟩,⟨10647033876963,10647033879103⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1328342400532,-1328342373563⟩,⟨8600417449860,8600417517837⟩,⟨3904754215156,3904754246026⟩,⟨-51651185578144,-51651185568141⟩,⟨-33255601221425,-33255601139323⟩,⟨-10647033879103,-10647033876963⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-228830772756,-228830745787⟩,⟨8600417449860,8600417517837⟩,⟨3904754215156,3904754246026⟩,⟨-51651185578144,-51651185568141⟩,⟨-33255601221425,-33255601139323⟩,⟨-10647033879103,-10647033876963⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11195471185,-11195469864⟩,⟨448884843151,448884849816⟩,⟨99908763369,99908775632⟩,⟨-4640166927678,-4640166910329⟩,⟨1547155162788,1547155224743⟩,⟨2589173048448,2589173073179⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437795468329,437795632964⟩,⟨833400100051,833403448156⟩,⟨-81041116065,-81038257015⟩,⟨-18200621349423,-18200525479438⟩,⟨-5435426278618,-5435326773613⟩,⟨-1258815921763,-1258712067856⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100498837341,-100498837339⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4916872953,4916872954⟩,⟨30499043138,30499043142⟩,⟨40022876823,40022876824⟩,⟨-322759494211,-322759494202⟩,⟨248259301866,248259301870⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10708182862,10708183124⟩,⟨12628912801,12628914429⟩,⟨87163587057,87163589166⟩,⟨-901519188274,-901519170898⟩,⟨102798145600,102798158703⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1460525249577,1460525270571⟩,⟨-7167914950574,-7167914582070⟩,⟨-1336058406861,-1336058341112⟩,⟨103245912740774,103245919910699⟩,⟨21764495368569,21764496817256⟩,⟨4848649143624,4848649418360⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14224107369,14224107922⟩,⟨-53033090707,-53033083004⟩,⟨102770956487,102770961912⟩,⟨-356668726534,-356668562114⟩,⟨-235064978969,-235064894607⟩,⟨-164610419681,-164610400298⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14224107922,-14224107369⟩,⟨53033083004,53033090707⟩,⟨-102770961912,-102770956487⟩,⟨356668562114,356668726534⟩,⟨235064894607,235064978969⟩,⟨164610400298,164610419681⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114722945263,-114722944708⟩,⟨-822710748652,-822710740947⟩,⟨-102770961912,-102770956487⟩,⟨2555691817666,2555691982086⟩,⟨235064894607,235064978969⟩,⟨164610400298,164610419681⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨93022417385,93022419279⟩,⟨-602278180676,-602278175895⟩,⟨589798720245,589798735635⟩,⟨3617078125363,3617078126167⟩,⟨-3260264205762,-3260264166634⟩,⟨-2361235923518,-2361235923231⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨123565395704,123565399997⟩,⟨-1406460153412,-1406460092035⟩,⟨670418137616,670418177187⟩,⟨21392384368456,21392385689089⟩,⟨-5602542554079,-5602541939965⟩,⟨-4159685695314,-4159685510308⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-123565399997,-123565395704⟩,⟨1406460092035,1406460153412⟩,⟨-670418177187,-670418137616⟩,⟨-21392385689089,-21392384368456⟩,⟨5602541939965,5602542554079⟩,⟨4159685510308,4159685695314⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨975946227779,975946232072⟩,⟨1406460092035,1406460153412⟩,⟨-670418177187,-670418137616⟩,⟨-21392385689089,-21392384368456⟩,⟨5602541939965,5602542554079⟩,⟨4159685510308,4159685695314⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124898939217,124898939770⟩,⟨778061240321,778061250819⟩,⟨185735265494,185735271761⟩,⟨-2515728459541,-2515728208615⟩,⟨-666185402943,-666185276990⟩,⟨-150274214239,-150274167159⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11970181769,11970181886⟩,⟨171683129964,171683132404⟩,⟨21446224778,21446226016⟩,⟨697867020605,697867080562⟩,⟨104743636334,104743663740⟩,⟨-15138944345,-15138938104⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨173077676030,173077831740⟩,⟨1680392408770,1680397920373⟩,⟨105560913409,105563536437⟩,⟨-2078044114070,-2077832608386⟩,⟨497497363081,497627472342⟩,⟨-525208314627,-525115273412⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-173077831740,-173077676030⟩,⟨-1680397920373,-1680392408770⟩,⟨-105563536437,-105560913409⟩,⟨2077832608386,2078044114070⟩,⟨-497627472342,-497497363081⟩,⟨525115273412,525208314627⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58417288497,58417504398⟩,⟨-90053577750,-90046414018⟩,⟨134395211748,134398666154⟩,⟨-1739978352090,-1739712957342⟩,⟨-1783932646939,-1783764819315⟩,⟨396548579788,396671988631⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27491597825882,27491622847911⟩,⟨-236350558164113,-236349940875070⟩,⟨-81959197950277,-81958783616048⟩,⟨3252825801879064,3252847516911629⟩,⟨1251760465108393,1251777329331518⟩,⟨292232631455179,292247460381000⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14187885442,14187885569⟩,⟨176767614106,176767617274⟩,⟨42197166540,42197168152⟩,⟨529630554125,529630643382⟩,⟨111517802948,111517844654⟩,⟨28609972676,28609987762⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354746262538,354746588594⟩,⟨1369980493327,1369992587991⟩,⟨-2510378124,-2504021563⟩,⟨-20779352767892,-20778858056707⟩,⟨-3306394966945,-3306082743800⟩,⟨-1804614980670,-1804390525986⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354746588594,-354746262538⟩,⟨-1369992587991,-1369980493327⟩,⟨2504021563,2510378124⟩,⟨20778858056707,20779352767892⟩,⟨3306082743800,3306394966945⟩,⟨1804390525986,1804614980670⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83048879735,83049370426⟩,⟨-536592487940,-536577045171⟩,⟨-78537094502,-78527878891⟩,⟨2578236707284,2578827288454⟩,⟨-2129343534818,-2128931806668⟩,⟨545574604223,545902912814⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨241211339788,241211339793⟩,⟨1549531836560,1549531836569⟩,⟨305912656869,305912656874⟩,⟨-3890928397846,-3890928397841⟩,⟨-1536314667176,-1536314667168⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1658788379824,-1658786895689⟩,⟨-4209393486796,-4209351513538⟩,⟨474246390777,474270104906⟩,⟨43334593572023,43336110887318⟩,⟨-7798218270522,-7797172555596⟩,⟨1802943700389,1803794878800⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-188429939902,-188429770476⟩,⟨-1651995030649,-1651989194506⟩,⟨-226339251991,-226336297783⟩,⟨2760470880328,2760706520276⟩,⟨-256268226354,-256124445285⟩,⟨591741930739,591846912302⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52781399886,52781569317⟩,⟨-102463194089,-102457357937⟩,⟨79573404878,79576359091⟩,⟨-1130457517518,-1130221877565⟩,⟨-1792582893530,-1792439112453⟩,⟨242983791530,243088773095⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4412404784,4412447163⟩,⟨-35311392787,-35309885658⟩,⟨5978500406,5979326356⟩,⟨93444367275,93506595444⟩,⟨-307037752715,-306997146938⟩,⟨39738863845,39768658926⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2533739619,2533755887⟩,⟨-9837400616,-9836808712⟩,⟨7639747678,7640055836⟩,⟨-89439366321,-89414218993⟩,⟨-186935696874,-186919944810⟩,⟨34846291655,34857300950⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4381490031,4381518252⟩,⟨-34377614354,-34376478951⟩,⟨5326505272,5327089051⟩,⟨63333861591,63385998645⟩,⟨-287461493754,-287429924270⟩,⟨29850482633,29871549703⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4381518252,-4381490031⟩,⟨34376478951,34377614354⟩,⟨-5327089051,-5326505272⟩,⟨-63385998645,-63333861591⟩,⟨287429924270,287461493754⟩,⟨-29871549703,-29850482633⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨30886532,30957132⟩,⟨-934913836,-932271304⟩,⟨651411355,652821084⟩,⟨30058368630,30172733853⟩,⟨-19607828445,-19535653184⟩,⟨9867314142,9918176293⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58417288497,58417504398⟩,⟨-90053577750,-90046414018⟩,⟨134395211748,134398666154⟩,⟨-1739978352090,-1739712957342⟩,⟨-1783932646939,-1783764819315⟩,⟨396548579788,396671988631⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨30886532,30957132⟩,⟨-934913836,-932271304⟩,⟨651411355,652821084⟩,⟨30058368630,30172733853⟩,⟨-19607828445,-19535653184⟩,⟨9867314142,9918176293⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111669149696,112098646426⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨133143986176,137009456743⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112098646426,-111669149696⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437657167462,438086664192⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨52997547622,54589705422⟩,⟨-137009456743,-133143986176⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨164666697318,166688351848⟩,⟨962502171033,966367641600⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52568050892,55019202152⟩,⟨-137009456743,-133143986176⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2087640532864,-2074223705984⟩,⟨6348867914750,6452625065977⟩,⟨2886879252623,2925190029910⟩,⟨-37868058136219,-36660025033548⟩,⟨-24508506430153,-23922207662180⟩,⟨-7782306703195,-7579794163781⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-316490840919,-310642978695⟩,⟨-884011703441,-837524005762⟩,⟨-399445166285,-382173099674⟩,⟨5374599008687,5852171751399⟩,⟨3412974944292,3646902853768⟩,⟨1118411924002,1195834386965⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨310642978695,316490840919⟩,⟨837524005762,884011703441⟩,⟨382173099674,399445166285⟩,⟨-5852171751399,-5374599008687⟩,⟨-3646902853768,-3412974944292⟩,⟨-1195834386965,-1118411924002⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-166688351848,-164666697318⟩,⟨-966367641600,-962502171033⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨932823275928,934844930458⟩,⟨-966367641600,-962502171033⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-180765888064,-178385557760⟩,⟨-1139050113849,-1132040506751⟩,⟨-516369384945,-514747557509⟩,⟨-1180010405606,-1165531747507⟩,⟨758245214647,766009624086⟩,⟨-242505249579,-240984307276⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-153693758018,-151341919597⟩,⟨-812304950019,-801544437362⟩,⟨-368030290552,-364686800793⟩,⟨978667362979,1013401926196⟩,⟨1363738076656,1380584352067⟩,⟨203600496002,207031290960⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151341919597,153693758018⟩,⟨801544437362,812304950019⟩,⟨364686800793,368030290552⟩,⟨-1013401926196,-978667362979⟩,⟨-1380584352067,-1363738076656⟩,⟨-207031290960,-203600496002⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨461984898292,470184598937⟩,⟨1639068443124,1696316653460⟩,⟨746859900467,767475456837⟩,⟨-6865573677595,-6353266371666⟩,⟨-5027487205835,-4776713020948⟩,⟨-1402865677925,-1322012420004⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨822702694442,832788956147⟩,⟨4026578973404,4097924057494⟩,⟨746859900467,767475456837⟩,⟨-18999733926562,-18277370525811⟩,⟨-5027487205835,-4776713020948⟩,⟨-1402865677925,-1322012420004⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨105136101784,110038404304⟩,⟨-274018913486,-266287972352⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10986399041872,11498674566596⟩,⟨26586589862095,29969289880477⟩,⟨-95826569523362,-87392693772422⟩,⟨128676695212203,156219454814249⟩,⟨-279956708130923,-182466849765331⟩,⟨1390352361259049,1597180853050975⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8220504327221,8709293242091⟩,⟨60127115367319,65555276498143⟩,⟨-65118008851283,-57364790450353⟩,⟨92310905543832,159087993457743⟩,⟨-603711524251658,-483385277253537⟩,⟨891874567511312,1077796898481206⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨95688476672,101310677248⟩,⟨-798578700318,-652982600111⟩,⟨622983653785,793252010419⟩,⟨6908934465350,11529087720886⟩,⟨-7198417853106,-1086197528488⟩,⟨-5076764135971,2679178905873⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1195200104448,1200822305024⟩,⟨-798578700318,-652982600111⟩,⟨622983653785,793252010419⟩,⟨6908934465350,11529087720886⟩,⟨-7198417853106,-1086197528488⟩,⟨-5076764135971,2679178905873⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨91751514496,96911471488⟩,⟨-734643984240,-597891926684⟩,⟨570423923993,729743752505⟩,⟨5835187289865,10280940265885⟩,⟨-6311923105973,-506975686554⟩,⟨-5154644711644,2168747620710⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨99736480214,105841042183⟩,⟨-872722302551,-704415138644⟩,⟨672053308586,866901059046⟩,⟨7629703494613,13311569382588⟩,⟨-8588015548104,-1319268863798⟩,⟨-5430665138448,3657683086745⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-101310677248,-95688476672⟩,⟨652982600111,798578700318⟩,⟨-793252010419,-622983653785⟩,⟨-11529087720886,-6908934465350⟩,⟨1086197528488,7198417853106⟩,⟨-2679178905873,5076764135971⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨998200950528,1003823151104⟩,⟨652982600111,798578700318⟩,⟨-793252010419,-622983653785⟩,⟨-11529087720886,-6908934465350⟩,⟨1086197528488,7198417853106⟩,⟨-2679178905873,5076764135971⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-106286244480,-100110803072⟩,⟨715227538603,879629062896⟩,⟨-873761749828,-682368971563⟩,⟨-13402931577552,-8032774407674⟩,⟨1633616315897,8628033913503⟩,⟨-3645459987445,5168535856900⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-97036347919,-90886441089⟩,⟨572129354530,743622336114⟩,⟨-740997055933,-542813339881⟩,⟨-10757914203037,-4900387962483⟩,⟨-481987158865,6967757102250⟩,⟨-3045695753533,6238480949852⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2700132295,14954601094⟩,⟨-300592948021,39207197470⟩,⟨-68943747347,324087719165⟩,⟨-3128210708424,8411181420105⟩,⟨-9070002706969,5648488238452⟩,⟨-8476360891981,9896164036597⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1350066147,7477300547⟩,⟨-150296474011,19603598735⟩,⟨-34471873674,162043859583⟩,⟨-1564105354212,4205590710053⟩,⟨-4535001353485,2824244119226⟩,⟨-4238180445991,4948082018299⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7477300547,-1350066147⟩,⟨-19603598735,150296474011⟩,⟨-162043859583,34471873674⟩,⟨-4205590710053,1564105354212⟩,⟨-2824244119226,4535001353485⟩,⟨-4948082018299,4238180445991⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754646083069,760773336733⟩,⟨-19603598735,150296474011⟩,⟨-162043859583,34471873674⟩,⟨-4205590710053,1564105354212⟩,⟨-2824244119226,4535001353485⟩,⟨-4948082018299,4238180445991⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8327592302,9334920219⟩,⟨-147164517268,-113655751734⟩,⟨108434245380,146182898614⟩,⟨1978135861396,3284635796548⟩,⟨-2478829169046,-929019866706⟩,⟨-229596080245,1638324068076⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9334920219,-8327592302⟩,⟨113655751734,147164517268⟩,⟨-146182898614,-108434245380⟩,⟨-3284635796548,-1978135861396⟩,⟨929019866706,2478829169046⟩,⟨-1638324068076,229596080245⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090176707557,1091184035474⟩,⟨113655751734,147164517268⟩,⟨-146182898614,-108434245380⟩,⟨-3284635796548,-1978135861396⟩,⟨929019866706,2478829169046⟩,⟨-1638324068076,229596080245⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9374772992,-8359288576⟩,⟨114523138657,148424651537⟩,⟨-147434627519,-109261783318⟩,⟨-3332797397271,-2005160929052⟩,⟨947490379610,2519957197199⟩,⟨-1672122300438,220704383490⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4687386496,-4179644288⟩,⟨57261569328,74212325769⟩,⟨-73717313760,-54630891659⟩,⟨-1666398698636,-1002580464526⟩,⟨473745189805,1259978598600⟩,⟨-836061150219,110352191745⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4179644288,4687386496⟩,⟨-74212325769,-57261569328⟩,⟨54630891659,73717313760⟩,⟨1002580464526,1666398698636⟩,⟨-1259978598600,-473745189805⟩,⟨-110352191745,836061150219⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766303027904,766810789376⟩,⟨-74212325769,-57261569328⟩,⟨54630891659,73717313760⟩,⟨1002580464526,1666398698636⟩,⟨-1259978598600,-473745189805⟩,⟨-110352191745,836061150219⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272544176889,272796008869⟩,⟨28413937933,36791129317⟩,⟨-36545724654,-27108561345⟩,⟨-821158949137,-494533965349⟩,⟨232254966676,619707292262⟩,⟨-409581017019,57399020062⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532606055808,1533621578752⟩,⟨-148424651538,-114523138656⟩,⟨109261783318,147434627520⟩,⟨2005160929052,3332797397272⟩,⟨-2519957197200,-947490379610⟩,⟨-220704383490,1672122300438⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1204321516479,1211104656808⟩,⟨-968905491697,-783405916006⟩,⟨747415137658,962442685848⟩,⟨9308093050288,15538380719735⟩,⟨-10273692723412,-2275529521401⟩,⟨-5231866006449,4780285209833⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1309131405182,1322697685840⟩,⟨-1937810983395,-1566811832012⟩,⟨1494830275316,1924885371696⟩,⟨18616186100581,31076761439461⟩,⟨-20547385446820,-4551059042801⟩,⟨-10458988306098,9560570419666⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨191862317568,203197715904⟩,⟨-1627526236284,-1302435050938⟩,⟨1242599338349,1616670289888⟩,⟨13065867146552,24557901497485⟩,⟨-15785381373294,-1390095623506⟩,⟨-11161357974732,6625411656470⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨65675461987,70098814810⟩,⟨-554358335967,-434323850564⟩,⟨412651753309,552042681835⟩,⟨4136092651275,8149793884902⟩,⟨-5280134748249,-101520433345⟩,⟨-4202450842662,2294028102733⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379898534424,380501520157⟩,⟨2780980855,22929321193⟩,⟨-23891197217,-1207051649⟩,⟨-658268227327,131640237253⟩,⟨-295831143777,639385746761⟩,⟨-635851185060,489538075415⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177190511921,3182233438852⟩,⟨-192068265653,-23221210739⟩,⟨10078890210,200125454007⟩,⟨-1102349643727,5537192076386⟩,⟨-5379994919948,2477892655848⟩,⟨-4100568965385,5351400946294⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨189778306495,202881703911⟩,⟨-1616682667742,-1256425712977⟩,⟨1193016188254,1610494326950⟩,⟨11899875949758,24134029909417⟩,⟨-15822228050848,-148076828661⟩,⟨-12416700408484,7181566058316⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨381640624063,406079419815⟩,⟨-3244208904026,-2558860763915⟩,⟨2435615526603,3227164616838⟩,⟨24965743096310,48691931406902⟩,⟨-31607609424142,-1538172452167⟩,⟨-23578058383216,13806977714786⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517948784082,526393769073⟩,⟨-27128217374,207986067896⟩,⟨-224242553946,47703510716⟩,⟨-5825218302905,2205558629479⟩,⟨-3952598932418,6285134282456⟩,⟨-6857507874790,5912721266218⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355492394317,364222018228⟩,⟨-28155806538,215864367693⟩,⟨-232736632830,49510470974⟩,⟨-6051434012423,2331748560972⟩,⟨-4148298208428,6532989913476⟩,⟨-7127808942512,6186261747371⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨710984788634,728444036456⟩,⟨-56311613076,431728735386⟩,⟨-465473265660,99020941948⟩,⟨-12102868024846,4663497121944⟩,⟨-8296596416856,13065979826952⟩,⟨-14255617885024,12372523494742⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523271135589,1525293986450⟩,⟨-34768899804,32641378612⟩,⟨-36921115296,39000382140⟩,⟨-1279474867496,1354661535876⟩,⟨-1590937330494,1531338789436⟩,⟨-1859028451566,1901718380683⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨985003322392,1010531658060⟩,⟨-101153057139,620539741662⟩,⟨-670187127272,163204861634⟩,⟨-17664641855304,7392539987789⟩,⟨-12591764087959,19170308082796⟩,⟨-21040717631674,18454923230263⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67557565085,67682469722⟩,⟨14086350940,18256238472⟩,⟨-18134465476,-13439204008⟩,⟨-406001221752,-242705510268⟩,⟨112695816348,306105748710⟩,⟨-201902717261,30911566823⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50549525281,51263862870⟩,⟨257946112413,266082874738⟩,⟨32154142682,37187569453⟩,⟨-1373903288237,-1168540410131⟩,⟨-283171839792,-98120304011⟩,⟨-264596820920,-76073350805⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136295117724,2139127124623⟩,⟨-414051552830,-319266938884⟩,⟨304599363118,411289740842⟩,⟨5613833003775,9337381713066⟩,⟨-7069581749188,-2664169180152⟩,⟨-593970740287,4704160913492⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2977775542983,2983698794211⟩,⟨-866291515380,-667537884446⟩,⟨636870247732,860513166583⟩,⟨11787539610562,19619800070792⟩,⟨-14874479338377,-5617956268399⟩,⟨-1197330619539,9924916916949⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136901817396,139112604149⟩,⟨658197837310,691368249455⟩,⟨116361942101,141035102485⟩,⟨-3605664211572,-2563176092981⟩,⟨-1341831937125,-335295731236⟩,⟨-736600645351,314922547316⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8690268053064,8830604608541⟩,⟨-44595460936630,-41117163129548⟩,⟨-9097214702182,-7269049948555⟩,⟨549203600054518,683000184401454⟩,⟨89731306294822,178436185579131⟩,⟨-8152990923534,66256843347482⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7785222719344,8115971938188⟩,⟨-41798891956918,-31851233131814⟩,⟨-13743539049208,-5201255359386⟩,⟨299798003952531,695304916825997⟩,⟨-32496822727466,345979370019757⟩,⟨-179180035824927,220203619635912⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15570445438688,16231943876376⟩,⟨-83597783913836,-63702466263628⟩,⟨-27487078098416,-10402510718772⟩,⟨599596007905062,1390609833651994⟩,⟨-64993645454932,691958740039514⟩,⟨-358360071649854,440407239271824⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10784481866270,10825960642718⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533866,2099083303790624⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9684970238494,9726449014942⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533869,2099083303790615⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2392217469760,2396916459264⟩,⟨-12101371604921,-11957606413725⟩,⟨0,0⟩,⟨101381360168522,108260423343400⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7252611272544,7341653408400⟩,⟨-43085435034986,-41878475718850⟩,⟨-19532063882527,-19042466201470⟩,⟨483634559368625,505704807592802⟩,⟨267752125763860,278274496637432⟩,⟨99995851261712,103927956902628⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6153099644768,6242141780624⟩,⟨-43085435034987,-41878475718849⟩,⟨-19532063882528,-19042466201469⟩,⟨483634559368626,505704807592801⟩,⟨267752125763859,278274496637433⟩,⟨99995851261711,103927956902628⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1893457817984,1909254974912⟩,⟨-7699036184017,-7376614089287⟩,⟨-3490229736755,-3354203372147⟩,⟨31278558579236,40875922702807⟩,⟨22723350032609,27222192681574⟩,⟨6534407141489,8338693255114⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100284130918,100713627649⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139702868208,141724522739⟩,⟨670081316286,677493369080⟩,⟨304892499720,306932212697⟩,⟨-1698693120000,-1685130754127⟩,⟨-1540252447540,-1532376886800⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4285675287744,4306171434176⟩,⟨-19800407788938,-19334220503012⟩,⟨-3490229736755,-3354203372147⟩,⟨132659918747758,149136346046207⟩,⟨22723350032609,27222192681574⟩,⟨6534407141489,8338693255114⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨763281248126,812158839630⟩,⟨-6488417808052,-5117721527830⟩,⟨4871231053206,6454329233676⟩,⟨49931486192620,97383862813804⟩,⟨-63215218848284,-3076344904334⟩,⟨-47156116766432,27613955429572⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5048956535870,5118330273806⟩,⟨-26288825596990,-24451942030842⟩,⟨1381001316451,3100125861529⟩,⟨182591404940378,246520208860011⟩,⟨-40491868815675,24145847777240⟩,⟨-40621709624943,35952648684686⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨460504650839,468831430572⟩,⟨1611425468354,1848459502026⟩,⟨125958210280,283966912033⟩,⟨-35480700343574,-26449105524280⟩,⟨-2609588363954,4682136492931⟩,⟨-3720888105484,3293209076788⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38483410361,40558714870⟩,⟨-823428215512,-781340900045⟩,⟨320394994437,322946015318⟩,⟨9609724058633,10337117884547⟩,⟨-6562818552468,-6498504886492⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨498988061200,509390145442⟩,⟨787997252842,1067118601981⟩,⟨446353204717,606912927351⟩,⟨-25870976284941,-16111987639733⟩,⟨-9172406916422,-1816368393561⟩,⟨-3720888105484,3293209076788⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504367106722,505357825907⟩,⟨2516159178967,2556424289217⟩,⟨0,0⟩,⟨2234856254543,4531068346710⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228895409887,234126033719⟩,⟨1503370444791,1674829106540⟩,⟨204750790034,278949480600⟩,⟨-7270028343971,-329472821335⟩,⟨-3194374498442,577902462755⟩,⟨-1710195577681,1513625629107⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-812158839630,-763281248126⟩,⟨5117721527830,6488417808052⟩,⟨-6454329233676,-4871231053206⟩,⟨-97383862813804,-49931486192620⟩,⟨3076344904334,63215218848284⟩,⟨-27613955429572,47156116766432⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3473516448114,3542890186050⟩,⟨-14682686261108,-12845802694960⟩,⟨-9944558970431,-8225434425353⟩,⟨35276055933954,99204859853587⟩,⟨25799694936943,90437411529858⟩,⟨-21079548288083,55494810021546⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441341590493,456670405342⟩,⟨224319383788,550871052390⟩,⟨-318631247184,-56106416497⟩,⟨-19085711897139,-8193667538509⟩,⟨-11911302901534,-1758813737550⟩,⟨-9394101619346,1490661598239⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨329333394636,333376703696⟩,⟨1925004342066,1932735283200⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-333376703696,-329333394636⟩,⟨-1932735283200,-1925004342066⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨766134924080,770178233140⟩,⟨-1932735283200,-1925004342066⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1319353179160,1337381602927⟩,⟨-8749079406449,-8455023086208⟩,⟨-3966249330924,-3844564268114⟩,⟨47624438962592,55699405205980⟩,⟨31365399934965,35157260453799⟩,⟨9893667181161,11403583310745⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1337381602927,-1319353179160⟩,⟨8455023086208,8749079406449⟩,⟨3844564268114,3966249330924⟩,⟨-55699405205980,-47624438962592⟩,⟨-35157260453799,-31365399934965⟩,⟨-11403583310745,-9893667181161⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-237869975151,-219841551384⟩,⟨8455023086208,8749079406449⟩,⟨3844564268114,3966249330924⟩,⟨-55699405205980,-47624438962592⟩,⟨-35157260453799,-31365399934965⟩,⟨-11403583310745,-9893667181161⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11902935739,-10510704543⟩,⟨430859167287,467441900199⟩,⟨89033697966,110962576450⟩,⟨-4967614647951,-4324642654777⟩,⟨1331847407158,1758687416174⟩,⟨2490002007094,2687585108643⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429438654754,446159700799⟩,⟨655178551075,1018312952589⟩,⟨-229597549218,54856159953⟩,⟨-24053326545090,-12518310193286⟩,⟨-10579455494376,-126321376⟩,⟨-6904099612252,4178246706882⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100713627649,-100284130918⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4794620779,5039676980⟩,⟨29299234568,31699645237⟩,⟨39917784923,40128086017⟩,⟨-328397225989,-317126292273⟩,⟨247702508009,248816179610⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10431700128,10986409237⟩,⟨8279254761,16961360638⟩,⟨86849488477,87478538129⟩,⟨-971589464460,-831037071749⟩,⟨97273538155,108293929972⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1451659283773,1469456497204⟩,⟨-7319437716710,-7018849980464⟩,⟨-1370813301225,-1301873782291⟩,⟨99732857275896,106853038006008⟩,⟨20915689226913,22635943064111⟩,⟨4639526282339,5063288649068⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13772727776,14682928336⟩,⟨-62205509589,-43923643395⟩,⟨100968054833,104560194195⟩,⟨-578093419533,-135217461180⟩,⟨-276623120446,-193305024581⟩,⟨-174109427794,-155075015684⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14682928336,-13772727776⟩,⟨43923643395,62205509589⟩,⟨-104560194195,-100968054833⟩,⟨135217461180,578093419533⟩,⟨193305024581,276623120446⟩,⟨155075015684,174109427794⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115396555985,-114056858694⟩,⟨-832249684989,-813108825335⟩,⟨-104560194195,-100968054833⟩,⟨2334240716732,2777116675085⟩,⟨193305024581,276623120446⟩,⟨155075015684,174109427794⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨90526907058,95538494338⟩,⟨-623168321073,-581964510636⟩,⟨579035013182,600353095691⟩,⟨3281962988586,3964161973608⟩,⟨-3484255008783,-3032591042068⟩,⟨-2468864439029,-2252994858284⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨119520541431,127683653080⟩,⟨-1468840125297,-1346242210753⟩,⟨645373905806,695161497961⟩,⟨19974543038951,22879453682313⟩,⟨-6241981517814,-4956380043375⟩,⟨-4414533526964,-3905827665012⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-127683653080,-119520541431⟩,⟨1346242210753,1468840125297⟩,⟨-695161497961,-645373905806⟩,⟨-22879453682313,-19974543038951⟩,⟨4956380043375,6241981517814⟩,⟨3905827665012,4414533526964⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨971827974696,979991086345⟩,⟨1346242210753,1468840125297⟩,⟨-695161497961,-645373905806⟩,⟨-22879453682313,-19974543038951⟩,⟨4956380043375,6241981517814⟩,⟨3905827665012,4414533526964⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123479508574,126318599542⟩,⟨763318591118,793177722239⟩,⟨179881343662,191567093542⟩,⟨-2822253249587,-2217256470713⟩,⟨-798100985565,-533130806937⟩,⟨-202994468539,-96854107171⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11831586575,12111163536⟩,⟨168694238516,174693463792⟩,⟨20947662346,21947719330⟩,⟨619686510551,775623219996⟩,⟨91270814764,118184152250⟩,⟨-18002684075,-12286427481⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167549909037,178795495953⟩,⟨1468086342726,1893489075159⟩,⟨-6126414838,212072284024⟩,⟨-11336856728402,7220749112505⟩,⟨-5459346546527,6557022615133⟩,⟨-5310478937342,4280739071288⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178795495953,-167549909037⟩,⟨-1893489075159,-1468086342726⟩,⟨-212072284024,6126414838⟩,⟨-7220749112505,11336856728402⟩,⟨-6557022615133,5459346546527⟩,⟨-4280739071288,5310478937342⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50099913934,66576124682⟩,⟨-390118630368,206742763814⟩,⟨-7321493990,285075895438⟩,⟨-14490777456476,11007383907067⟩,⟨-9751397113575,6037249009282⟩,⟨-5990934648969,6824104566449⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26813706104237,28186077177874⟩,⟨-258823827671460,-214163355823282⟩,⟨-99255934226551,-65413729174359⟩,⟨2330259902813714,4188922642043674⟩,⟨473055092908948,2061273563293963⟩,⟨-466273237792100,1062358340457207⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13867237646,14512250883⟩,⟨171447399254,182250185502⟩,⟨40402774024,44016791390⟩,⟨411368443574,646369080043⟩,⟨66378152080,156644129432⟩,⟨12215097407,44998985272⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338179265524,372022826390⟩,⟨764906739519,1970932902601⟩,⟨-324761377349,303364642123⟩,⟨-46381320148713,5069345519115⟩,⟨-19228714517983,13152289465008⟩,⟨-13803398976145,10368024414101⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372022826390,-338179265524⟩,⟨-1970932902601,-764906739519⟩,⟨-303364642123,324761377349⟩,⟨-5069345519115,46381320148713⟩,⟨-13152289465008,19228714517983⟩,⟨-10368024414101,13803398976145⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57415828364,107980435275⟩,⟨-1315754351526,253406213070⟩,⟨-532962191341,379617537302⟩,⟨-29122672064205,33863009955427⟩,⟨-23731744959384,19228588196607⟩,⟨-17272124026353,17981645683027⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239986999126,242438150388⟩,⟨1545395651210,1553666697464⟩,⟨304892499720,306932212697⟩,⟨-3897716375552,-3884154009679⟩,⟨-1540252447540,-1532376886800⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1703584003077,-1615186279380⟩,⟨-5678272814098,-2740826174848⟩,⟨-464513058217,1455006493253⟩,⟨-18674056966623,105354432450578⟩,⟨-56342762735077,39660595958937⟩,⟨-42115288148955,45409034081676⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-195718117058,-181391813415⟩,⟨-1881304659854,-1429123207641⟩,⟨-350180266703,-97086281718⟩,⟨-7080741387023,12671009883671⟩,⟨-7014245918386,6394255480218⟩,⟨-4858045600696,6038395850796⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44268882068,61046336973⟩,⟨-335909008644,124543489823⟩,⟨-45287766983,209845930979⟩,⟨-10978457762575,8786855873992⟩,⟨-8554498365926,4861878593418⟩,⟨-5207145911224,5689979715138⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2616187029,6538283672⟩,⟨-117982385996,35647624158⟩,⟨-32990224473,50982711193⟩,⟨-3681307576621,4065123584462⟩,⟨-2870468451745,2012009776398⟩,⟨-1910561115132,1955829871049⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1782367616,3389373213⟩,⟨-37300223148,13829637916⟩,⟨-5028873210,23301846186⟩,⟨-1295174865334,1180961092733⟩,⟨-1078133079364,587415021992⟩,⟨-595501910701,711930140476⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3069397186,5885501804⟩,⟨-88503423849,12056686432⟩,⟨-19491464966,35025316072⟩,⟨-2391988282933,2699062983376⟩,⟨-2042361259204,1257553820851⟩,⟨-1171407223281,1293868037179⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5885501804,-3069397186⟩,⟨-12056686432,88503423849⟩,⟨-35025316072,19491464966⟩,⟨-2699062983376,2391988282933⟩,⟨-1257553820851,2042361259204⟩,⟨-1293868037179,1171407223281⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3269314775,3468886486⟩,⟨-130039072428,124151048007⟩,⟨-68015540545,70474176159⟩,⟨-6380370559997,6457111867395⟩,⟨-4128022272596,4054371035602⟩,⟨-3204429152311,3127237094330⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50099913934,66576124682⟩,⟨-390118630368,206742763814⟩,⟨-7321493990,285075895438⟩,⟨-14490777456476,11007383907067⟩,⟨-9751397113575,6037249009282⟩,⟨-5990934648969,6824104566449⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3269314775,3468886486⟩,⟨-130039072428,124151048007⟩,⟨-68015540545,70474176159⟩,⟨-6380370559997,6457111867395⟩,⟨-4128022272596,4054371035602⟩,⟨-3204429152311,3127237094330⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (521/5120) u, BivariateJet2.affineZ (629/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000052

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000053Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2070745208640,-2070745169984⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2070745208640,-2070745169984⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-181388636352,-181388636288⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-181388636352,-181388636288⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨96580498496,96580498560⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-105888220416,-105888220352⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨96580622528,96580622592⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-105888369536,-105888369472⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-9307747008,-9307746944⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-9307721920,-9307721856⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨202468718848,202468718912⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨202468992000,202468992064⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1889356533632,1889356572224⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1889356533696,1889356572288⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2077414445888,-2077414407168⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2064111246400,-2064111207744⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-182582749440,-182582749376⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-180196708096,-180196708032⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨94012516160,94012516224⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-102808938176,-102808938112⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨99169768576,99169768640⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-109009106048,-109009105984⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9839337472,-9839337408⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8796421952,-8796421888⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨196821454272,196821454336⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨208178874624,208178874688⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1881528458304,1881528496896⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1897217699136,1897217737728⟩



end LaneCBRB2Cell000053Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000053
open Set LaneCBRB2Cell000053Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111883898060,111883898061⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨138942192025,138942192026⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111883898061,-111883898060⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437871915827,437871915828⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨55332642488,55332642489⟩,⟨-138942192026,-138942192025⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨167216540548,167216540550⟩,⟨960569435750,960569435751⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨55332642487,55332642490⟩,⟨-138942192026,-138942192025⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2070745208640,-2070745169984⟩,⟨6316105215545,6316105215629⟩,⟨2879172487032,2879172487075⟩,⟨-36282640480651,-36282640479689⟩,⟨-23769005733095,-23769005732548⟩,⟨-7539378393926,-7539378393707⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-314924227632,-314924221748⟩,⟨-848501524859,-848501491060⟩,⟨-386786185825,-386786170415⟩,⟨5517956763354,5517956763726⟩,⟨3486573099641,3486573138505⟩,⟨1146607949390,1146607949479⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨314924221748,314924227632⟩,⟨848501491060,848501524859⟩,⟨386786170415,386786185825⟩,⟨-5517956763726,-5517956763354⟩,⟨-3486573138505,-3486573099641⟩,⟨-1146607949479,-1146607949390⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-167216540550,-167216540548⟩,⟨-960569435751,-960569435750⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨932295087226,932295087228⟩,⟨-960569435751,-960569435750⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-181388636352,-181388636288⟩,⟨-1132857266296,-1132857266290⟩,⟨-516408666662,-516408666659⟩,⟨-1167214200723,-1167214200710⟩,⟨764649999582,764649999593⟩,⟨-242542147138,-242542147134⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-153802588603,-153802588547⟩,⟨-802102371280,-802102371215⟩,⟨-365635308528,-365635308496⟩,⟨989701279699,989701279726⟩,⟨1369274547268,1369274547352⟩,⟨205655717051,205655717060⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨153802588547,153802588603⟩,⟨802102371215,802102371280⟩,⟨365635308496,365635308528⟩,⟨-989701279726,-989701279699⟩,⟨-1369274547352,-1369274547268⟩,⟨-205655717060,-205655717051⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨468726810295,468726816235⟩,⟨1650603862275,1650603896139⟩,⟨752421478911,752421494353⟩,⟨-6507658043452,-6507658043053⟩,⟨-4855847685857,-4855847646909⟩,⟨-1352263666539,-1352263666441⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨830387195654,830387207542⟩,⟨4045168798519,4045168890327⟩,⟨752421478911,752421494353⟩,⟨-18536909840177,-18536909839273⟩,⟨-4855847685857,-4855847646909⟩,⟨-1352263666539,-1352263666441⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨110665284974,110665284980⟩,⟨-277884384052,-277884384050⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10924164880008,10924164880601⟩,⟨27430958402991,27430958406168⟩,⟨-86447796275296,-86447796265711⟩,⟨137760183441333,137760183465754⟩,⟨-217073426680765,-217073426582369⟩,⟨1368200052138443,1368200052367527⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8250287136954,8250287255515⟩,⟨60907411848207,60907413061531⟩,⟨-57812547176873,-57812546081124⟩,⟨121708350907468,121708357038653⟩,⟨-511461049617566,-511461039165666⟩,⟨901557626111402,901557643520535⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨100949262336,100949397760⟩,⟨-736221635942,-736219615312⟩,⟨698810360587,698812277867⟩,⟨9201841230120,9201890340073⟩,⟨-3948421193857,-3948361493080⟩,⟨-1281718308238,-1281647856159⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1200460890112,1200461025536⟩,⟨-736221635942,-736219615312⟩,⟨698810360587,698812277867⟩,⟨9201841230120,9201890340073⟩,⟨-3948421193857,-3948361493080⟩,⟨-1281718308238,-1281647856159⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨96580498496,96580622592⟩,⟨-674311221637,-674309294856⟩,⟨640045866322,640047694579⟩,⟨8014494979903,8014543274191⟩,⟨-3223862416139,-3223805084910⟩,⟨-1546520495692,-1546453707121⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨105447826346,105447973732⟩,⟨-800891106904,-800888659580⟩,⟨760193400652,760195722885⟩,⟨10461631654632,10461695781180⟩,⟨-4723820967223,-4723747484596⟩,⟨-987516038728,-987432038369⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-100949397760,-100949262336⟩,⟨736219615312,736221635942⟩,⟨-698812277867,-698810360587⟩,⟨-9201890340073,-9201841230120⟩,⟨3948361493080,3948421193857⟩,⟨1281647856159,1281718308238⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨998562230016,998562365440⟩,⟨736219615312,736221635942⟩,⟨-698812277867,-698810360587⟩,⟨-9201890340073,-9201841230120⟩,⟨3948361493080,3948421193857⟩,⟨1281647856159,1281718308238⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-105888369536,-105888220352⟩,⟨810647442411,810649777257⟩,⟨-769458529526,-769456314065⟩,⟨-10729830359648,-10729771467951⟩,⟨4914823924573,4914893517778⟩,⟨872734252817,872815119458⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-96166459804,-96166311274⟩,⟨665317756287,665320271099⟩,⟨-631513597825,-631511211537⟩,⟨-7772913792426,-7772846901809⟩,⟨3052884149840,3052960039087⟩,⟨1647248144231,1647334152183⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨9281366542,9281662458⟩,⟨-135573350617,-135568388481⟩,⟨128679802827,128684511348⟩,⟨2688717862206,2688848879371⟩,⟨-1670936817383,-1670787445509⟩,⟨659732105503,659902113814⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4640683271,4640831229⟩,⟨-67786675309,-67784194240⟩,⟨64339901413,64342255674⟩,⟨1344358931103,1344424439686⟩,⟨-835468408692,-835393722754⟩,⟨329866052751,329951056907⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4640831229,-4640683271⟩,⟨67784194240,67786675309⟩,⟨-64342255674,-64339901413⟩,⟨-1344424439686,-1344358931103⟩,⟨835393722754,835468408692⟩,⟨-329951056907,-329866052751⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757482552387,757482719609⟩,⟨67784194240,67786675309⟩,⟨-64342255674,-64339901413⟩,⟨-1344424439686,-1344358931103⟩,⟨835393722754,835468408692⟩,⟨-329951056907,-329866052751⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨9268436375,9268461243⟩,⟨-135189349324,-135188796926⟩,⟨128319498642,128320022848⟩,⟨2675621374296,2675638070858⟩,⟨-1660867310514,-1660850239222⟩,⟨652921205526,652939332293⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9268461243,-9268436375⟩,⟨135188796926,135189349324⟩,⟨-128320022848,-128319498642⟩,⟨-2675638070858,-2675621374296⟩,⟨1660850239222,1660867310514⟩,⟨-652939332293,-652921205526⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090243166533,1090243191401⟩,⟨135188796926,135189349324⟩,⟨-128320022848,-128319498642⟩,⟨-2675638070858,-2675621374296⟩,⟨1660850239222,1660867310514⟩,⟨-652939332293,-652921205526⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9307747008,-9307721856⟩,⟨136338071484,136338631689⟩,⟨-129410907153,-129410375538⟩,⟨-2715290306245,-2715273267258⟩,⟨1691016277412,1691033663895⟩,⟨-673721625781,-673703204750⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4653873504,-4653860928⟩,⟨68169035742,68169315845⟩,⟨-64705453577,-64705187769⟩,⟨-1357645153123,-1357636633629⟩,⟨845508138706,845516831948⟩,⟨-336860812891,-336851602375⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4653860928,4653873504⟩,⟨-68169315845,-68169035742⟩,⟨64705187769,64705453577⟩,⟨1357636633629,1357645153123⟩,⟨-845516831948,-845508138706⟩,⟨336851602375,336860812891⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766777244544,766777276384⟩,⟨-68169315845,-68169035742⟩,⟨64705187769,64705453577⟩,⟨1357636633629,1357645153123⟩,⟨-845516831948,-845508138706⟩,⟨336851602375,336860812891⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272560791633,272560797851⟩,⟨33797199231,33797337331⟩,⟨-32080005712,-32079874660⟩,⟨-668909517715,-668905343574⟩,⟨415212559805,415216827629⟩,⟨-163234833074,-163230301381⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533554489088,1533554552768⟩,⟨-136338631690,-136338071484⟩,⟨129410375538,129410907154⟩,⟨2715273267258,2715290306246⟩,⟨-1691033663896,-1691016277412⟩,⟨673703204750,673721625782⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1210666315350,1210666479540⟩,⟨-892602212818,-892599520877⟩,⟨847244191910,847246746247⟩,⟨12472588792974,12472659120780⟩,⟨-6036422945373,-6036341900312⟩,⟨-368136810137,-368043982427⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1321821002924,1321821331304⟩,⟨-1785204425636,-1785199041754⟩,⟨1694488383821,1694493492494⟩,⟨24945177585954,24945318241550⟩,⟨-12072845890743,-12072683800626⟩,⟨-736273474217,-736088110911⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨202468718848,202468992064⟩,⟨-1484961291737,-1484956444428⟩,⟨1409501902427,1409506502067⟩,⟨18744252417045,18744387664682⟩,⟨-8138767346705,-8138617596723⟩,⟨-2419344854134,-2419178720993⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨69546608661,69546717312⟩,⟨-500979151750,-500977411570⟩,⟨475521431881,475523083105⟩,⟨6125176978592,6125221963083⟩,⟨-2557309789453,-2557257709763⟩,⟨-995091019726,-995031226421⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380156803256,380156827715⟩,⟨13341632772,13341966990⟩,⟨-12664026519,-12663709357⟩,⟨-268253616480,-268243447929⟩,⟨167882732856,167893094230⟩,⟨-68218876460,-68207914263⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3180071306047,3180071510652⟩,⟨-111607654415,-111604844266⟩,⟨105933908898,105936575641⟩,⟨2251731946087,2251817690354⟩,⟨-1411888057217,-1411800828049⟩,⟨577627566968,577719695781⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨201146735558,201147062747⟩,⟨-1456020503522,-1456015188468⟩,⟨1382031227913,1382036271316⟩,⟨17959721741627,17959861548339⟩,⟨-7582242884995,-7582083358561⟩,⟨-2749894407224,-2749712775101⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨403615454406,403616054811⟩,⟨-2940981795259,-2940971632896⟩,⟨2791533130340,2791542773383⟩,⟨36703974158672,36704249213021⟩,⟨-15721010231700,-15720700955284⟩,⟨-5169239261358,-5168891496094⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨521849703701,521849934109⟩,⟨93396637502,93400076670⟩,⟨-88654172604,-88650909206⟩,⟨-1844061596591,-1843970314632⟩,⟨1143115917810,1143219658824⟩,⟨-447094136710,-446976362069⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359516021055,359516259157⟩,⟨96515109397,96518684706⟩,⟨-91614315946,-91610923359⟩,⟨-1896997643546,-1896902257589⟩,⟨1173085535411,1173193604161⟩,⟨-454241161049,-454118779638⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨719032042110,719032518314⟩,⟨193030218794,193037369412⟩,⟨-183228631892,-183221846718⟩,⟨-3793995287092,-3793804515178⟩,⟨2346171070822,2346387208322⟩,⟨-908482322098,-908237559276⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524286027845,1524286116393⟩,⟨-1149834764,-1148722160⟩,⟨1090352690,1091408512⟩,⟨39635196400,39668931950⟩,⟨-30183424674,-30148966898⟩,⟨20763872457,20800420256⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨996815738618,996816456701⟩,⟨266851654371,266862311128⟩,⟨-253302333657,-253292221475⟩,⟨-5234214120470,-5233926857727⟩,⟨3233211701031,3233534459808⟩,⟨-1246241532068,-1245877861834⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67565802178,67565805262⟩,⟨16756150902,16756219754⟩,⟨-15904792148,-15904726810⟩,⟨-329557699231,-329555605204⟩,⟨203884056136,203886192876⟩,⟨-79057459484,-79055195594⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨51027906913,51027909974⟩,⟨261233406467,261233475637⟩,⟨34225035833,34225088411⟩,⟨-1264705879646,-1264703733133⟩,⟨-191463579608,-191461658588⟩,⟨-164572431026,-164570626735⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2138939972612,2138940150249⟩,⟨-380319269146,-380317690646⟩,⟨360992748648,360994246592⟩,⟨7608118863280,7608166986251⟩,⟨-4749265063148,-4749216103620⟩,⟨1909770834123,1909822548273⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2983307237526,2983307609168⟩,⟨-795681007782,-795677672299⟩,⟨755247197344,755250362615⟩,⟨15987984557057,15988086482248⟩,⟨-10003270092312,-10003166695049⟩,⟨4059239258323,4059348143727⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨138454128327,138454153881⟩,⟨671877908974,671878341967⟩,⟨127913591120,127913894352⟩,⟨-3067625872725,-3067613161217⟩,⟨-829074610367,-829063565439⟩,⟨-211129170517,-211118885386⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8731596602393,8731598213955⟩,⟨-42371952368651,-42371909421093⟩,⟨-8066879225343,-8066857124295⟩,⟨604695909160300,604697539970389⟩,⟨130577048775430,130578044028860⟩,⟨28219639212387,28220371681039⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7916053542911,7916060706495⟩,⟨-36295221821069,-36295070191976⟩,⟨-9324987486427,-9324881505675⟩,⟨486081617410441,486086621954419⟩,⟨151860228158436,151864266748097⟩,⟨19403746129805,19407477035848⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15832107085822,15832121412990⟩,⟨-72590443642138,-72590140383952⟩,⟨-18649974972854,-18649763011350⟩,⟨972163234820882,972173243908838⟩,⟨303720456316872,303728533496194⟩,⟨38807492259610,38814954071696⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10805181447606,10805181447704⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230896,2087019636287702⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9705669819830,9705669819928⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230908,2087019636287687⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2394564936256,2394564994112⟩,⟨-12029251796733,-12029251796224⟩,⟨0,0⟩,⟨104822536628670,104822536664337⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7229702370580,7229702370668⟩,⟨-41530766657906,-41530766656849⟩,⟨-18931641675737,-18931641675232⟩,⟨477144006957887,477144006976324⟩,⟨265042288278616,265042288288451⟩,⟨99148495511479,99148495515558⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6130190742804,6130190742892⟩,⟨-41530766657906,-41530766656849⟩,⟨-18931641675738,-18931641675231⟩,⟨477144006957891,477144006976316⟩,⟨265042288278619,265042288288447⟩,⟨99148495511480,99148495515557⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1889356533632,1889356572288⟩,⟨-7448962482065,-7448962481723⟩,⟨-3395581153801,-3395581153640⟩,⟨35115426273358,35115426285276⟩,⟨24533655729417,24533655735310⟩,⟨7296836245377,7296836247923⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100498837339,100498837341⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨141785821375,141785821378⟩,⟨668397722514,668397722521⟩,⟨304686554037,304686554041⟩,⟨-1678369955515,-1678369955510⟩,⟨-1530157093360,-1530157093352⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4283921469888,4283921566400⟩,⟨-19478214278798,-19478214277947⟩,⟨-3395581153801,-3395581153640⟩,⟨139937962902028,139937962949613⟩,⟨24533655729417,24533655735310⟩,⟨7296836245377,7296836247923⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨807230908812,807232109622⟩,⟨-5881963590518,-5881943265792⟩,⟨5583066260680,5583085546766⟩,⟨73407948317344,73408498426042⟩,⟨-31442020463400,-31441401910568⟩,⟨-10338478522716,-10337782992188⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5091152378700,5091153676022⟩,⟨-25360177869316,-25360157543739⟩,⟨2187485106879,2187504393126⟩,⟨213345911219372,213346461375655⟩,⟨-6908364733983,-6907746175258⟩,⟨-3041642277339,-3040946744265⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨465347415934,465347534523⟩,⟨1737022922524,1737025813700⟩,⟨199943051427,199944814256⟩,⟨-31079787713762,-31079702454604⟩,⟨1110851340391,1110923239826⟩,⟨-278015716031,-277952142103⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨40648400244,40648402566⟩,⟨-825248275147,-825248263438⟩,⟨321668947845,321668966201⟩,⟨10254918440852,10254918472134⟩,⟨-6530558220472,-6530558128119⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨505995816178,505995937089⟩,⟨911774647377,911777550262⟩,⟨521611999272,521613780457⟩,⟨-20824869272910,-20824783982470⟩,⟨-5419706880081,-5419634888293⟩,⟨-278015716031,-277952142103⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504862395711,504862407910⟩,⟨2536208829314,2536208952001⟩,⟨0,0⟩,⟨3381169318170,3381172243620⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨232337933971,232337995105⟩,⟨1585823874311,1585825552707⟩,⟨239508411672,239509235326⟩,⟨-3799809105391,-3799754397975⟩,⟨-1285379137349,-1285341853963⟩,⟨-127656388788,-127627194483⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-807232109622,-807230908812⟩,⟨5881943265792,5881963590518⟩,⟨-5583085546766,-5583066260680⟩,⟨-73408498426042,-73407948317344⟩,⟨31441401910568,31442020463400⟩,⟨10337782992188,10338478522716⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3476689360266,3476690657588⟩,⟨-13596271013006,-13596250687429⟩,⟨-8978666700567,-8978647414320⟩,⟨66529464475986,66530014632269⟩,⟨55975057639985,55975676198710⟩,⟨17634619237565,17635314770639⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨448331099151,448331266456⟩,⟨360207920523,360211330286⟩,⟨-194401884422,-194399037853⟩,⟨-13258315027718,-13258217390464⟩,⟨-6846071013411,-6845972085767⟩,⟨-3804910397658,-3804809605786⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨334433081096,334433081100⟩,⟨1921138871500,1921138871502⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-334433081100,-334433081096⟩,⟨-1921138871502,-1921138871500⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨765078546676,765078546680⟩,⟨-1921138871502,-1921138871500⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1314680185627,1314680212533⟩,⟨-8484455741567,-8484455673753⟩,⟨-3867606809094,-3867606778176⟩,⟨50465170762522,50465170772166⟩,⟨32716051024888,32716051106967⟩,⟨10486447872887,10486447874956⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1314680212533,-1314680185627⟩,⟨8484455673753,8484455741567⟩,⟨3867606778176,3867606809094⟩,⟨-50465170772166,-50465170762522⟩,⟨-32716051106967,-32716051024888⟩,⟨-10486447874956,-10486447872887⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-215168584757,-215168557851⟩,⟨8484455673753,8484455741567⟩,⟨3867606778176,3867606809094⟩,⟨-50465170772166,-50465170762522⟩,⟨-32716051106967,-32716051024888⟩,⟨-10486447874956,-10486447872887⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-10828304199,-10828302843⟩,⟨454168315240,454168322079⟩,⟨108947117680,108947129965⟩,⟨-4683960478629,-4683960460849⟩,⟨1458871215042,1458871277096⟩,⟨2552760550311,2552760575078⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437502794952,437502963613⟩,⟨814376235763,814379652365⟩,⟨-85454766742,-85451907888⟩,⟨-17942275506347,-17942177851313⟩,⟨-5387199798369,-5387100808671⟩,⟨-1252149847347,-1252049030708⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100498837341,-100498837339⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨5057578379,5057578381⟩,⟨31371829746,31371829750⟩,⟨40022876823,40022876824⟩,⟨-331995854935,-331995854926⟩,⟨248259301866,248259301870⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨11014617347,11014617618⟩,⟨12990312523,12990314210⟩,⟨87163587057,87163589166⟩,⟨-927317829617,-927317811654⟩,⟨102798145600,102798158703⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1455857952331,1455857973175⟩,⟨-7092102831846,-7092102467804⟩,⟨-1319166332858,-1319166268010⟩,⟨101596713042018,101596720078541⟩,⟨21365845602789,21365847022366⟩,⟨4761443631517,4761443900388⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14584400793,14584401362⟩,⟨-53846407365,-53846399488⟩,⟨102197817468,102197822889⟩,⟨-377668972248,-377668804984⟩,⟨-227658721408,-227658637365⟩,⟨-161454468015,-161454448803⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14584401362,-14584400793⟩,⟨53846399488,53846407365⟩,⟨-102197822889,-102197817468⟩,⟨377668804984,377668972248⟩,⟨227658637365,227658721408⟩,⟨161454448803,161454468015⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115083238703,-115083238132⟩,⟨-821897432168,-821897424289⟩,⟨-102197822889,-102197817468⟩,⟨2576692060536,2576692227800⟩,⟨227658637365,227658721408⟩,⟨161454448803,161454468015⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨95081386103,95081388055⟩,⟨-613619814990,-613619810063⟩,⟨581539722617,581539738033⟩,⟨3649783756197,3649783756994⟩,⟨-3192107672603,-3192107633413⟩,⟨-2337315908405,-2337315908121⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨125896796886,125896801274⟩,⟨-1425787815273,-1425787753042⟩,⟨655937641353,655937680742⟩,⟨21534317187409,21534318516408⟩,⟨-5393880437019,-5393879829835⟩,⟨-4078511326962,-4078511144980⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-125896801274,-125896796886⟩,⟨1425787753042,1425787815273⟩,⟨-655937680742,-655937641353⟩,⟨-21534318516408,-21534317187409⟩,⟨5393879829835,5393880437019⟩,⟨4078511144980,4078511326962⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨973614826502,973614830890⟩,⟨1425787753042,1425787815273⟩,⟨-655937680742,-655937641353⟩,⟨-21534318516408,-21534317187409⟩,⟨5393879829835,5393880437019⟩,⟨4078511144980,4078511326962⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨125550994087,125550994657⟩,⟨775724784317,775724795022⟩,⟨185213760786,185213767089⟩,⟨-2529632497710,-2529632243888⟩,⟨-663036964651,-663036839021⟩,⟨-146421213933,-146421167223⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨12045485799,12045485920⟩,⟨172052054038,172052056544⟩,⟨21393599606,21393600850⟩,⟨689362949444,689363010696⟩,⟨105131075478,105131102882⟩,⟨-14799860197,-14799853988⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨173445570063,173445728764⟩,⟨1682164454038,1682170062321⟩,⟨103734918383,103737539222⟩,⟨-2141335928358,-2141121065198⟩,⟨510380562507,510510041477⟩,⟨-513717466211,-513627142625⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-173445728764,-173445570063⟩,⟨-1682170062321,-1682164454038⟩,⟨-103737539222,-103734918383⟩,⟨2141121065198,2141335928358⟩,⟨-510510041477,-510380562507⟩,⟨513627142625,513717466211⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58892205207,58892425042⟩,⟨-96346188010,-96338901331⟩,⟨135770872450,135774316943⟩,⟨-1658688040193,-1658418469617⟩,⟨-1795889178826,-1795722416470⟩,⟨385970753837,386090271728⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27205255686348,27205280862195⟩,⟨-231995827741627,-231995207014363⟩,⟨-80941122980774,-80940713850586⟩,⟨3159727032758266,3159748832961285⟩,⟨1225692168052041,1225708750553073⟩,⟨286944713917789,286958941669224⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14336412383,14336412514⟩,⟨177156867372,177156870624⟩,⟨42298364468,42298366102⟩,⟨516867775874,516867866677⟩,⟨109921446404,109921488286⟩,⟨28959781294,28959796364⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354726366371,354726697879⟩,⟨1358430368251,1358442626368⟩,⟨-8792547245,-8786194047⟩,⟨-20771622005706,-20771121897642⟩,⟨-3264950535030,-3264640234360⟩,⟨-1769638857264,-1769420553825⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354726697879,-354726366371⟩,⟨-1358442626368,-1358430368251⟩,⟨8786194047,8792547245⟩,⟨20771121897642,20771622005706⟩,⟨3264640234360,3264950535030⟩,⟨1769420553825,1769638857264⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨82776097073,82776597242⟩,⟨-544066390605,-544050715886⟩,⟨-76668572695,-76659360643⟩,⟨2828846391295,2829444154393⟩,⟨-2122559564009,-2122150273641⟩,⟨517270706478,517589826556⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨242284658714,242284658719⟩,⟨1544141554168,1544141554177⟩,⟨304686554037,304686554041⟩,⟨-3877393211067,-3877393211062⟩,⟨-1530157093360,-1530157093352⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1657110085713,-1657108577900⟩,⟨-4236855168772,-4236812566595⟩,⟨480455835366,480479440299⟩,⟨43871221315254,43872759849537⟩,⟨-7824384097982,-7823347222125⟩,⟨1729080077314,1729903074725⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-189222027546,-189221854512⟩,⟨-1652918183233,-1652912236456⟩,⟨-224279477799,-224276518657⟩,⟨2843702098790,2843941850856⟩,⟨-268899002397,-268755641960⟩,⟨579982551309,580084757856⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨53062631168,53062804207⟩,⟨-108776629065,-108770682279⟩,⟨80407076238,80410035384⟩,⟨-1033691112277,-1033451360206⟩,⟨-1799056095757,-1798912735312⟩,⟨231224412100,231326618649⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4433665612,4433708954⟩,⟨-36394884527,-36393343771⟩,⟨6114882804,6115712633⟩,⟨121984109496,122047699792⟩,⟨-309360292927,-309319619271⟩,⟨37828721361,37857846506⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2560812232,2560828935⟩,⟨-10499194052,-10498585826⟩,⟨7760920252,7761231180⟩,⟨-78251992414,-78226172856⟩,⟨-189556329060,-189540470308⟩,⟨34078172765,34088976217⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4400396684,4400425477⟩,⟨-35390476066,-35389317383⟩,⟨5427539613,5428125758⟩,⟨89571804735,89624949471⟩,⟨-288744313500,-288712698239⟩,⟨27615774550,27636371280⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4400425477,-4400396684⟩,⟨35389317383,35390476066⟩,⟨-5428125758,-5427539613⟩,⟨-89624949471,-89571804735⟩,⟨288712698239,288744313500⟩,⟨-27636371280,-27615774550⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨33240135,33312270⟩,⟨-1005567144,-1002867705⟩,⟨686757046,688173020⟩,⟨32359160025,32475895057⟩,⟨-20647594688,-20575305771⟩,⟨10192350081,10242071956⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58892205207,58892425042⟩,⟨-96346188010,-96338901331⟩,⟨135770872450,135774316943⟩,⟨-1658688040193,-1658418469617⟩,⟨-1795889178826,-1795722416470⟩,⟨385970753837,386090271728⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨33240135,33312270⟩,⟨-1005567144,-1002867705⟩,⟨686757046,688173020⟩,⟨32359160025,32475895057⟩,⟨-20647594688,-20575305771⟩,⟨10192350081,10242071956⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111669149696,112098646426⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨137009456742,140874927309⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112098646426,-111669149696⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437657167462,438086664192⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨54536186101,56129853850⟩,⟨-140874927309,-137009456742⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨166205335797,168228500276⟩,⟨958636700467,962502171034⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨54106689371,56559350580⟩,⟨-140874927309,-137009456742⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2077414445888,-2064111207744⟩,⟨6265479376246,6367318616679⟩,⟨2860449589780,2898110213749⟩,⟨-36873413015475,-35703334846556⟩,⟨-24056767931486,-23486256904932⟩,⟨-7638884936597,-7441641951733⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-317850496398,-312016978937⟩,⟨-871441271236,-825428556640⟩,⟨-395326042185,-378193662631⟩,⟨5283689443354,5750763400278⟩,⟨3371264207573,3601121414908⟩,⟨1108414265760,1184531604428⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨312016978937,317850496398⟩,⟨825428556640,871441271236⟩,⟨378193662631,395326042185⟩,⟨-5750763400278,-5283689443354⟩,⟨-3601121414908,-3371264207573⟩,⟨-1184531604428,-1108414265760⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-168228500276,-166205335797⟩,⟨-962502171034,-958636700467⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨931283127500,933306291979⟩,⟨-962502171034,-958636700467⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-182582749440,-180196708032⟩,⟨-1136370130160,-1129352933794⟩,⟨-517223352415,-515596164666⟩,⟨-1174464225841,-1160004148068⟩,⟨760753162380,768539490835⟩,⟨-243308019239,-241779530386⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-154983016600,-152626083782⟩,⟨-807484152459,-796727399124⟩,⟨-367311648320,-363960626706⟩,⟨972380338268,1007015401983⟩,⟨1360843762462,1377713093354⟩,⟨203934004020,207375805058⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨152626083782,154983016600⟩,⟨796727399124,807484152459⟩,⟨363960626706,367311648320⟩,⟨-1007015401983,-972380338268⟩,⟨-1377713093354,-1360843762462⟩,⟨-207375805058,-203934004020⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨464643062719,472833512998⟩,⟨1622155955764,1678925423695⟩,⟨742154289337,762637690505⟩,⟨-6757778802261,-6256069781622⟩,⟨-4978834508262,-4732107970035⟩,⟨-1391907409486,-1312348269780⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨825360858869,835437870208⟩,⟨4009666486044,4080532827729⟩,⟨742154289337,762637690505⟩,⟨-18891939051228,-18180173935767⟩,⟨-4978834508262,-4732107970035⟩,⟨-1391907409486,-1312348269780⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨108213378742,113118701160⟩,⟨-281749854618,-274018913484⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10687232148331,11171685365235⟩,⟨25888767386876,29087168001635⟩,⟨-90453998053734,-82697974819059⟩,⟨125425978870773,151465658885837⟩,⟨-263261869110097,-173633600554319⟩,⟨1279836527223173,1464761223828605⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8022491879163,8488540541445⟩,⟨58407578634819,63561811256996⟩,⟨-61515602561292,-54329323754603⟩,⟨91019992885813,154274581212430⟩,⟨-568841602711451,-457741263359233⟩,⟨821100700103881,988568274912850⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨98148777984,103779591936⟩,⟨-812261672216,-667143743718⟩,⟨620561052016,786113001119⟩,⟨7028807710819,11613328055687⟩,⟨-7017229964267,-1102584005037⟩,⟨-4845695258664,2472644390094⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1197660405760,1203291219712⟩,⟨-812261672216,-667143743718⟩,⟨620561052016,786113001119⟩,⟨7028807710819,11613328055687⟩,⟨-7017229964267,-1102584005037⟩,⟨-4845695258664,2472644390094⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨94012516160,99169768640⟩,⟨-745696483831,-609604966444⟩,⟨567039866375,721690707416⟩,⟨5916861445775,10323626100486⟩,⟨-6127779670408,-518034362061⟩,⟨-4922287403923,1977576473596⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨102404618019,108530104504⟩,⟨-889341966899,-721065219705⟩,⟨670717511070,860711894373⟩,⟨7785797477005,13447262103521⟩,⟨-8405371725021,-1346670741836⟩,⟨-5183870580111,3419220661141⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-103779591936,-98148777984⟩,⟨667143743718,812261672216⟩,⟨-786113001119,-620561052016⟩,⟨-11613328055687,-7028807710819⟩,⟨1102584005037,7017229964267⟩,⟨-2472644390094,4845695258664⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨995732035840,1001362849792⟩,⟨667143743718,812261672216⟩,⟨-786113001119,-620561052016⟩,⟨-11613328055687,-7028807710819⟩,⟨1102584005037,7017229964267⟩,⟨-2472644390094,4845695258664⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-109009106048,-102808938112⟩,⟨732533969847,896919172281⟩,⟨-868045171157,-681385466394⟩,⟨-13555376160760,-8205778019618⟩,⟨1664617361676,8456698649524⟩,⟨-3415660770622,4928469229887⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-99278321692,-93105111999⟩,⟨582862069087,754474238902⟩,⟨-732533375001,-539133781911⟩,⟨-10799171773498,-4954682854161⟩,⟨-470744248987,6771828581672⟩,⟨-2822033045791,5974916290963⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨3126296327,15424992505⟩,⟨-306479897812,33409019197⟩,⟨-61815863931,321578112462⟩,⟨-3013374296493,8492579249360⟩,⟨-8876115974008,5425157839836⟩,⟨-8005903625902,9394136952104⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1563148163,7712496253⟩,⟨-153239948906,16704509599⟩,⟨-30907931966,160789056231⟩,⟨-1506687148247,4246289624680⟩,⟨-4438057987004,2712578919918⟩,⟨-4002951812951,4697068476052⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7712496253,-1563148163⟩,⟨-16704509599,153239948906⟩,⟨-160789056231,30907931966⟩,⟨-4246289624680,1506687148247⟩,⟨-2712578919918,4438057987004⟩,⟨-4697068476052,4002951812951⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754410887363,760560254717⟩,⟨-16704509599,153239948906⟩,⟨-160789056231,30907931966⟩,⟨-4246289624680,1506687148247⟩,⟨-2712578919918,4438057987004⟩,⟨-4697068476052,4002951812951⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8761328553,9795443205⟩,⟨-153333867072,-119106231404⟩,⟨110789749522,148397678408⟩,⟨2064461409250,3392406999027⟩,⟨-2486148738268,-949913912638⟩,⟨-214255591912,1590858439770⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9795443205,-8761328553⟩,⟨119106231404,153333867072⟩,⟨-148397678408,-110789749522⟩,⟨-3392406999027,-2064461409250⟩,⟨949913912638,2486148738268⟩,⟨-1590858439770,214255591912⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1089716184571,1090750299223⟩,⟨119106231404,153333867072⟩,⟨-148397678408,-110789749522⟩,⟨-3392406999027,-2064461409250⟩,⟨949913912638,2486148738268⟩,⟨-1590858439770,214255591912⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9839337472,-8796421888⟩,⟨120062938751,154712183012⟩,⟨-149731623018,-111679655668⟩,⟨-3444670834510,-2094154427787⟩,⟨969739028258,2529565417048⟩,⟨-1625549113608,204838000224⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4919668736,-4398210944⟩,⟨60031469375,77356091506⟩,⟨-74865811509,-55839827834⟩,⟨-1722335417255,-1047077213893⟩,⟨484869514129,1264782708524⟩,⟨-812774556804,102419000112⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4398210944,4919668736⟩,⟨-77356091506,-60031469375⟩,⟨55839827834,74865811509⟩,⟨1047077213893,1722335417255⟩,⟨-1264782708524,-484869514129⟩,⟨-102419000112,812774556804⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766521594560,767043071616⟩,⟨-77356091506,-60031469375⟩,⟨55839827834,74865811509⟩,⟨1047077213893,1722335417255⟩,⟨-1264782708524,-484869514129⟩,⟨-102419000112,812774556804⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272429046142,272687574806⟩,⟨29776557851,38333466768⟩,⟨-37099419602,-27697437380⟩,⟨-848101749757,-516115352312⟩,⟨237478478159,621537184567⟩,⟨-397714609943,53563897978⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533043189120,1534086143232⟩,⟨-154712183012,-120062938750⟩,⟨111679655668,149731623018⟩,⟨2094154427786,3444670834510⟩,⟨-2529565417048,-969739028258⟩,⟨-204838000224,1625549113608⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1207280477666,1214107587284⟩,⟨-990400051020,-804333431936⟩,⟨748171597791,958516673933⟩,⟨9545944675774,15776089493790⟩,⟨-10119996637116,-2326233838351⟩,⟨-4981103745633,4528388151340⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1315049327556,1328703546792⟩,⟨-1980800102041,-1608666863873⟩,⟨1496343195582,1917033347867⟩,⟨19091889351555,31552178987573⟩,⟨-20239993274229,-4652467676702⟩,⟨-9957458563057,9056776302678⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨196821454272,208178874688⟩,⟨-1656145285853,-1331183262298⟩,⟨1238234628527,1602829956754⟩,⟨13304096401813,24769081033660⟩,⟨-15423505444251,-1435678848441⟩,⟨-10661972640454,6177902977852⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨67343086532,71786992410⟩,⟨-563438817616,-443285284137⟩,⟨410610838362,546691732721⟩,⟨4195489039769,8200127910976⟩,⟨-5144805530211,-109280178490⟩,⟨-4025150524316,2132414017211⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379846363745,380465489745⟩,⟨3147451234,23736182185⟩,⟨-24091535549,-1483762915⟩,⟨-675221561115,128185718608⟩,⟨-290188312583,637361125215⟩,⟨-615814462622,472257123552⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177491394620,3182670508402⟩,⟨-198881585380,-26286219067⟩,⟨12391778022,201859033053⟩,⟨-1073612242255,5682426723811⟩,⟨-5365572443288,2431235347731⟩,⟨-3956868486545,5185414169975⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨194615566163,207796205023⟩,⟨-1643927334022,-1282665262653⟩,⟨1187387993933,1595645251466⟩,⟨12075691769839,24311106974079⟩,⟨-15444912855087,-171887452404⟩,⟨-11900377246008,6711821534769⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨391437020435,415975079711⟩,⟨-3300072619875,-2613848524951⟩,⟨2425622622460,3198475208220⟩,⟨25379788171652,49080188007739⟩,⟨-30868418299338,-1607566300845⟩,⟨-22562349886462,12889724512621⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517625982840,526098939241⟩,⟨-23109871246,211999967312⟩,⟨-222443787722,42759610750⟩,⟨-5879190060563,2127142294178⟩,⟨-3797538776844,6148451289774⟩,⟨-6507204041156,5584914417491⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355160115792,363916063394⟩,⟨-23978531629,219968682094⟩,⟨-230805067782,44366871103⟩,⟨-6105009986845,2251417867100⟩,⟨-3986785032905,6388500186816⟩,⟨-6761178211261,5843635961312⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨710320231584,727832126788⟩,⟨-47957063258,439937364188⟩,⟨-461610135564,88733742206⟩,⟨-12210019973690,4502835734200⟩,⟨-7973570065810,12777000373632⟩,⟨-13522356422522,11687271922624⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523247745915,1525324814679⟩,⟨-35605951608,33270928322⟩,⟨-36718022740,38941873496⟩,⟨-1298252571241,1380209425260⟩,⟨-1579651504410,1516409710010⟩,⟨-1795696439994,1839804705520⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨984067529896,1009703195369⟩,⟨-90099323746,632338041234⟩,⟨-664685968392,148876029466⟩,⟨-17826537405773,7186938175638⟩,⟨-12135858219041,18759542840340⟩,⟨-19980601146200,17462165191395⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67500500501,67628674018⟩,⟨14755640682,19014005534⟩,⟨-18401898630,-13725341788⟩,⟨-419059080620,-253085742688⟩,⟨115094528000,306792086424⟩,⟨-195877299873,29072137062⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50670015359,51386046277⟩,⟨257235317727,265432431401⟩,⟨31579605074,36605175300⟩,⟨-1372795138763,-1164956627939⟩,⟨-278174454158,-94266556361⟩,⟨-259973721434,-77005864416⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137513929216,2140423289217⟩,⟨-431722248592,-334806228268⟩,⟨311428694630,417824063472⟩,⟨5865957594767,9655846324295⟩,⟨-7100855438614,-2728593972556⟩,⟨-548910597467,4576853697037⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2980324253106,2986411080782⟩,⟨-903536309976,-700227803355⟩,⟨651335047949,874449287151⟩,⟨12323149564508,20299502564940⟩,⟨-14949318583303,-5757706435072⟩,⟨-1101357764930,9664085125294⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137345592229,139570927786⟩,⟨655032179146,688678301945⟩,⟨115615530183,140291915766⟩,⟨-3597026184774,-2536657081522⟩,⟨-1331916224292,-329867993734⟩,⟨-720178846960,301147719272⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8661730911957,8802072203373⟩,⟨-44135352582045,-40651105244024⟩,⟨-8990893352173,-7175065950867⟩,⟨538990507226291,673129745478501⟩,⟨87819334321606,175522845089593⟩,⟨-7412532888313,64521659356619⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7752285585550,8083116362845⟩,⟨-41251648584800,-31320767110762⟩,⟨-13577616876562,-5229896365925⟩,⟨288924332289769,682916228918272⟩,⟨-29700936314547,338782275423351⟩,⟨-169195308541026,209914292803452⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15504571171100,16166232725690⟩,⟨-82503297169600,-62641534221524⟩,⟨-27155233753124,-10459792731850⟩,⟨577848664579538,1365832457836544⟩,⟨-59401872629094,677564550846702⟩,⟨-338390617082052,419828585606904⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10784481866270,10825960642718⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533866,2099083303790624⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9684970238494,9726449014942⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533869,2099083303790615⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2392217469760,2396916459264⟩,⟨-12101371604921,-11957606413725⟩,⟨0,0⟩,⟨101381360168522,108260423343400⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7186212904657,7273688379603⟩,⟨-42122238875313,-40950061472762⟩,⟨-19172103370282,-18695390968062⟩,⟨466701322900225,487863354950534⟩,⟨260036203138570,270171152864835⟩,⟨97274502741830,101068269207549⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6086701276881,6174176751827⟩,⟨-42122238875314,-40950061472762⟩,⟨-19172103370283,-18695390968061⟩,⟨466701322900232,487863354950533⟩,⟨260036203138572,270171152864836⟩,⟨97274502741831,101068269207550⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1881528458304,1897217737728⟩,⟨-7609029805274,-7292481339134⟩,⟨-3463279964916,-3329318317460⟩,⟨30453928307221,39761244068057⟩,⟨22340659737719,26722542574150⟩,⟨6414107988541,8175969578660⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100284130918,100713627649⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨140775432490,142798596970⟩,⟨664696824788,672097301106⟩,⟨303665795562,305706711189⟩,⟨-1685130754132,-1671622746438⟩,⟨-1534094873726,-1526219312984⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4273745928064,4294134196992⟩,⟨-19710401410195,-19250087752859⟩,⟨-3463279964916,-3329318317460⟩,⟨131835288475743,148021667411457⟩,⟨22340659737719,26722542574150⟩,⟨6414107988541,8175969578660⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨782874040870,831950159422⟩,⟨-6600145239750,-5227697049902⟩,⟨4851245244920,6396950416440⟩,⟨50759576343304,98160376015478⟩,⟨-61736836598676,-3215132601690⟩,⟨-45124699772924,25779449025242⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5056619968934,5126084356414⟩,⟨-26310546649945,-24477784802761⟩,⟨1387965280004,3067632098980⟩,⟨182594864819047,246182043426935⟩,⟨-39396176860957,23507409972460⟩,⟨-38710591784383,33955418603902⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461203616366,469541692992⟩,⟨1615536663417,1852281472015⟩,⟨126593378672,280990531775⟩,⟨-35530510868719,-26536554378878⟩,⟨-2503680644809,4597763073780⟩,⟨-3545832557434,3110265775776⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨39609799013,41694071954⟩,⟨-846500624475,-804187206281⟩,⟨320394994437,322946015318⟩,⟨9890173778525,10627276481193⟩,⟨-6562818552468,-6498504886492⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨500813415379,511235764946⟩,⟨769036038942,1048094265734⟩,⟨446988373109,603936547093⟩,⟨-25640337090194,-15909277897685⟩,⟨-9066499197277,-1900741812712⟩,⟨-3545832557434,3110265775776⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504367106722,505357825907⟩,⟨2516159178967,2556424289217⟩,⟨0,0⟩,⟨2234856254543,4531068346710⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229732734917,234974317845⟩,⟨1498849773253,1670376301720⟩,⟨205042153978,277581475916⟩,⟨-7247094651598,-317345433736⟩,⟨-3144243623896,532278508610⟩,⟨-1629736500268,1429541180587⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-831950159422,-782874040870⟩,⟨5227697049902,6600145239750⟩,⟨-6396950416440,-4851245244920⟩,⟨-98160376015478,-50759576343304⟩,⟨3215132601690,61736836598676⟩,⟨-25779449025242,45124699772924⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3441795768642,3511260156122⟩,⟨-14482704360293,-12649942513109⟩,⟨-9860230381356,-8180563562380⟩,⟨33674912460265,97262091068153⟩,⟨25555792339409,88459379172826⟩,⟨-19365341036701,53300669351584⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨440668634721,456023393682⟩,⟨199762194828,526695063086⟩,⟨-330029628470,-71128469287⟩,⟨-18775522344842,-7895548330436⟩,⟨-11681070312373,-1728048501423⟩,⟨-9112957508146,1313100196880⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨332410671594,336457000552⟩,⟨1917273400934,1925004342068⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-336457000552,-332410671594⟩,⟨-1925004342068,-1917273400934⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨763054627224,767100956182⟩,⟨-1925004342068,-1917273400934⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1305769725479,1323639972449⟩,⟨-8630237445885,-8341854569131⟩,⟨-3928086655422,-3808400450688⟩,⟨46567376474404,54383889775406⟩,⟨30878341504388,34564956719693⟩,⟨9752252369949,11223765931825⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1323639972449,-1305769725479⟩,⟨8341854569131,8630237445885⟩,⟨3808400450688,3928086655422⟩,⟨-54383889775406,-46567376474404⟩,⟨-34564956719693,-30878341504388⟩,⟨-11223765931825,-9752252369949⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-224128344673,-206258097703⟩,⟨8341854569131,8630237445885⟩,⟨3808400450688,3928086655422⟩,⟨-54383889775406,-46567376474404⟩,⟨-34564956719693,-30878341504388⟩,⟨-11223765931825,-9752252369949⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11529258356,-10149908869⟩,⟨436202248115,472659566690⟩,⟨98109286515,119962074174⟩,⟨-5009029003677,-4370515397747⟩,⟨1245384912104,1668660794223⟩,⟨2454488454033,2650288178679⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429139376365,445873484813⟩,⟨635964442943,999354629776⟩,⟨-231920341955,48833604887⟩,⟨-23784551348519,-12266063728183⟩,⟨-10435685400269,-59387707200⟩,⟨-6658469054113,3963388375559⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100713627649,-100284130918⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4934956742,5180752282⟩,⟨30170063698,32574389618⟩,⟨39917784923,40128086017⟩,⟨-337638116559,-326358123148⟩,⟨247702508009,248816179610⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10737030361,11293950971⟩,⟨8621232049,17342081480⟩,⟨86849488477,87478538129⟩,⟨-998049762640,-856173449082⟩,⟨97273538155,108293929972⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1447056522962,1464723952710⟩,⟨-7241504256438,-6945117345571⟩,⟨-1353412486817,-1285480636832⟩,⟨98155650744237,105129612569051⟩,⟨20535728117096,22218046964073⟩,⟨4557002018836,4971264174977⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14130900873,15045334756⟩,⟨-63036881290,-44718557242⟩,⟨100399797290,103982225046⟩,⟨-599477702871,-155845210257⟩,⟨-268932264276,-186184542592⟩,⟨-170858059059,-152014270183⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-15045334756,-14130900873⟩,⟨44718557242,63036881290⟩,⟨-103982225046,-100399797290⟩,⟨155845210257,599477702871⟩,⟨186184542592,268932264276⟩,⟨152014270183,170858059059⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115758962405,-114415031791⟩,⟨-831454771142,-812277453634⟩,⟨-103982225046,-100399797290⟩,⟨2354868465809,2798500958423⟩,⟨186184542592,268932264276⟩,⟨152014270183,170858059059⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨92589539996,97593695641⟩,⟨-634492785341,-593317249219⟩,⟨570783913524,592087779248⟩,⟨3316053200429,3995149367405⟩,⟨-3414698055547,-2965926048456⟩,⟨-2444164588687,-2229874116042⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨121856189988,130010288230⟩,⟨-1488007858732,-1365705262207⟩,⟨631072961324,680504937495⟩,⟨20125315861642,23011255322187⟩,⟨-6025497670297,-4755704250604⟩,⟨-4329898442105,-3828111566197⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-130010288230,-121856189988⟩,⟨1365705262207,1488007858732⟩,⟨-680504937495,-631072961324⟩,⟨-23011255322187,-20125315861642⟩,⟨4755704250604,6025497670297⟩,⟨3828111566197,4329898442105⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨969501339546,977655437788⟩,⟨1365705262207,1488007858732⟩,⟨-680504937495,-631072961324⟩,⟨-23011255322187,-20125315861642⟩,⟨4755704250604,6025497670297⟩,⟨3828111566197,4329898442105⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124129628942,126972577015⟩,⟨760958037939,790864774588⟩,⟨179378953604,191026865196⟩,⟨-2835706542936,-2231552939111⟩,⟨-793968347024,-530978704681⟩,⟨-198693313314,-93456977446⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11906012786,12187353948⟩,⟨169050964688,175074713470⟩,⟨20895178746,21894947132⟩,⟨610895030049,767403773490⟩,⟨91715577250,118514811712⟩,⟨-17640981861,-11969704118⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167890559718,179191920537⟩,⟨1469348561899,1895830478101⟩,⟨-6347963145,208660262478⟩,⟨-11402283384337,7160168038140⟩,⟨-5331950024100,6454240906467⟩,⟨-5091714461833,4087174568967⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-179191920537,-167890559718⟩,⟨-1895830478101,-1469348561899⟩,⟨-208660262478,6347963145⟩,⟨-7160168038140,11402283384337⟩,⟨-6454240906467,5331950024100⟩,⟨-4087174568967,5091714461833⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50540814380,67083758127⟩,⟨-396980704848,201027739821⟩,⟨-3618108500,283929439061⟩,⟨-14407262689738,11084937950601⟩,⟨-9598484530363,5864228532710⟩,⟨-5716911069235,6521255642420⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26532044914551,27894987833332⟩,⟨-254236570490303,-210028361149072⟩,⟨-97777575370518,-64847018163383⟩,⟨2249215180753365,4083277585989911⟩,⟨471587111980949,2009844434470895⟩,⟨-430104344671574,1015699327022109⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14013644232,14662905700⟩,⟨171817080426,182659529856⟩,⟨40502059984,44119903312⟩,⟨398358985127,633854603419⟩,⟨64915456262,154916468266⟩,⟨12638714849,45275525364⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338159805487,372002956377⟩,⟨755618781438,1957253181175⟩,⟨-326600359228,292840126394⟩,⟨-46191858060527,4894137420877⟩,⟨-18868290720237,12863116166970⟩,⟨-13277824873424,9916391756617⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372002956377,-338159805487⟩,⟨-1957253181175,-755618781438⟩,⟨-292840126394,326600359228⟩,⟨-4894137420877,46191858060527⟩,⟨-12863116166970,18868290720237⟩,⟨-9916391756617,13277824873424⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57136419988,107713679326⟩,⟨-1321288738232,243735848338⟩,⟨-524760468349,375433964115⟩,⟨-28678688769396,33925794332344⟩,⟨-23298801567239,18808903013037⟩,⟨-16574860810730,17241213248983⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨241059563408,243512224619⟩,⟨1540011159712,1548270629490⟩,⟨303665795562,305706711189⟩,⟨-3884154009684,-3870646001990⟩,⟨-1534094873726,-1526219312984⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1702015948762,-1613403586313⟩,⟨-5706495541541,-2768063054830⟩,⟨-440416744357,1443191541040⟩,⟨-18036653812617,105794392385997⟩,⟨-55262723193035,38545427552009⟩,⟨-40146627040298,43274850323908⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-196550309861,-182145584860⟩,⟨-1883229655776,-1429117280465⟩,⟨-346564429672,-96556412210⟩,⟨-7017567914413,12775348964063⟩,⟨-6910860496742,6266778797344⟩,⟨-4652065155187,5806464437833⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44509253547,61366639759⟩,⟨-343218496064,119153349025⟩,⟨-42898634110,209150298979⟩,⟨-10901721924097,8904702962073⟩,⟨-8444955370468,4740559484360⟩,⟨-5001165465715,5458048302175⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2626367128,6571861751⟩,⟨-119505117685,34564576890⟩,⟨-32371303053,50721251494⟩,⟨-3644313320847,4109935164016⟩,⟨-2838580315883,1974470338000⟩,⟨-1842348292579,1884679775826⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1801775989,3425033788⟩,⟨-38311856418,13300524454⟩,⟨-4788571506,23346458062⟩,⟨-1291296349014,1208264866137⟩,⟨-1073245193890,574497179890⟩,⟨-574576882465,688825696690⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3083271439,5909928273⟩,⟨-89809980399,10999950190⟩,⟨-19051016078,34828761768⟩,⟨-2362328227912,2738995367559⟩,⟨-2018745626259,1228357104307⟩,⟨-1128001993724,1244210242964⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5909928273,-3083271439⟩,⟨-10999950190,89809980399⟩,⟨-34828761768,19051016078⟩,⟨-2738995367559,2362328227912⟩,⟨-1228357104307,2018745626259⟩,⟨-1244210242964,1128001993724⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3283561145,3488590312⟩,⟨-130505067875,124374557289⟩,⟨-67200064821,69772267572⟩,⟨-6383308688406,6472263391928⟩,⟨-4066937420190,3993215964259⟩,⟨-3086558535543,3012681769550⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50540814380,67083758127⟩,⟨-396980704848,201027739821⟩,⟨-3618108500,283929439061⟩,⟨-14407262689738,11084937950601⟩,⟨-9598484530363,5864228532710⟩,⟨-5716911069235,6521255642420⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3283561145,3488590312⟩,⟨-130505067875,124374557289⟩,⟨-67200064821,69772267572⟩,⟨-6383308688406,6472263391928⟩,⟨-4066937420190,3993215964259⟩,⟨-3086558535543,3012681769550⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (521/5120) u, BivariateJet2.affineZ (647/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000053

end


