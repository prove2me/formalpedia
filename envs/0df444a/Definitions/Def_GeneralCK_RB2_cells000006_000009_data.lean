-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000006_000009_data
-- name    : GeneralCK_RB2_cells000006_000009_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T00:26:09.550819+00:00
-- url     : https://prove2.me/theorems/8cdfc056-c973-486f-812e-3564dee24022
-- title:
--   Exact certificate data for RB2 cells 000006–000009
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000006 through 000009. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000006Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2525295488000,-2525295430144⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-116561173120,-116561173056⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2130501048704,-2130501009664⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2130501048704,-2130501009664⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-171006037184,-171006037120⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-171006037184,-171006037120⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨85808313664,85808313728⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-93076184448,-93076184384⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨85808437504,85808437568⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-93076330176,-93076330112⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-7267892672,-7267892608⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-7267870784,-7267870720⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨178884498112,178884498176⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨178884767680,178884767744⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1959494972480,1959495011072⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1959494972480,1959495011072⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2137533418560,-2137533379392⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2123508163264,-2123508124288⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-172187155520,-172187155456⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-169827067392,-169827067328⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨83212124160,83212124224⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-90029137344,-90029137280⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨88427447552,88427447616⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-96166070656,-96166070592⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-7738623040,-7738622976⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-6817013120,-6817013056⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨173241261440,173241261504⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨184593518208,184593518272⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1951320968832,1951321007424⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1967706312064,1967706350656⟩



end LaneCBRB2Cell000006Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000006
open Set LaneCBRB2Cell000006Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110595407872,110595407872⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨119614839193,119614839194⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110595407872,-110595407872⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439160406016,439160406016⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨47775848857,47775848858⟩,⟨-119614839194,-119614839193⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158371256729,158371256730⟩,⟨979896788582,979896788583⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47775848857,47775848858⟩,⟨-119614839194,-119614839193⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2130501048704,-2130501009664⟩,⟨6803052115088,6803052115140⟩,⟨3048924298786,3048924298806⟩,⟨-42092795484950,-42092795484321⟩,⟨-26498223448644,-26498223448332⟩,⟨-8454607613975,-8454607613865⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-306872724239,-306872718613⟩,⟨-918829048387,-918829013576⟩,⟨-411791673011,-411791657411⟩,⟨6062954453254,6062954453490⟩,⟨3748224064528,3748224103682⟩,⟨1217783240417,1217783240458⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306872718613,306872724239⟩,⟨918829013576,918829048387⟩,⟨411791657411,411791673011⟩,⟨-6062954453490,-6062954453254⟩,⟨-3748224103682,-3748224064528⟩,⟨-1217783240458,-1217783240417⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158371256730,-158371256729⟩,⟨-979896788583,-979896788582⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941140371046,941140371047⟩,⟨-979896788583,-979896788582⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-171006037184,-171006037120⟩,⟨-1144789816922,-1144789816918⟩,⟨-513060525007,-513060525005⟩,⟨-1191932574265,-1191932574256⟩,⟨750344455020,750344455026⟩,⟨-239407292902,-239407292900⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146374700568,-146374700512⟩,⟨-827494337926,-827494337861⟩,⟨-370858190020,-370858189990⟩,⟨1020249205968,1020249205988⟩,⟨1385750742070,1385750742148⟩,⟨204923588599,204923588604⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146374700512,146374700568⟩,⟨827494337861,827494337926⟩,⟨370858189990,370858190020⟩,⟨-1020249205988,-1020249205968⟩,⟨-1385750742148,-1385750742070⟩,⟨-204923588604,-204923588599⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨453247419125,453247424807⟩,⟨1746323351437,1746323386313⟩,⟨782649847401,782649863031⟩,⟨-7083203659478,-7083203659222⟩,⟨-5133974845830,-5133974806598⟩,⟨-1422706829062,-1422706829016⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨812093385618,812093397178⟩,⟨4155057608459,4155057701259⟩,⟨782649847401,782649863031⟩,⟨-19236746185092,-19236746184826⟩,⟨-5133974845830,-5133974806598⟩,⟨-1422706829062,-1422706829016⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95551697714,95551697716⟩,⟨-239229678388,-239229678386⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12652060073362,12652060073628⟩,⟨31676551381292,31676551382890⟩,⟨-116299008218657,-116299008213764⟩,⟨158615103246977,158615103259636⟩,⟨-291174045048188,-291174044994337⟩,⟨2138064352062679,2138064352197554⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9344743648415,9344743781633⟩,⟨71208302257617,71208303660692⟩,⟨-76891886953488,-76891885547089⟩,⟨135206937106182,135206944150040⟩,⟨-691082567957108,-691082554117624⟩,⟨1397224823778138,1397224849671166⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨89245478912,89245612800⟩,⟨-673617574090,-673615512928⟩,⟨727381011492,727383236141⟩,⟨8841308881553,8841360232875⟩,⟨-4390666222900,-4390595053242⟩,⟨-1417140896603,-1417045237864⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1188757106688,1188757240576⟩,⟨-673617574090,-673615512928⟩,⟨727381011492,727383236141⟩,⟨8841308881553,8841360232875⟩,⟨-4390666222900,-4390595053242⟩,⟨-1417140896603,-1417045237864⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨85808313664,85808437568⟩,⟨-623045995873,-623044019278⟩,⟨672773088281,672775221690⟩,⟨7824496729006,7824547386278⟩,⟨-3679808266340,-3679739563974⟩,⟨-1722410995857,-1722319760240⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨92773227771,92773372182⟩,⟨-726188327788,-726185878118⟩,⟨784147348775,784149992862⟩,⟨9913008518029,9913074001635⟩,⟨-5145503886980,-5145417974587⟩,⟨-1082668359058,-1082556337972⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-89245612800,-89245478912⟩,⟨673615512928,673617574090⟩,⟨-727383236141,-727381011492⟩,⟨-8841360232875,-8841308881553⟩,⟨4390595053242,4390666222900⟩,⟨1417045237864,1417140896603⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1010266014976,1010266148864⟩,⟨673615512928,673617574090⟩,⟨-727383236141,-727381011492⟩,⟨-8841360232875,-8841308881553⟩,⟨4390595053242,4390666222900⟩,⟨1417045237864,1417140896603⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-93076330176,-93076184384⟩,⟨733121752072,733124092475⟩,⟨-791639344620,-791636818533⟩,⟨-10111221700687,-10111161416792⟩,⟨5306293951836,5306375411205⟩,⟨972251176148,972359127166⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-85521483595,-85521338302⟩,⟨616592059686,616594563199⟩,⟨-665808859446,-665806157226⟩,⟨-7643780320075,-7643712562384⟩,⟨3533911691376,3533999855097⟩,⟨1820784042939,1820898181512⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7251744176,7252033880⟩,⟨-109596268102,-109591314919⟩,⟨118338489329,118343835636⟩,⟨2269228197954,2269361439251⟩,⟨-1611592195604,-1611418119490⟩,⟨738115683881,738341843540⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3625872088,3626016940⟩,⟨-54798134051,-54795657459⟩,⟨59169244664,59171917818⟩,⟨1134614098977,1134680719626⟩,⟨-805796097802,-805709059745⟩,⟨369057841940,369170921770⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3626016940,-3625872088⟩,⟨54795657459,54798134051⟩,⟨-59171917818,-59169244664⟩,⟨-1134680719626,-1134614098977⟩,⟨805709059745,805796097802⟩,⟨-369170921770,-369057841940⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758497366676,758497530792⟩,⟨54795657459,54798134051⟩,⟨-59171917818,-59169244664⟩,⟨-1134680719626,-1134614098977⟩,⟨805709059745,805796097802⟩,⟨-369170921770,-369057841940⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7243902933,7243924669⟩,⟨-109352937566,-109352438910⟩,⟨118080546092,118081084384⟩,⟨2260648588344,2260664128866⟩,⟨-1604031838046,-1604013762306⟩,⟨732342465448,732364226363⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7243924669,-7243902933⟩,⟨109352438910,109352937566⟩,⟨-118081084384,-118080546092⟩,⟨-2260664128866,-2260648588344⟩,⟨1604013762306,1604031838046⟩,⟨-732364226363,-732342465448⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092267703107,1092267724843⟩,⟨109352438910,109352937566⟩,⟨-118081084384,-118080546092⟩,⟨-2260664128866,-2260648588344⟩,⟨1604013762306,1604031838046⟩,⟨-732364226363,-732342465448⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7267892672,-7267870720⟩,⟨110077662621,110078166775⟩,⟨-118864198705,-118863654477⟩,⟨-2286677396009,-2286661606187⟩,⟨1626551597995,1626569934736⟩,⟨-750071245173,-750049207599⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3633946336,-3633935360⟩,⟨55038831310,55039083388⟩,⟨-59432099353,-59431827238⟩,⟨-1143338698005,-1143330803093⟩,⟨813275798997,813284967368⟩,⟨-375035622587,-375024603799⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3633935360,3633946336⟩,⟨-55039083388,-55038831310⟩,⟨59431827238,59432099353⟩,⟨1143330803093,1143338698005⟩,⟨-813284967368,-813275798997⟩,⟨375024603799,375035622587⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765757318976,765757349216⟩,⟨-55039083388,-55038831310⟩,⟨59431827238,59432099353⟩,⟨1143330803093,1143338698005⟩,⟨-813284967368,-813275798997⟩,⟨375024603799,375035622587⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273066925776,273066931211⟩,⟨27338109727,27338234392⟩,⟨-29520271096,-29520136523⟩,⟨-565166032217,-565162147086⟩,⟨401003440576,401007959512⟩,⟨-183091056591,-183085616362⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531514637952,1531514698432⟩,⟨-110078166776,-110077662620⟩,⟨118863654476,118864198706⟩,⟨2286661606186,2286677396010⟩,⟨-1626569934736,-1626551597994⟩,⟨750049207598,750071245174⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1196640925734,1196641084323⟩,⟨-797887340889,-797884687995⟩,⟨861568892446,861571755867⟩,⟨11536372929589,11536443464527⟩,⟨-6349606189825,-6349513025906⟩,⟨-437935626644,-437813793653⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1293770223692,1293770540870⟩,⟨-1595774681778,-1595769375990⟩,⟨1723137784892,1723143511734⟩,⟨23072745859186,23072886929045⟩,⟨-12699212379646,-12699026051815⟩,⟨-875871102213,-875627738381⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨178884498112,178884767744⟩,⟨-1356170350652,-1356165509046⟩,⟨1464409623574,1464414849550⟩,⟨17935645296855,17935781935907⟩,⟨-8986195542165,-8986021651204⟩,⟨-2694780992766,-2694560066691⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨61565934395,61566040079⟩,⟨-460247067126,-460245336993⟩,⟨496980417410,496982284837⟩,⟨5939926501217,5939972031251⟩,⟨-2891000763940,-2890940351488⟩,⟨-1085869442379,-1085790240991⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380356135762,380356158354⟩,⟨10741139727,10741440631⟩,⟨-11598782632,-11598457811⟩,⟨-224797182231,-224787756740⟩,⟨160506891814,160517824364⟩,⟨-75134102883,-75120979966⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178404747924,3178404936712⟩,⟨-89759687617,-89757162481⟩,⟨96921247534,96923973380⟩,⟨1883483798040,1883563069222⟩,⟨-1346824208776,-1346732385133⟩,⟨633651245286,633761312235⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨177971249460,177971565537⟩,⟨-1335481737248,-1335476506833⟩,⟨1442069301890,1442074947422⟩,⟨17351403280116,17351542931844⟩,⟨-8513695941005,-8513512949423⟩,⟨-3015871280855,-3015633126209⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨356855747572,356856333281⟩,⟨-2691652087900,-2691642015879⟩,⟨2906478925464,2906489796972⟩,⟨35287048576971,35287324867751⟩,⟨-17499891483170,-17499534600627⟩,⟨-5710652273621,-5710193192900⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523248904987,523249131418⟩,⟨75601495860,75604929170⟩,⟨-81639434134,-81635728320⟩,⟨-1560056189188,-1559963440325⟩,⟨1105737627654,1105858487504⟩,⟨-502976459919,-502819758191⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360962909825,360963144131⟩,⟨78230462613,78234032241⟩,⟨-84478382460,-84474529499⟩,⟨-1608654384688,-1608557548371⟩,⟨1138085358204,1138211222173⟩,⟨-513877347014,-513714485710⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721925819650,721926288262⟩,⟨156460925226,156468064482⟩,⟨-168956764920,-168949058998⟩,⟨-3217308769376,-3217115096742⟩,⟨2276170716408,2276422444346⟩,⟨-1027754694028,-1027428971420⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524270713283,1524270795499⟩,⟨-725727866,-724725054⟩,⟨782570092,783652614⟩,⟨25997477320,26028807666⟩,⟨-22556172430,-22519759948⟩,⟨17684981235,17728779726⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000817414074,1000818117701⟩,⟨216427801269,216438368980⟩,⟨-233713676530,-233702269946⟩,⟨-4443344235924,-4443054626809⟩,⟨3140904801391,3141278182029⟩,⟨-1413422093986,-1412941353857⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67816968978,67816971679⟩,⟨13578998876,13579061070⟩,⟨-14662891476,-14662824338⟩,⟨-279361814681,-279359866926⟩,⟨197712769754,197715031690⟩,⟨-89357262361,-89354543902⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50089249216,50089251925⟩,⟨266309896782,266309958794⟩,⟨37443263017,37443315648⟩,⟨-1290211649728,-1290209688560⟩,⟨-216375113182,-216373125998⟩,⟨-174624739429,-174622631153⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133253552766,2133253721253⟩,⟨-306656748570,-306655331976⟩,⟨331131426264,331132955464⟩,⟨6392243110392,6392287551286⟩,⟨-4555113475664,-4555061996082⟩,⟨2115193472445,2115255182781⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2971418364290,2971418716319⟩,⟨-640715349357,-640712364284⟩,⟨691851655223,691854877589⟩,⟨13401727021691,13401820825646⟩,⟨-9566984430926,-9566876038481⟩,⟨4473089470485,4473219073744⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135365658001,135365681360⟩,⟨690511265333,690511655751⟩,⟨132707945637,132708248363⟩,⟨-3186627833088,-3186616295334⟩,⟨-874831783726,-874820430790⟩,⟨-221024637386,-221012682957⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8930814719570,8930816260693⟩,⟨-45556848128601,-45556806647792⟩,⟨-8755492345036,-8755469350807⟩,⟨675016408913658,675018008866078⟩,⟨147041402372615,147042471817318⟩,⟨31748549412616,31749430353156⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8129168139215,8129175257237⟩,⟨-39709668634860,-39709515583661⟩,⟨-9867934996696,-9867815485549⟩,⟨560398790242097,560403929189698⟩,⟨167314410245768,167319085103663⟩,⟨21140144078337,21145064506334⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16258336278430,16258350514474⟩,⟨-79419337269720,-79419031167322⟩,⟨-19735869993392,-19735630971098⟩,⟨1120797580484194,1120807858379396⟩,⟨334628820491536,334638170207326⟩,⟨42280288156674,42290129012668⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10931067056724,10931067056725⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603222,2160817149603840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9831555428948,9831555428949⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603232,2160817149603830⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2408734257088,2408734314944⟩,⟨-12153542525660,-12153542525558⟩,⟨0,0⟩,⟨107314718406763,107314718418708⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7633492620922,7633492620971⟩,⟨-47231013123561,-47231013122905⟩,⟨-21167526153325,-21167526153052⟩,⟨584468659733010,584468659745467⟩,⟨314937803275009,314937803281006⟩,⟨117394274335739,117394274338003⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6533980993146,6533980993195⟩,⟨-47231013123562,-47231013122904⟩,⟨-21167526153325,-21167526153052⟩,⟨584468659733011,584468659745462⟩,⟨314937803275008,314937803281005⟩,⟨117394274335737,117394274338003⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1959494972480,1959495011072⟩,⟨-7947841932127,-7947841931929⟩,⟨-3561984823842,-3561984823756⟩,⟨40900862906231,40900862914745⟩,⟨27248567901577,27248567905533⟩,⟨8215200320224,8215200321875⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99471065088,99471065088⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135559806331,135559806333⟩,⟨697612396214,697612396219⟩,⟨312648991948,312648991950⟩,⟨-1746589471214,-1746589471210⟩,⟨-1565538228636,-1565538228632⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4368229229568,4368229326016⟩,⟨-20101384457787,-20101384457487⟩,⟨-3561984823842,-3561984823756⟩,⟨148215581312994,148215581333453⟩,⟨27248567901577,27248567905533⟩,⟨8215200320224,8215200321875⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨713711495144,713712666562⟩,⟨-5383304175800,-5383284031758⟩,⟨5812957850928,5812979593944⟩,⟨70574097153942,70574649735502⟩,⟨-34999782966340,-34999069201254⟩,⟨-11421304547242,-11420386385800⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5081940724712,5081941992578⟩,⟨-25484688633587,-25484668489245⟩,⟨2250973027086,2250994770188⟩,⟨218789678466936,218790231068955⟩,⟨-7751215064763,-7750501295721⟩,⟨-3206104227018,-3205186063925⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459755080192,459755194895⟩,⟨1754038005135,1754040840371⟩,⟨203641943233,203643910298⟩,⟨-31086102451581,-31086017739089⟩,⟨1096900485930,1096982428482⟩,⟨-290051141060,-289968076307⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35832726202,35832728212⟩,⟨-720897882327,-720897872251⟩,⟨329378021832,329378040293⟩,⟨8997886724610,8997886750387⟩,⟨-6626565812353,-6626565719884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨495587806394,495587923107⟩,⟨1033140122808,1033142968120⟩,⟨533019965065,533021950591⟩,⟨-22088215726971,-22088130988702⟩,⟨-5529665326423,-5529583291402⟩,⟨-290051141060,-289968076307⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501892554988,501892567044⟩,⟨2532355881864,2532356003553⟩,⟨0,0⟩,⟨3194096148032,3194099067279⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226220281885,226220340596⟩,⟨1613016167901,1613017801686⟩,⟨243306887683,243307799859⟩,⟨-3883905497471,-3883851584926⟩,⟨-1296486227048,-1296444088016⟩,⟨-132399247160,-132361327525⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-713712666562,-713711495144⟩,⟨5383284031758,5383304175800⟩,⟨-5812979593944,-5812957850928⟩,⟨-70574649735502,-70574097153942⟩,⟨34999069201254,34999782966340⟩,⟨11420386385800,11421304547242⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3654516563006,3654517830872⟩,⟨-14718100426029,-14718080281687⟩,⟨-9374964417786,-9374942674684⟩,⟨77640931577492,77641484179511⟩,⟨62247637102831,62248350871873⟩,⟨19635586706024,19636504869117⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450568729788,450568886112⟩,⟨504090360827,504093648916⟩,⟨-116676748234,-116673706960⟩,⟨-14909356950513,-14909261243230⟩,⟨-7662220373111,-7662111042870⟩,⟨-4076723490427,-4076597519233⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨316742513458,316742513460⟩,⟨1959793577164,1959793577166⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-316742513460,-316742513458⟩,⟨-1959793577166,-1959793577164⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨782769114316,782769114318⟩,⟨-1959793577166,-1959793577164⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1395012208481,1395012235960⟩,⟨-9150909069958,-9150909001010⟩,⟨-4101163499464,-4101163468567⟩,⟨57451135374220,57451135381093⟩,⟨36015828605217,36015828685587⟩,⟨11539428564249,11539428565580⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1395012235960,-1395012208481⟩,⟨9150909001010,9150909069958⟩,⟨4101163468567,4101163499464⟩,⟨-57451135381093,-57451135374220⟩,⟨-36015828685587,-36015828605217⟩,⟨-11539428565580,-11539428564249⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-295500608184,-295500580705⟩,⟨9150909001010,9150909069958⟩,⟨4101163468567,4101163499464⟩,⟨-57451135381093,-57451135374220⟩,⟨-36015828685587,-36015828605217⟩,⟨-11539428565580,-11539428564249⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12840057384,-12840056188⟩,⟨429771443830,429771449826⟩,⟨60176170285,60176182608⟩,⟨-4487397558889,-4487397543518⟩,⟨1939385071203,1939385133114⟩,⟨2774714842353,2774714867105⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437728672404,437728829924⟩,⟨933861804657,933865098742⟩,⟨-56500577949,-56497524352⟩,⟨-19396754509402,-19396658786748⟩,⟨-5722835301908,-5722725909756⟩,⟨-1302008648074,-1301882652128⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99471065088,-99471065088⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4322204923,4322204924⟩,⟨27343327845,27343327848⟩,⟨39730142208,39730142208⟩,⟨-286655093148,-286655093143⟩,⟨251342618624,251342618624⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9468788506,9468788737⟩,⟨12126028317,12126029776⟩,⟨87038055949,87038058040⟩,⟨-810611118869,-810611103554⟩,⟨111463671483,111463684713⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1488653674337,1488653695529⟩,⟨-7616663442483,-7616663055508⟩,⟨-1434680581742,-1434680512241⟩,⟨113203974776090,113203982590793⟩,⟨24092143691801,24092145279748⟩,⟨5373301558205,5373301861098⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12820007033,12820007529⟩,⟨-49175578542,-49175571398⟩,⟨105487592428,105487597839⟩,⟨-290614951105,-290614794910⟩,⟨-260372286768,-260372200177⟩,⟨-180866634267,-180866614066⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12820007529,-12820007033⟩,⟨49175571398,49175578542⟩,⟨-105487597839,-105487592428⟩,⟨290614794910,290614951105⟩,⟨260372200177,260372286768⟩,⟨180866614066,180866634267⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112291072617,-112291072121⟩,⟨-829145240634,-829145233490⟩,⟨-105487597839,-105487592428⟩,⟨2489638050462,2489638206657⟩,⟨260372200177,260372286768⟩,⟨180866614066,180866634267⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨85143743164,85143744843⟩,⟨-558520310322,-558520306104⟩,⟨627874905259,627874920682⟩,⟨3506495989828,3506495990295⟩,⟨-3562468314677,-3562468275794⟩,⟨-2488447748051,-2488447747901⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨115278040637,115278044552⟩,⟨-1346010842728,-1346010784652⟩,⟨738995556598,738995597155⟩,⟨21251880985155,21251882282978⟩,⟨-6578375253447,-6578374603747⟩,⟨-4591614780460,-4591614581006⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-115278044552,-115278040637⟩,⟨1346010784652,1346010842728⟩,⟨-738995597155,-738995556598⟩,⟨-21251882282978,-21251880985155⟩,⟨6578374603747,6578375253447⟩,⟨4591614581006,4591614780460⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨984233583224,984233587139⟩,⟨1346010784652,1346010842728⟩,⟨-738995597155,-738995556598⟩,⟨-21251882282978,-21251880985155⟩,⟨6578374603747,6578375253447⟩,⟨4591614581006,4591614780460⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121347069513,121347069998⟩,⟨790422300009,790422309662⟩,⟨188757928848,188757934967⟩,⟨-2475613154623,-2475612914642⟩,⟨-676478242597,-676478114649⟩,⟨-168198934265,-168198885344⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11468077789,11468077892⟩,⟨169358112930,169358115138⟩,⟨21546502192,21546503394⟩,⟨741997925733,741997981435⟩,⟨105914388936,105914416392⟩,⟨-16702099324,-16702092954⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨169576983499,169577133507⟩,⟨1675920435041,1675925860611⟩,⟨112757137604,112759929243⟩,⟨-1804049041165,-1803836688294⟩,⟨460115491625,460257760943⟩,⟨-579487215154,-579374847963⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-169577133507,-169576983499⟩,⟨-1675925860611,-1675920435041⟩,⟨-112759929243,-112757137604⟩,⟨1803836688294,1804049041165⟩,⟨-460257760943,-460115491625⟩,⟨579374847963,579487215154⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56643148378,56643357097⟩,⟨-62909692710,-62902633355⟩,⟨130546958440,130550662255⟩,⟨-2080068809177,-2079802543761⟩,⟨-1756743987991,-1756559579641⟩,⟨446975600803,447125887629⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28974798804913,28974824746340⟩,⟨-259061012119506,-259060360903011⟩,⟨-87842942397836,-87842469611019⟩,⟨3750389641521567,3750412952672496⟩,⟨1399225703216983,1399245449862011⟩,⟨324698282830900,324717477270625⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13392410691,13392410799⟩,⟨174469150412,174469153242⟩,⟨41664355218,41664356736⟩,⟨590005601386,590005684302⟩,⟨122072058016,122072098970⟩,⟨27683395914,27683411067⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352922511669,352922830491⟩,⟨1442237621215,1442249769624⟩,⟨28001103957,28007894301⟩,⟨-20985916235580,-20985407822328⟩,⟨-3495620709304,-3495275810049⟩,⟨-1972899368802,-1972628416231⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352922830491,-352922511669⟩,⟨-1442249769624,-1442237621215⟩,⟨-28007894301,-28001103957⟩,⟨20985407822328,20985916235580⟩,⟨3495275810049,3495620709304⟩,⟨1972628416231,1972899368802⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84805841913,84806318255⟩,⟨-508387964967,-508372522473⟩,⟨-84508472250,-84498628309⟩,⟨1588653312926,1589257448832⟩,⟨-2227559491859,-2227105200452⟩,⟨670619768157,671016716674⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235030871419,235030871421⟩,⟨1575933208246,1575933208251⟩,⟨312648991948,312648991950⟩,⟨-3945612726766,-3945612726762⟩,⟨-1565538228636,-1565538228632⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1660435026000,-1660433564764⟩,⟨-4149556655690,-4149514517110⟩,⟨455730351069,455756216699⟩,⟨42128229599763,42129777009772⟩,⟨-7823685830527,-7822516024779⟩,⟨2142328119096,2143381864991⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-183253110051,-183252948049⟩,⟨-1651625489334,-1651619771860⟩,⟨-234757630156,-234754515208⟩,⟨2421914969825,2422150078472⟩,⟨-226624886464,-226468830094⟩,⟨646917895510,647043376029⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51777761368,51777923372⟩,⟨-75692281088,-75686563609⟩,⟨77891361792,77894476742⟩,⟨-1523697756941,-1523462648290⟩,⟨-1792163115100,-1792007058726⟩,⟨296104211798,296229692317⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4368912311,4368952950⟩,⟨-31042819015,-31041355215⟩,⟨5715538598,5716404004⟩,⟨-20427897945,-20366739804⟩,⟨-305785430797,-305741967972⟩,⟨48955265024,48990534189⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2438297608,2438312867⟩,⟨-7128963500,-7128402702⟩,⟨7336057648,7336373980⟩,⟨-133087177876,-133063011234⟩,⟨-179516964770,-179500499806⟩,⟨38923967548,38936755695⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4345412802,4345440083⟩,⟨-30330278297,-30329168318⟩,⟨5174783519,5175396962⟩,⟨-43423232539,-43371484154⟩,⟨-289437191388,-289403360500⟩,⟨40052615486,40077570854⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4345440083,-4345412802⟩,⟨30329168318,30330278297⟩,⟨-5175396962,-5174783519⟩,⟨43371484154,43423232539⟩,⟨289403360500,289437191388⟩,⟨-40077570854,-40052615486⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨23472228,23540148⟩,⟨-713650697,-711076918⟩,⟨540141636,541620485⟩,⟨22943586209,23056492735⟩,⟨-16382070297,-16304776584⟩,⟨8877694170,8937918703⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56643148378,56643357097⟩,⟨-62909692710,-62902633355⟩,⟨130546958440,130550662255⟩,⟨-2080068809177,-2079802543761⟩,⟨-1756743987991,-1756559579641⟩,⟨446975600803,447125887629⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨23472228,23540148⟩,⟨-713650697,-711076918⟩,⟨540141636,541620485⟩,⟨22943586209,23056492735⟩,⟨-16382070297,-16304776584⟩,⟨8877694170,8937918703⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110380659507,110810156237⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨117682103910,121547574477⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110810156237,-110380659507⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438945657651,439375154381⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46980902420,48571550270⟩,⟨-121547574477,-117682103910⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157361561927,159381706507⟩,⟨977964053299,981829523866⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46551405690,49001047000⟩,⟨-121547574477,-117682103910⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2137533418560,-2123508124288⟩,⟨6746588875944,6860207567623⟩,⟨3028113232856,3069987900997⟩,⟨-42803046991015,-41396980542243⟩,⟨-26837116555082,-26165560666044⟩,⟨-8571829050439,-8339584156599⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309850041928,-303915435508⟩,⟨-943182072111,-894327079842⟩,⟨-420796320906,-402728582708⟩,⟨5796955641009,6327186513130⟩,⟨3620014669795,3875537796907⟩,⟨1175214098957,1260034721048⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨303915435508,309850041928⟩,⟨894327079842,943182072111⟩,⟨402728582708,420796320906⟩,⟨-6327186513130,-5796955641009⟩,⟨-3875537796907,-3620014669795⟩,⟨-1260034721048,-1175214098957⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159381706507,-157361561927⟩,⟨-981829523866,-977964053299⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940129921269,942150065849⟩,⟨-981829523866,-977964053299⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-172187155520,-169827067328⟩,⟨-1148280629690,-1141307406458⟩,⟨-513863116436,-512260065612⟩,⟨-1199212787944,-1184691969716⟩,⟨746500737282,754180938454⟩,⟨-240156898539,-238660845590⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147543814739,-145209476101⟩,⟨-832886056517,-822109367851⟩,⟨-372521131097,-369196875102⟩,⟨1002696833376,1037794645172⟩,⟨1377365842870,1394143276662⟩,⟨203221884479,206623708670⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145209476101,147543814739⟩,⟨822109367851,832886056517⟩,⟨369196875102,372521131097⟩,⟨-1037794645172,-1002696833376⟩,⟨-1394143276662,-1377365842870⟩,⟨-206623708670,-203221884479⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨449124911609,457393856667⟩,⟨1716436447693,1776068128628⟩,⟨771925457810,793317452003⟩,⟨-7364981158302,-6799652474385⟩,⟨-5269681073569,-4997380512665⟩,⟨-1466658429718,-1378435983436⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨807026088511,817186009505⟩,⟨4118043329017,4191917538106⟩,⟨771925457810,793317452003⟩,⟨-19625854786960,-18845616262985⟩,⟨-5269681073569,-4997380512665⟩,⟨-1466658429718,-1378435983436⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨93102811380,98002094000⟩,⟨-243095148954,-235364207820⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12335714169685,12984847629149⟩,⟨29625750582857,33903954367927⟩,⟨-122557403951758,-110501887210838⟩,⟨142299843450427,177049150611829⟩,⟨-363209192855433,-224075014445274⟩,⟨1979726006811116,2313514596763663⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9054240904652,9650680856880⟩,⟨67946311043867,74703391585564⟩,⟨-82427453947079,-71738031304486⟩,⟨94588541437366,178673067380350⟩,⟨-778633999914790,-609939525768452⟩,⟨1258915603568455,1548841582207208⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨86441872384,92080578816⟩,⟨-752511752810,-602822908706⟩,⟨636463231505,830318765091⟩,⟨6556414140916,11414971375923⟩,⟨-8109789579060,-979128418867⟩,⟨-6287084934528,3750086629233⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1185953500160,1191592206592⟩,⟨-752511752810,-602822908706⟩,⟨636463231505,830318765091⟩,⟨6556414140916,11414971375923⟩,⟨-8109789579060,-979128418867⟩,⟨-6287084934528,3750086629233⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨83212124160,88427447616⟩,⟨-697662616740,-556239621193⟩,⟨587280379831,769798425365⟩,⟨5607084436743,10301556091564⟩,⟨-7221579220234,-415013185137⟩,⟨-6367788507082,3163066892775⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨89754130297,95832963260⟩,⟨-816609854647,-645592536244⟩,⟨681619603236,901044380424⟩,⟨7154033058900,13037287658379⟩,⟨-9532295949668,-1165711936369⟩,⟨-6726798615345,4892219843131⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-92080578816,-86441872384⟩,⟨602822908706,752511752810⟩,⟨-830318765091,-636463231505⟩,⟨-11414971375923,-6556414140916⟩,⟨979128418867,8109789579060⟩,⟨-3750086629233,6287084934528⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1007431048960,1013069755392⟩,⟨602822908706,752511752810⟩,⟨-830318765091,-636463231505⟩,⟨-11414971375923,-6556414140916⟩,⟨979128418867,8109789579060⟩,⟨-3750086629233,6287084934528⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-96166070656,-90029137280⟩,⟨654259782294,821292358527⟩,⟨-906211038385,-690770521937⟩,⟨-13071788808218,-7505165689716⟩,⟨1473714291601,9527939810686⟩,⟨-4839743513314,6427755063960⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-88605645648,-82489485254⟩,⟨533651037020,707363890211⟩,⟨-782851893153,-560298920821⟩,⟨-10789844974804,-4754055857997⟩,⟨-599438841922,7941246600241⟩,⟨-4209416105357,7619094873668⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1148484649,13343478006⟩,⟨-282958817627,61771353967⟩,⟨-101232289917,340745459603⟩,⟨-3635811915904,8283231800382⟩,⟨-10131734791590,6775534663872⟩,⟨-10936214720702,12511314716799⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨574242324,6671739003⟩,⟨-141479408814,30885676984⟩,⟨-50616144959,170372729802⟩,⟨-1817905957952,4141615900191⟩,⟨-5065867395795,3387767331936⟩,⟨-5468107360351,6255657358400⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6671739003,-574242324⟩,⟨-30885676984,141479408814⟩,⟨-170372729802,50616144959⟩,⟨-4141615900191,1817905957952⟩,⟨-3387767331936,5065867395795⟩,⟨-6255657358400,5468107360351⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755451644613,761549160556⟩,⟨-30885676984,141479408814⟩,⟨-170372729802,50616144959⟩,⟨-4141615900191,1817905957952⟩,⟨-3387767331936,5065867395795⟩,⟨-6255657358400,5468107360351⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6795923856,7711453687⟩,⟨-126040900368,-94785975204⟩,⟨100075473592,139073076738⟩,⟨1691922395778,2941980909930⟩,⟨-2494887208426,-851855130040⟩,⟨-316200339112,1882180002381⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7711453687,-6795923856⟩,⟨94785975204,126040900368⟩,⟨-139073076738,-100075473592⟩,⟨-2941980909930,-1691922395778⟩,⟨851855130040,2494887208426⟩,⟨-1882180002381,316200339112⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091800174089,1092715703920⟩,⟨94785975204,126040900368⟩,⟨-139073076738,-100075473592⟩,⟨-2941980909930,-1691922395778⟩,⟨851855130040,2494887208426⟩,⟨-1882180002381,316200339112⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7738623040,-6817013056⟩,⟨95375477366,126931135220⟩,⟨-140055358676,-100697872717⟩,⟨-2977413642975,-1710718166105⟩,⟨865887955422,2528677192665⟩,⟨-1913314155290,309211349835⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3869311520,-3408506528⟩,⟨47687738683,63465567610⟩,⟨-70027679338,-50348936358⟩,⟨-1488706821488,-855359083052⟩,⟨432943977711,1264338596333⟩,⟨-956657077645,154605674918⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3408506528,3869311520⟩,⟨-63465567610,-47687738683⟩,⟨50348936358,70027679338⟩,⟨855359083052,1488706821488⟩,⟨-1264338596333,-432943977711⟩,⟨-154605674918,956657077645⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765531890144,765992714400⟩,⟨-63465567610,-47687738683⟩,⟨50348936358,70027679338⟩,⟨855359083052,1488706821488⟩,⟨-1264338596333,-432943977711⟩,⟨-154605674918,956657077645⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272950043522,273178925980⟩,⟨23696493801,31510225092⟩,⟨-34768269185,-25018868398⟩,⟨-735495227483,-422980598944⟩,⟨212963782510,623721802107⟩,⟨-470545000596,79050084778⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531063780288,1531985428800⟩,⟨-126931135220,-95375477366⟩,⟨100697872716,140055358676⟩,⟨1710718166104,2977413642976⟩,⟨-2528677192666,-865887955422⟩,⟨-309211349836,1913314155290⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1193329297592,1200008497716⟩,⟨-896359605887,-710085593207⟩,⟨749711672816,989039969487⟩,⟨8568089966903,14936113934735⟩,⟨-11137580902663,-2045574216288⟩,⟨-6546889017698,6097263649734⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1287146967408,1300505367656⟩,⟨-1792719211774,-1420171186414⟩,⟨1499423345632,1978079938974⟩,⟨17136179933813,29872227869457⟩,⟨-22275161805319,-4091148432576⟩,⟨-13088947025839,12194527299464⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨173241261440,184593518272⟩,⟨-1531383492792,-1200683035786⟩,⟨1267686735081,1689723045345⟩,⟨12354886730795,24206405544426⟩,⟨-17643641547566,-1105438239592⟩,⟨-13777647120130,8955271001867⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59392418421,63777304150⟩,⟨-523794974175,-402338675428⟩,⟨423032520667,579338413877⟩,⟨3964270600016,8100814167661⟩,⟨-5958722999072,-25043557581⟩,⟨-5135803943540,3131787603004⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380081406060,380629111584⟩,⟨1460586813,20227585084⟩,⟨-23445857583,-41209901⟩,⟨-607384782460,146643521988⟩,⟨-327370628562,662125702631⟩,⟨-741308280141,580932456051⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176125479692,3180702345181⟩,⟨-169274072050,-12187735648⟩,⟨343872322,196206110086⟩,⟨-1227089343481,5100902550024⟩,⟨-5561867255358,2739590799086⟩,⟨-4861519578680,6227827482310⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨171565055504,184497021910⟩,⟨-1525069589417,-1162881724291⟩,⟨1222019628619,1687309621441⟩,⟨11389208889940,23891452884277⟩,⟨-17742862713748,81752725819⟩,⟨-15138746059219,9627745106844⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨344806316944,369090540182⟩,⟨-3056453082209,-2363564760077⟩,⟨2489706363700,3377032666786⟩,⟨23744095620735,48097858428703⟩,⟨-35386504261314,-1023685513773⟩,⟨-28916393179349,18583016108711⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519055163157,527467931483⟩,⟨-42784379514,195984330310⟩,⟨-236008798970,70116007382⟩,⟨-5745121233225,2554663623172⟩,⟨-4736749544258,7030518108916⟩,⟨-8681334694857,7627494482525⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356632041668,365337437362⟩,⟨-44450291586,203615448613⟩,⟨-245198365619,72846141708⟩,⟨-5977079164738,2691962915725⟩,⟨-4966738776442,7317801376389⟩,⟨-9035660248118,7979344650703⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713264083336,730674874724⟩,⟨-88900583172,407230897226⟩,⟨-490396731238,145692283416⟩,⟨-11954158329476,5383925831450⟩,⟨-9933477552884,14635602752778⟩,⟨-18071320496236,15958689301406⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523352326601,1525189504944⟩,⟨-32145160016,30665423002⟩,⟨-38375204022,39979885084⟩,⟨-1231262743826,1285491247198⟩,⟨-1676822062626,1628999253004⟩,⟨-2191391352217,2229514494402⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988213742703,1013556948652⟩,⟨-144680504678,585269612792⟩,⟨-705756742842,228665739217⟩,⟨-17424272828397,8345304327101⟩,⟨-14921454979930,21413490201715⟩,⟨-26559605405976,23652968419162⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67758925305,67872611544⟩,⟨11765148908,15657732454⟩,⟨-17276685748,-12421698952⟩,⟨-364453212551,-208200942516⟩,⟨103742272978,308854928428⟩,⟨-232679729585,41479597351⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49734099275,50444713072⟩,⟨262415571739,270403389178⟩,⟨34730486324,39853959729⟩,⟨-1394242007010,-1194812694294⟩,⟨-306758847477,-113647500700⟩,⟨-288401088451,-71560903509⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131997734349,2134565287684⟩,⟨-353714585106,-265619635542⟩,⟨280442446942,390287402692⟩,⟨4780877323510,8326361839205⟩,⟨-7078913766190,-2428958021508⟩,⟨-843223862466,5367446483643⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2968794897895,2974159467662⟩,⟨-739263110067,-554810781038⟩,⟨585771803754,815700260276⟩,⟨10020578485040,17463338380927⟩,⟨-14862506347465,-5109955485959⟩,⟨-1723818576266,11292529477454⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134287202107,136452054882⟩,⟨674632333388,706340675196⟩,⟨120272055609,145227929565⟩,⟨-3681754716223,-2689742098918⟩,⟨-1398649617996,-354917471646⟩,⟨-822201474814,384003701375⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8859711351801,9002539338421⟩,⟨-47352685996934,-43803281288643⟩,⟨-9735999621951,-7809158295966⟩,⟨607778009723157,744965987051779⟩,⟨100262965847851,196185957311407⟩,⟨-11977042387680,76178363204365⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7962888516186,8298762897512⟩,⟨-44835483881248,-34577253092883⟩,⟨-14753452805683,-5146416910398⟩,⟨353178351127919,767519308462706⟩,⟨-47089876156473,387853574418495⟩,⟨-232554053689193,276386693066939⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15925777032372,16597525795024⟩,⟨-89670967762496,-69154506185766⟩,⟨-29506905611366,-10292833820796⟩,⟨706356702255838,1535038616925412⟩,⟨-94179752312946,775707148836990⟩,⟨-465108107378386,552773386133878⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10909882818222,10952333724170⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145760,2173453475298114⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9810371190446,9852822096394⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145775,2173453475298112⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2406362562496,2411110103296⟩,⟨-12227224809080,-12080350374972⟩,⟨0,0⟩,⟨103760055435140,110865974497594⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7585097726140,7682472166713⟩,⟨-47933420952298,-46542059810349⟩,⟨-21450520399914,-20889760705386⟩,⟨571162932792569,598144137546073⟩,⟨308685195620719,321352148008528⟩,⟨115063013842114,119785614693344⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6485586098364,6582960538937⟩,⟨-47933420952299,-46542059810349⟩,⟨-21450520399915,-20889760705386⟩,⟨571162932792572,598144137546072⟩,⟨308685195620719,321352148008529⟩,⟨115063013842114,119785614693345⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1951320968832,1967706350656⟩,⟨-8126228361926,-7773635530593⟩,⟨-3636540513671,-3489088938192⟩,⟨35338833732458,46444090227883⟩,⟨24680995719458,29811196800400⟩,⟨7190725101111,9235490450303⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99256358666,99685855397⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134550930693,136571075274⟩,⟨693878613145,701344833604⟩,⟨311627067882,313670312921⟩,⟨-1753486165281,-1739706366688⟩,⟨-1569485068700,-1561591388566⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4357683531328,4378816453952⟩,⟨-20353453171006,-19853985905565⟩,⟨-3636540513671,-3489088938192⟩,⟨139098889167598,157310064725477⟩,⟨24680995719458,29811196800400⟩,⟨7190725101111,9235490450303⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨689612633888,738181080364⟩,⟨-6112906164418,-4727129520154⟩,⟨4979412727400,6754065333572⟩,⟨47488191241470,96195716857406⟩,⟨-70773008522628,-2047371027546⟩,⟨-57832786358698,37166032217422⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5047296165216,5116997534316⟩,⟨-26466359335424,-24581115425719⟩,⟨1342872213729,3264976395380⟩,⟨186587080409068,253505781582883⟩,⟨-46092012803170,27763825772854⟩,⟨-50642061257587,46401522667725⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨455635234600,463926222686⟩,⟨1630410951841,1870586087634⟩,⟨121225281044,296015027584⟩,⟨-35695016119153,-26363774363874⟩,⟨-3106675530273,5126603115789⟩,⟨-4591399552310,4206936390670⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34794361908,36878202413⟩,⟨-741895700491,-700092275372⟩,⟨328085346598,330673870673⟩,⟨8648339141662,9355264001325⟩,⟨-6659570832821,-6593775017748⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨490429596508,500804425099⟩,⟨888515251350,1170493812262⟩,⟨449310627642,626688898257⟩,⟨-27046676977491,-17008510362549⟩,⟨-9766246363094,-1467171901959⟩,⟨-4591399552310,4206936390670⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501398014948,502387228948⟩,⟨2512147284185,2552733193796⟩,⟨0,0⟩,⟨2027158573049,4364694834823⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨223645134757,228826818212⟩,⟨1525705704106,1697536592832⟩,⟨204894110351,286345765752⟩,⟨-7393795555495,-333109737883⟩,⟨-3435800840264,785923906310⟩,⟨-2097895501791,1922227161840⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-738181080364,-689612633888⟩,⟨4727129520154,6112906164418⟩,⟨-6754065333572,-4979412727400⟩,⟨-96195716857406,-47488191241470⟩,⟨2047371027546,70773008522628⟩,⟨-37166032217422,57832786358698⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3619502450964,3689203820064⟩,⟨-15626323650852,-13741079741147⟩,⟨-10390605847243,-8468501665592⟩,⟨42903172310192,109821873484007⟩,⟨26728366747004,100584205323028⟩,⟨-29975307116311,67068276809001⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442930671327,458238475959⟩,⟨343235585544,671688186609⟩,⟨-264773259298,16142563245⟩,⟨-20568394408534,-9429334400621⟩,⟨-13081021504710,-1885833046047⟩,⟨-10829988546113,2376535605384⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨314723123854,318763413014⟩,⟨1955928106598,1963659047732⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-318763413014,-314723123854⟩,⟨-1963659047732,-1955928106598⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨780748214762,784788503922⟩,⟨-1963659047732,-1955928106598⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1385606413208,1404472025651⟩,⟨-9314385331373,-8991169661979⟩,⟨-4168248553805,-4035562316442⟩,⟨52750761640580,62175851580491⟩,⟨33841804704282,38202750080499⟩,⟨10677674745098,12404715500368⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1404472025651,-1385606413208⟩,⟨8991169661979,9314385331373⟩,⟨4035562316442,4168248553805⟩,⟨-62175851580491,-52750761640580⟩,⟨-38202750080499,-33841804704282⟩,⟨-12404715500368,-10677674745098⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-304960397875,-286094785432⟩,⟨8991169661979,9314385331373⟩,⟨4035562316442,4168248553805⟩,⟨-62175851580491,-52750761640580⟩,⟨-38202750080499,-33841804704282⟩,⟨-12404715500368,-10677674745098⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13590923836,-12112754504⟩,⟨411291532900,448819109872⟩,⟨48993639832,71548565349⟩,⟨-4830293360198,-4158047550347⟩,⟨1712200328074,2162341800142⟩,⟨2669313346549,2879268263103⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429339747491,446125721455⟩,⟨754527118444,1120507296481⟩,⟨-215779619466,87691128594⟩,⟨-25398687768732,-13587381950968⟩,⟨-11368821176636,276508754095⟩,⟨-8160675199564,5255803868487⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99685855397,-99256358666⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4202341205,4442619034⟩,⟨26148428184,28539023395⟩,⟨39624999436,39835402372⟩,⟨-292288295079,-281026421061⟩,⟨250784818133,251900503000⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9197134705,9742183137⟩,⟨7823197829,16411807788⟩,⟨86722243560,87354729775⟩,⟨-879126868966,-741675211085⟩,⟨105867709348,117030113883⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1479376550201,1498000915739⟩,⟨-7781032608713,-7455018395807⟩,⟨-1472554960107,-1397440004483⟩,⟨109252898703777,117263176376029⟩,⟨23131140645244,25079294570760⟩,⟨5135507523964,5617492213830⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12374608024,13272983107⟩,⟨-58417562518,-39999490872⟩,⟨103635969392,107324941596⟩,⟨-516157207681,-64994076747⟩,⟨-304243137036,-216287000740⟩,⟨-191027835865,-170668160480⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13272983107,-12374608024⟩,⟨39999490872,58417562518⟩,⟨-107324941596,-103635969392⟩,⟨64994076747,516157207681⟩,⟨216287000740,304243137036⟩,⟨170668160480,191027835865⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112958838504,-111630966690⟩,⟨-838750817890,-819473752784⟩,⟨-107324941596,-103635969392⟩,⟨2264017332299,2715180463233⟩,⟨216287000740,304243137036⟩,⟨170668160480,191027835865⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨82615528346,87693180259⟩,⟨-579678846500,-537974500080⟩,⟨616937152993,638591961385⟩,⟨3160228474580,3866494573418⟩,⟨-3796631501344,-3324122299638⟩,⟨-2601948597501,-2374228802665⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨111157965254,119475284312⟩,⟨-1410356106180,-1283994737261⟩,⟨712633963782,765031562548⟩,⟨19756383551300,22824854831710⟩,⟨-7270031207992,-5878986798469⟩,⟨-4869591279922,-4314668307279⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-119475284312,-111157965254⟩,⟨1283994737261,1410356106180⟩,⟨-765031562548,-712633963782⟩,⟨-22824854831710,-19756383551300⟩,⟨5878986798469,7270031207992⟩,⟨4314668307279,4869591279922⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨980036343464,988353662522⟩,⟨1283994737261,1410356106180⟩,⟨-765031562548,-712633963782⟩,⟨-22824854831710,-19756383551300⟩,⟨5878986798469,7270031207992⟩,⟨4314668307279,4869591279922⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119930338883,122764070004⟩,⟨775607027878,805621843869⟩,⟨182739921925,194751591636⟩,⟨-2790699423554,-2169075126441⟩,⟨-815458942677,-536269872459⟩,⟨-224153985265,-111486538430⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11333643418,11604878816⟩,⟨166398689908,172338910822⟩,⟨21043858300,22052155592⟩,⟨663628452540,819943108772⟩,⟨91968114024,119825118544⟩,⟨-19713967613,-13702826706⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164161136162,175179844061⟩,⟨1463747794110,1888681257695⟩,⟨-6625003761,226787881720⟩,⟨-11216980125315,7647509450639⟩,⟨-6085344505168,7114791753961⟩,⟨-6390208050658,5241816436957⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-175179844061,-164161136162⟩,⟨-1888681257695,-1463747794110⟩,⟨-226787881720,6625003761⟩,⟨-7647509450639,11216980125315⟩,⟨-7114791753961,6085344505168⟩,⟨-5241816436957,6390208050658⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48465290696,64665682050⟩,⟨-362975553589,233788798722⟩,⟨-21893771369,292970769513⟩,⟨-15041305006134,10883870387432⟩,⟨-10550592594225,6871268411478⟩,⟨-7339711938748,8312435212498⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28263732627429,29703239226406⟩,⟨-283145179845684,-235326137226962⟩,⟨-107700998833022,-68804251840432⟩,⟨2743300577973602,4773697349770319⟩,⟨481163532908191,2352888215055956⟩,⟨-662888002548329,1323849672849477⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13081522578,13707010007⟩,⟨169200236438,179900628496⟩,⟨39865082296,43489304570⟩,⟨471061216193,707384315943⟩,⟨75715995978,168404055902⟩,⟨10688060730,44669948895⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336269892163,370294035126⟩,⟨819596998191,2060193972166⟩,⟨-317888990670,356257117820⟩,⟨-47908083529431,6193883370969⟩,⟨-21150204755173,14761296153654⟩,⟨-16508976000440,12721182945738⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370294035126,-336269892163⟩,⟨-2060193972166,-819596998191⟩,⟨-356257117820,317888990670⟩,⟨-6193883370969,47908083529431⟩,⟨-14761296153654,21150204755173⟩,⟨-12721182945738,16508976000440⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59045712365,109855829292⟩,⟨-1305666853722,300910298290⟩,⟨-572036737286,405580119264⟩,⟨-31592571139701,34320701578463⟩,⟨-26130117330290,21426713509268⟩,⟨-20881858145302,21764779868927⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨233807289359,236256930671⟩,⟨1571769928447,1580095142366⟩,⟨311627067882,313670312921⟩,⟨-3952509420833,-3938729622240⟩,⟨-1569485068700,-1561591388566⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1705154532689,-1616908671542⟩,⟨-5640144044301,-2657205099910⟩,⟨-575100327473,1530299818694⟩,⟨-21827271287398,106080907589275⟩,⟨-62370271333562,45530206388943⟩,⟨-52377073153966,56427156654929⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-190386081539,-176365942862⟩,⟨-1879122261921,-1430421650364⟩,⟨-366238251526,-97868842501⟩,⟨-7512476048277,12423337317903⟩,⟨-7595617139496,7027867892131⟩,⟨-5887852724103,7190011496687⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43421207820,59890987809⟩,⟨-307352333474,149673492002⟩,⟨-54611183644,215801470420⟩,⟨-11464985469110,8484607695663⟩,⟨-9165102208196,5466276503565⟩,⟨-6239009585769,6839540823157⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2602671533,6460961348⟩,⟨-113056392437,41056075169⟩,⟨-35830729926,53125097003⟩,⟨-3916130268473,3968014863304⟩,⟨-3072731350903,2215724822084⟩,⟨-2266306025794,2326714855261⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1714762482,3262294214⟩,⟨-33483292750,16305590698⟩,⟨-5949400900,23509643570⟩,⟨-1332685864303,1096153924586⟩,⟨-1119104327010,654254943754⟩,⟨-701121499832,829817746663⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3043216554,5838262080⟩,⟨-84033159104,17057278284⟩,⟨-21436916550,36631823739⟩,⟨-2570907453951,2594432855333⟩,⟨-2191961647767,1414031470227⟩,⟨-1399037850924,1551813522261⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5838262080,-3043216554⟩,⟨-17057278284,84033159104⟩,⟨-36631823739,21436916550⟩,⟨-2594432855333,2570907453951⟩,⟨-1414031470227,2191961647767⟩,⟨-1551813522261,1399037850924⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3235590547,3417744794⟩,⟨-130113670721,125089234273⟩,⟨-72462553665,74562013553⟩,⟨-6510563123806,6538922317255⟩,⟨-4486762821130,4407686469851⟩,⟨-3818119548055,3725752706185⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48465290696,64665682050⟩,⟨-362975553589,233788798722⟩,⟨-21893771369,292970769513⟩,⟨-15041305006134,10883870387432⟩,⟨-10550592594225,6871268411478⟩,⟨-7339711938748,8312435212498⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3235590547,3417744794⟩,⟨-130113670721,125089234273⟩,⟨-72462553665,74562013553⟩,⟨-6510563123806,6538922317255⟩,⟨-4486762821130,4407686469851⟩,⟨-3818119548055,3725752706185⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (103/1024) u, BivariateJet2.affineZ (557/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000006

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000007Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2525295488000,-2525295430144⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-116561173120,-116561173056⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2119834084864,-2119834045952⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-172811246720,-172811246656⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨88162957248,88162957312⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-95853312896,-95853312832⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨88163080768,88163080832⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-95853458944,-95853458880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨-7690378112,-7690378048⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-7690355648,-7690355584⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨184016270080,184016270144⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨184016539712,184016539776⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨1947022799232,1947022837824⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨1947022799232,1947022837824⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2126803568128,-2126803529088⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2112903342784,-2112903303872⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-173995191296,-173995191232⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-171629458176,-171629458112⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨85567699008,85567699072⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-92793126080,-92793126016⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨90780886144,90780886208⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-98956242752,-98956242688⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨-8175356608,-8175356544⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-7225427072,-7225427008⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨178360825088,178360825152⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨189737128896,189737128960⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨1938908112640,1938908151232⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨1955174070976,1955174109568⟩



end LaneCBRB2Cell000007Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000007
open Set LaneCBRB2Cell000007Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110595407872,110595407872⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨123480309760,123480309760⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110595407872,-110595407872⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439160406016,439160406016⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49319772160,49319772160⟩,⟨-123480309760,-123480309760⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159915180032,159915180032⟩,⟨976031318016,976031318016⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49319772160,49319772160⟩,⟨-123480309760,-123480309760⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2119834084864,-2119834045952⟩,⟨6710793703370,6710793703372⟩,⟨3019488035949,3019488035951⟩,⟨-40958868457171,-40958868457158⟩,⟨-25989031849544,-25989031849536⟩,⟨-8292143319748,-8292143319744⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308312927991,-308312922330⟩,⟨-905735462397,-905735427852⟩,⟨-407531137647,-407531122102⟩,⟨5957140113634,5957140113641⟩,⟨3700707793835,3700707832754⟩,⟨1206025983107,1206025983111⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨308312922330,308312927991⟩,⟨905735427852,905735462397⟩,⟨407531122102,407531137647⟩,⟨-5957140113641,-5957140113634⟩,⟨-3700707832754,-3700707793835⟩,⟨-1206025983111,-1206025983107⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159915180032,-159915180032⟩,⟨-976031318016,-976031318016⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939596447744,939596447744⟩,⟨-976031318016,-976031318016⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-172811246720,-172811246656⟩,⟨-1142147552611,-1142147552609⟩,⟨-513903574277,-513903574276⟩,⟨-1186436777003,-1186436776998⟩,⟨752812378523,752812378527⟩,⟨-240194716439,-240194716438⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147677231825,-147677231769⟩,⟨-822627584414,-822627584353⟩,⟨-370137163945,-370137163916⟩,⟨1013879028630,1013879028641⟩,⟨1382890175013,1382890175085⟩,⟨205260314333,205260314337⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147677231769,147677231825⟩,⟨822627584353,822627584414⟩,⟨370137163916,370137163945⟩,⟨-1013879028641,-1013879028630⟩,⟨-1382890175085,-1382890175013⟩,⟨-205260314337,-205260314333⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨455990154099,455990159816⟩,⟨1728363012205,1728363046811⟩,⟨777668286018,777668301592⟩,⟨-6971019142282,-6971019142264⟩,⟨-5083598007839,-5083597968848⟩,⟨-1411286297448,-1411286297440⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨814836120592,814836132187⟩,⟨4137097269227,4137097361757⟩,⟨777668286018,777668301592⟩,⟨-19124561667896,-19124561667868⟩,⟨-5083598007839,-5083597968848⟩,⟨-1411286297448,-1411286297440⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98639544320,98639544320⟩,⟨-246960619520,-246960619520⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12255995584212,12255995584213⟩,⟨30684937599591,30684937599597⟩,⟨-109131647636826,-109131647636807⟩,⟨153649760889881,153649760889921⟩,⟨-273229357408660,-273229357408476⟩,⟨1943492298784139,1943492298784627⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9082785159836,9082785289085⟩,⟨68855516817492,68855518172503⟩,⟨-72207795328876,-72207794004401⟩,⟨131605679453962,131605686239312⟩,⟨-648076144188660,-648076131253781⟩,⟨1270195353187571,1270195376774912⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨91793972736,91794106624⟩,⟨-688902211072,-688900160239⟩,⟨722439728279,722441877993⟩,⟨8971376740479,8971427603313⟩,⟨-4305020565525,-4304952091013⟩,⟨-1394106948649,-1394017581719⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1191305600512,1191305734400⟩,⟨-688902211072,-688900160239⟩,⟨722439728279,722441877993⟩,⟨8971376740479,8971427603313⟩,⟨-4305020565525,-4304952091013⟩,⟨-1394106948649,-1394017581719⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨88162957248,88163080832⟩,⟨-635820054191,-635818089921⟩,⟨666773321635,666775380646⟩,⟨7912423218254,7912473364305⟩,⟨-3587727591714,-3587661564976⟩,⟨-1691038183429,-1690953060628⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨95523341521,95523486160⟩,⟨-744141123437,-744138675876⟩,⟨780367568235,780370133913⟩,⟨10089104367226,10089169583359⟩,⟨-5067986783259,-5067903765379⟩,⟨-1067787865396,-1067682794565⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-91794106624,-91793972736⟩,⟨688900160239,688902211072⟩,⟨-722441877993,-722439728279⟩,⟨-8971427603313,-8971376740479⟩,⟨4304952091013,4305020565525⟩,⟨1394017581719,1394106948649⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1007717521152,1007717655040⟩,⟨688900160239,688902211072⟩,⟨-722441877993,-722439728279⟩,⟨-8971427603313,-8971376740479⟩,⟨4304952091013,4305020565525⟩,⟨1394017581719,1394106948649⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-95853458944,-95853312832⟩,⟨751652740001,751655077515⟩,⟨-788249909894,-788247459629⟩,⟨-10302496081035,-10302436088535⟩,⟨5235959354229,5236038041080⟩,⟨955896440547,955997663326⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-87851024432,-87850878845⟩,⟨628842804976,628845309205⟩,⟨-659461065432,-659458440331⟩,⟨-7718375513415,-7718307915451⟩,⟨3435764172225,3435849479919⟩,⟨1790400510326,1790507677126⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7672317089,7672607315⟩,⟨-115298318461,-115293366671⟩,⟨120906502803,120911693582⟩,⟨2370728853811,2370861667908⟩,⟨-1632222611034,-1632054285460⟩,⟨722612644930,722824882561⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3836158544,3836303658⟩,⟨-57649159231,-57646683335⟩,⟨60453251401,60455846791⟩,⟨1185364426905,1185430833954⟩,⟨-816111305517,-816027142730⟩,⟨361306322465,361412441281⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3836303658,-3836158544⟩,⟨57646683335,57649159231⟩,⟨-60455846791,-60453251401⟩,⟨-1185430833954,-1185364426905⟩,⟨816027142730,816111305517⟩,⟨-361412441281,-361306322465⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758287079958,758287244336⟩,⟨57646683335,57649159231⟩,⟨-60455846791,-60453251401⟩,⟨-1185430833954,-1185364426905⟩,⟨816027142730,816111305517⟩,⟨-361412441281,-361306322465⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7663523711,7663546068⟩,⟨-115027729438,-115027219228⟩,⟨120627396828,120627931716⟩,⟨2361233314690,2361249132097⟩,⟨-1624116201004,-1624098330368⟩,⟨716587890756,716608802012⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7663546068,-7663523711⟩,⟨115027219228,115027729438⟩,⟨-120627931716,-120627396828⟩,⟨-2361249132097,-2361233314690⟩,⟨1624098330368,1624116201004⟩,⟨-716608802012,-716587890756⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091848081708,1091848104065⟩,⟨115027219228,115027729438⟩,⟨-120627931716,-120627396828⟩,⟨-2361249132097,-2361233314690⟩,⟨1624098330368,1624116201004⟩,⟨-716608802012,-716587890756⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7690378112,-7690355584⟩,⟨115834578620,115835094784⟩,⟨-121474604186,-121474063055⟩,⟨-2390025836449,-2390009750575⟩,⟨1648295047518,1648313191110⟩,⟨-735059166274,-735037973899⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3845189056,-3845177792⟩,⟨57917289310,57917547392⟩,⟨-60737302093,-60737031527⟩,⟨-1195012918225,-1195004875287⟩,⟨824147523759,824156595555⟩,⟨-367529583137,-367518986949⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3845177792,3845189056⟩,⟨-57917547392,-57917289310⟩,⟨60737031527,60737302093⟩,⟨1195004875287,1195012918225⟩,⟨-824156595555,-824147523759⟩,⟨367518986949,367529583137⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765968561408,765968591936⟩,⟨-57917547392,-57917289310⟩,⟨60737031527,60737302093⟩,⟨1195004875287,1195012918225⟩,⟨-824156595555,-824147523759⟩,⟨367518986949,367529583137⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272962020427,272962026017⟩,⟨28756804807,28756932360⟩,⟨-30156982929,-30156849207⟩,⟨-590312283025,-590308328672⟩,⟨406024582592,406029050251⟩,⟨-179152200503,-179146972689⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531937122816,1531937183872⟩,⟨-115835094784,-115834578620⟩,⟨121474063054,121474604186⟩,⟨2390009750574,2390025836450⟩,⟨-1648313191110,-1648295047518⟩,⟨735037973898,735059166274⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1199667201986,1199667361378⟩,⟨-820124172159,-820121512754⟩,⟨860049680674,860052468405⟩,⟨11801549824816,11801620337192⟩,⟨-6300949049203,-6300858701447⟩,⟨-426505092375,-426390431515⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1299822776196,1299823094980⟩,⟨-1640248344318,-1640243025508⟩,⟨1720099361348,1720104936811⟩,⟨23603099649644,23603240674382⟩,⟨-12601898098407,-12601717402899⟩,⟨-853010034587,-852781013193⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨184016270080,184016539776⟩,⟨-1387475400530,-1387470561100⟩,⟨1455020499354,1455025572452⟩,⟨18214846174918,18214982577240⟩,⟨-8823777410724,-8823609141304⟩,⟨-2647046339714,-2646839008263⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨63306455143,63306561204⟩,⟨-470294381715,-470292650625⟩,⟨493189164949,493190979566⟩,⟨6015974796220,6016020221449⟩,⟨-2825111823159,-2825053351325⟩,⟨-1071076184922,-1071001793385⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380314897675,380314920622⟩,⟨11309598140,11309906187⟩,⟨-11860536526,-11860213579⟩,⟨-235196757856,-235187156052⟩,⟨162857426886,162868243329⟩,⟨-73795565376,-73782947435⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178749383898,3178749575695⟩,⟨-94530505413,-94527919285⟩,⟨99130075005,99132786226⟩,⟨1971364078313,1971444876653⟩,⟨-1367182110351,-1367091217852⟩,⟨622875657985,622981533566⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨183022489438,183022807111⟩,⟨-1365090126961,-1365084882225⟩,⟨1431544958789,1431550456647⟩,⟨17586887970592,17587027699157⟩,⟨-8331078599508,-8330901064408⟩,⟨-2971747708790,-2971523536324⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨367038759518,367039346887⟩,⟨-2752565527491,-2752555443325⟩,⟨2886565458143,2886576029099⟩,⟨35801734145510,35802010276397⟩,⟨-17154856010232,-17154510205712⟩,⟨-5618794048504,-5618362544587⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522958812899,522959039630⟩,⟨79513002082,79516434366⟩,⟨-83387744722,-83384146780⟩,⟨-1629039507555,-1628947037540⟩,⟨1119219833506,1119336709040⟩,⟨-491854459257,-491707408984⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360662771683,360663006233⟩,⟨82255176722,82258745208⟩,⟨-86263566787,-86259826061⟩,⟨-1678967535434,-1678870971660⟩,⟨1151260274570,1151381997388⟩,⟨-501940285315,-501787460418⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721325543366,721326012466⟩,⟨164510353444,164517490416⟩,⟨-172527133574,-172519652122⟩,⟨-3357935070868,-3357741943320⟩,⟨2302520549140,2302763994776⟩,⟨-1003880570630,-1003574920836⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524273576748,1524273660161⟩,⟨-807875556,-806849182⟩,⟨846131338,847207358⟩,⟨28760618477,28792521760⟩,⟨-24214860742,-24178846514⟩,⟨18429171886,18471275518⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨999987119927,999987824972⟩,⟨227533785802,227544366092⟩,⟨-238622514392,-238611423350⟩,⟨-4636542172761,-4636252921880⟩,⟨3176394619673,3176756257826⟩,⟨-1379874094573,-1379422311556⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67764871887,67764874664⟩,⟨14278185592,14278249218⟩,⟨-14973395372,-14973328668⟩,⟨-291594702386,-291592719641⟩,⟨200019836644,200022073028⟩,⟨-87297507092,-87294894909⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50219810255,50219813029⟩,⟨265558126365,265558189822⟩,⟨36832469233,36832521750⟩,⟨-1287330577402,-1287328575419⟩,⟨-211319908418,-211317936254⟩,⟨-172856263805,-172854228675⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134430677198,2134430847336⟩,⟨-322783469342,-322782018144⟩,⟨338496877978,338498399376⟩,⟨6684353703168,6684399010659⟩,⟨-4618747498934,-4618696529274⟩,⟨2075081114321,2075140489294⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2973878136323,2973878491901⟩,⟨-674595865837,-674592806043⟩,⟨707435810907,707439018723⟩,⟨14020859769932,14020955472959⟩,⟨-9706365332079,-9706257945399⟩,⟨4392876302947,4393001067533⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135830847036,135830870781⟩,⟨687450144748,687450543721⟩,⟨131933636248,131933938506⟩,⟨-3167341413093,-3167329619487⟩,⟨-866633237054,-866621954894⟩,⟨-219489170590,-219477618057⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8900228737867,8900230293744⟩,⟨-45044761835692,-45044719944418⟩,⟨-8644887828411,-8644865000673⟩,⟨663486555562175,663488169244946⟩,⟨144289445449348,144290501706845⟩,⟨31174783228772,31175630984628⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8094606621190,8094613743371⟩,⟨-39125653234101,-39125500284056⟩,⟨-9793964552974,-9793848131687⟩,⟨547254197178825,547259322454816⟩,⟨164927146112916,164931682516693⟩,⟨20935396207436,20940030537520⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16189213242380,16189227486742⟩,⟨-78251306468202,-78251000568112⟩,⟨-19587929105948,-19587696263374⟩,⟨1094508394357650,1094518644909632⟩,⟨329854292225832,329863365033386⟩,⟨41870792414872,41880061075040⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10931067056724,10931067056725⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603222,2160817149603840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9831555428948,9831555428949⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603232,2160817149603830⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2408734257088,2408734314944⟩,⟨-12153542525660,-12153542525558⟩,⟨0,0⟩,⟨107314718406763,107314718418708⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7559794006877,7559794006878⟩,⟨-46140683498507,-46140683498493⟩,⟨-20760769582937,-20760769582930⟩,⟨563232985388625,563232985388865⟩,⟨305401926211666,305401926211790⟩,⟨114026798424258,114026798424307⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6460282379101,6460282379102⟩,⟨-46140683498508,-46140683498493⟩,⟨-20760769582938,-20760769582929⟩,⟨563232985388627,563232985388859⟩,⟨305401926211666,305401926211788⟩,⟨114026798424258,114026798424307⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1947022799232,1947022837824⟩,⟨-7852941255984,-7852941255938⟩,⟨-3533391610228,-3533391610207⟩,⟨39772431679076,39772431681453⟩,⟨26741844227526,26741844228649⟩,⟨8051948603069,8051948603584⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99471065088,99471065088⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136656794983,136656794983⟩,⟨692119406592,692119406592⟩,⟨311415662592,311415662592⟩,⟨-1732836851712,-1732836851712⟩,⟨-1559362535424,-1559362535424⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4355757056320,4355757152768⟩,⟨-20006483781644,-20006483781496⟩,⟨-3533391610228,-3533391610207⟩,⟨147087150085839,147087150100161⟩,⟨26741844227526,26741844228649⟩,⟨8051948603069,8051948603584⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨734077519036,734078693774⟩,⟨-5505131054982,-5505110886650⟩,⟨5773130916286,5773152058198⟩,⟨71603468291020,71604020552794⟩,⟨-34309712020464,-34309020411424⟩,⟨-11237588097008,-11236725089174⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5089834575356,5089835846542⟩,⟨-25511614836626,-25511594668146⟩,⟨2239739306058,2239760447991⟩,⟨218690618376859,218691170652955⟩,⟨-7567867792938,-7567176182775⟩,⟨-3185639493939,-3184776485590⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨460469224283,460469339286⟩,⟨1757907864357,1757910704429⟩,⟨202625646391,202627559069⟩,⟨-31153870784597,-31153786056387⟩,⟨1104513809175,1104593266817⟩,⟨-288199729265,-288121654274⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36990695811,36990697885⟩,⟨-744194402756,-744194392369⟩,⟨329378021832,329378040293⟩,⟨9288662238245,9288662264701⟩,⟨-6626565812353,-6626565719884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497459920094,497460037171⟩,⟨1013713461601,1013716312060⟩,⟨532003668223,532005599362⟩,⟨-21865208546352,-21865123791686⟩,⟨-5522052003178,-5521972453067⟩,⟨-288199729265,-288121654274⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501892554988,501892567044⟩,⟨2532355881864,2532356003553⟩,⟨0,0⟩,⟨3194096148032,3194099067279⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227074843042,227074901939⟩,⟨1608460292036,1608461929002⟩,⟨242842980066,242843867405⟩,⟨-3866156782978,-3866102839958⟩,⟨-1295351682373,-1295310803083⟩,⟨-131554135753,-131518493809⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-734078693774,-734077519036⟩,⟨5505110886650,5505131054982⟩,⟨-5773152058198,-5773130916286⟩,⟨-71604020552794,-71603468291020⟩,⟨34309020411424,34309712020464⟩,⟨11236725089174,11237588097008⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3621678362546,3621679633732⟩,⟨-14501372894994,-14501352726514⟩,⟨-9306543668426,-9306522526493⟩,⟨75483129533045,75483681809141⟩,⟨61050864638950,61051556249113⟩,⟨19288673692243,19289536700592⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450133445597,450133603592⟩,⟨477414447658,477417754557⟩,⟨-130926367210,-130923379467⟩,⟨-14582711249076,-14582615212770⟩,⟨-7513963440445,-7513856657587⟩,⟨-4029983186383,-4029863542568⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨319830360064,319830360064⟩,⟨1952062636032,1952062636032⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-319830360064,-319830360064⟩,⟨-1952062636032,-1952062636032⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨779681267712,779681267712⟩,⟨-1952062636032,-1952062636032⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1380664984362,1380665011729⟩,⟨-9025372243697,-9025372175146⟩,⟨-4060921064547,-4060921033701⟩,⟨56087343517785,56087343519636⟩,⟨35403415408276,35403415486333⟩,⟨11354910630871,11354910631272⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1380665011729,-1380664984362⟩,⟨9025372175146,9025372243697⟩,⟨4060921033701,4060921064547⟩,⟨-56087343519636,-56087343517785⟩,⟨-35403415486333,-35403415408276⟩,⟨-11354910631272,-11354910630871⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-281153383953,-281153356586⟩,⟨9025372175146,9025372243697⟩,⟨4060921033701,4060921064547⟩,⟨-56087343519636,-56087343517785⟩,⟨-35403415486333,-35403415408276⟩,⟨-11354910631272,-11354910630871⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12611436286,-12611435057⟩,⟨436417579201,436417585352⟩,⟨69860348859,69860361176⟩,⟨-4543041108401,-4543041092918⟩,⟨1841895316104,1841895377820⟩,⟨2734641252287,2734641276948⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437522009311,437522168535⟩,⟨913832026859,913835339909⟩,⟨-61066018351,-61063018291⟩,⟨-19125752357477,-19125656305688⟩,⟨-5672068124341,-5671961279767⟩,⟨-1295341934096,-1295222265620⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99471065088,-99471065088⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4461881205,4461881205⟩,⟨28226954240,28226954240⟩,⟨39730142208,39730142208⟩,⟨-295918632960,-295918632960⟩,⟨251342618624,251342618624⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9774781674,9774781909⟩,⟨12517892792,12517894281⟩,⟨87038055949,87038058040⟩,⟨-836806810200,-836806794571⟩,⟨111463671483,111463684713⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1483642872303,1483642893416⟩,⟨-7532772474159,-7532772091283⟩,⟨-1415968217333,-1415968148674⟩,⟨111312738498818,111312746177158⟩,⟨23634494168564,23634495726393⟩,⟨5272412124034,5272412420830⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13189751515,13189752021⟩,⟨-50075983098,-50075975833⟩,⟨104858018687,104858024095⟩,⟨-311095991224,-311095832890⟩,⟨-251901407018,-251901320789⟩,⟨-177305601355,-177305581332⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13189752021,-13189751515⟩,⟨50075975833,50075983098⟩,⟨-104858024095,-104858018687⟩,⟨311095832890,311095991224⟩,⟨251901320789,251901407018⟩,⟨177305581332,177305601355⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112660817109,-112660816603⟩,⟨-828244836199,-828244828934⟩,⟨-104858024095,-104858018687⟩,⟨2510119088442,2510119246776⟩,⟨251901320789,251901407018⟩,⟨177305581332,177305601355⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨87335793840,87335795572⟩,⟨-570911885604,-570911881266⟩,⟨619174219413,619174234830⟩,⟨3547879265425,3547879265545⟩,⟨-3487247490885,-3487247452220⟩,⟨-2461393812861,-2461393812819⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨117847892422,117847896437⟩,⟨-1368707706877,-1368707647781⟩,⟨723019826709,723019867088⟩,⟨21451769804845,21451771115433⟩,⟨-6334992795456,-6334992152875⟩,⟨-4497288696319,-4497288500078⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-117847896437,-117847892422⟩,⟨1368707647781,1368707706877⟩,⟨-723019867088,-723019826709⟩,⟨-21451771115433,-21451769804845⟩,⟨6334992152875,6334992795456⟩,⟨4497288500078,4497288696319⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨981663731339,981663735354⟩,⟨1368707647781,1368707706877⟩,⟨-723019867088,-723019826709⟩,⟨-21451771115433,-21451769804845⟩,⟨6334992152875,6334992795456⟩,⟨4497288500078,4497288696319⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122009641268,122009641768⟩,⟨788051438231,788051448105⟩,⟨188174347924,188174354081⟩,⟨-2490173877955,-2490173634335⟩,⟨-672324867790,-672324740071⟩,⟨-163814057110,-163814008563⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11543724756,11543724861⟩,⟨169731245068,169731247320⟩,⟨21488431252,21488432458⟩,⟨733411818642,733411875292⟩,⟨106353933740,106353961180⟩,⟨-16334870170,-16334863836⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨169969845670,169969996768⟩,⟨1677566404775,1677571855937⟩,⟨110742923049,110745665669⟩,⟨-1869302403487,-1869089579333⟩,⟨475985978628,476125095180⟩,⟨-566553180186,-566446415900⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-169969996768,-169969845670⟩,⟨-1677571855937,-1677566404775⟩,⟨-110745665669,-110742923049⟩,⟨1869089579333,1869302403487⟩,⟨-476125095180,-475985978628⟩,⟨566446415900,566553180186⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57104846274,57105056269⟩,⟨-69111563901,-69104475773⟩,⟨132097314397,132100944356⟩,⟨-1997067203645,-1996800436471⟩,⟨-1771476777553,-1771296781711⟩,⟨434892280147,435034686377⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28667970841108,28667996633353⟩,⟨-254194795358036,-254194149184598⟩,⟨-86712157910993,-86711699128225⟩,⟨3641542386271988,3641565461341781⟩,⟨1369222175594821,1369241245878230⟩,⟨318596088332933,318614103659401⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13539058784,13539058896⟩,⟨174895600646,174895603556⟩,⟨41762331758,41762333298⟩,⟨576983159605,576983244248⟩,⟨120527964550,120528005718⟩,⟨28053711122,28053726264⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353008856505,353009177024⟩,⟨1430038241003,1430050402245⟩,⟨21136926205,21143604164⟩,⟨-20983053657207,-20982546490202⟩,⟨-3445230743505,-3444893771600⟩,⟨-1932557951127,-1932299935974⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353009177024,-353008856505⟩,⟨-1430050402245,-1430038241003⟩,⟨-21143604164,-21136926205⟩,⟨20982546490202,20983053657207⟩,⟨3444893771600,3445230743505⟩,⟨1932299935974,1932557951127⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84512832287,84513312030⟩,⟨-516218375386,-516202901094⟩,⟨-82209622515,-82199944496⟩,⟨1856794132725,1857397351519⟩,⟨-2227174352741,-2226730536262⟩,⟨636958001878,637335685507⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236127860071,236127860071⟩,⟨1570440218624,1570440218624⟩,⟨311415662592,311415662592⟩,⟨-3931860107264,-3931860107264⟩,⟨-1559362535424,-1559362535424⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1658819744098,-1658818277107⟩,⟨-4177147678947,-4177105462036⟩,⟨463110564413,463135869588⟩,⟨42700286457057,42701834021467⟩,⟨-7872530677543,-7871391268762⟩,⟨2055503505833,2056500428864⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-184074454169,-184074290626⟩,⟨-1652449639917,-1652443886995⟩,⟨-232506299701,-232503231091⟩,⟨2507456534462,2507692563801⟩,⟨-242232273046,-242079353185⟩,⟨633754074234,633873659481⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52053405902,52053569445⟩,⟨-82009421293,-82003668371⟩,⟨78909362891,78912431501⟩,⟨-1424403572802,-1424167543463⟩,⟨-1801594808470,-1801441888609⟩,⟨282940390522,283059975769⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4389305373,4389346431⟩,⟨-32122922257,-32121445004⟩,⟨5883824139,5884679137⟩,⟨7818963721,7880624571⟩,⟨-308690539169,-308647753761⟩,⟨46754784830,46788526157⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2464327795,2464343281⟩,⟨-7765053136,-7764484026⟩,⟨7471500968,7471814994⟩,⟨-122637518269,-122613029873⟩,⟨-182355512726,-182339214118⟩,⟨38116374608,38128662621⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4363848712,4363876223⟩,⟨-31351263545,-31350144883⟩,⟨5311169711,5311775820⟩,⟨-17114567623,-17062509512⟩,⟨-291393407108,-291360090636⟩,⟨37520653046,37544545801⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4363876223,-4363848712⟩,⟨31350144883,31351263545⟩,⟨-5311775820,-5311169711⟩,⟨17062509512,17114567623⟩,⟨291360090636,291393407108⟩,⟨-37544545801,-37520653046⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨25429150,25497719⟩,⟨-772777374,-770181459⟩,⟨572048319,573509426⟩,⟨24881473233,24995192194⟩,⟨-17330448533,-17254346653⟩,⟨9210239029,9267873111⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57104846274,57105056269⟩,⟨-69111563901,-69104475773⟩,⟨132097314397,132100944356⟩,⟨-1997067203645,-1996800436471⟩,⟨-1771476777553,-1771296781711⟩,⟨434892280147,435034686377⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨25429150,25497719⟩,⟨-772777374,-770181459⟩,⟨572048319,573509426⟩,⟨24881473233,24995192194⟩,⟨-17330448533,-17254346653⟩,⟨9210239029,9267873111⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110380659507,110810156237⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121547574476,125413045044⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110810156237,-110380659507⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438945657651,439375154381⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨48524070747,50116228547⟩,⟨-125413045044,-121547574476⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158904730254,160926384784⟩,⟨974098582732,977964053300⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨48094574017,50545725277⟩,⟨-125413045044,-121547574476⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2126803568128,-2112903303872⟩,⟨6655420239207,6766839768908⟩,⟨2999047391742,3040174388929⟩,⟨-41645871950163,-40285720897779⟩,⟨-26318329737985,-25665733055524⟩,⟨-8406150586868,-8180254788310⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311282573753,-305363145848⟩,⟨-929830712469,-881494136890⟩,⟨-416459287664,-398545541199⟩,⟨5697212355587,6215359903324⟩,⟨3574845068551,3825699788164⟩,⟨1164213459100,1247529328263⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305363145848,311282573753⟩,⟨881494136890,929830712469⟩,⟨398545541199,416459287664⟩,⟨-6215359903324,-5697212355587⟩,⟨-3825699788164,-3574845068551⟩,⟨-1247529328263,-1164213459100⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160926384784,-158904730254⟩,⟨-977964053300,-974098582732⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938585242992,940606897522⟩,⟨-977964053300,-974098582732⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173995191296,-171629458112⟩,⟨-1145642184532,-1138661348470⟩,⟨-514708807544,-513100484187⟩,⟨-1193708171723,-1179205052266⟩,⟨748957815457,756659682645⟩,⟨-240948026261,-239444586325⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148848882481,-146509479824⟩,⟨-828017554306,-817244377598⟩,⟨-371803843545,-368472118309⟩,⟨996375703435,1031375439484⟩,⟨1374493809722,1391294204132⟩,⟨203553175650,206965858810⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146509479824,148848882481⟩,⟨817244377598,828017554306⟩,⟨368472118309,371803843545⟩,⟨-1031375439484,-996375703435⟩,⟨-1391294204132,-1374493809722⟩,⟨-206965858810,-203553175650⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨451872625672,460131456234⟩,⟨1698738514488,1757848266775⟩,⟨767017659508,788263131209⟩,⟨-7246735342808,-6693588059022⟩,⟨-5216993992296,-4949338878273⟩,⟨-1454495187073,-1367766634750⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨809773802574,819923609072⟩,⟨4100345395812,4173697676253⟩,⟨767017659508,788263131209⟩,⟨-19507608971466,-18739551847622⟩,⟨-5216993992296,-4949338878273⟩,⟨-1454495187073,-1367766634750⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨96189148034,101091450554⟩,⟨-250826090088,-243095148952⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11958734521955,12568214235429⟩,⟨28757232525209,32773302399424⟩,⟨-114818795734288,-103851207211815⟩,⟨138305340082715,170921553379681⟩,⟨-338674688268054,-212135518259765⟩,⟨1803714802691063,2097888467990759⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8807428392007,9372320687820⟩,⟨65776289893873,72147969088841⟩,⟨-77279838318692,-67474436090275⟩,⟨93359089389904,172452022019902⟩,⟨-727975299584754,-573856094304324⟩,⟨1147150888322635,1404660093837427⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨88985362432,94633841920⟩,⟨-767428824586,-618241658612⟩,⟨634202800883,822015868694⟩,⟨6700905391317,11520467992702⟩,⟨-7886065842071,-1012229191185⟩,⟨-5959537846556,3442169555866⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1188496990208,1194145469696⟩,⟨-767428824586,-618241658612⟩,⟨634202800883,822015868694⟩,⟨6700905391317,11520467992702⟩,⟨-7886065842071,-1012229191185⟩,⟨-5959537846556,3442169555866⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨85567699008,90780886208⟩,⟨-709969754300,-569247139204⟩,⟨583943390176,760469747331⟩,⟨5711433690613,10363190661535⟩,⟨-6993295478872,-440966124169⟩,⟨-6039307981066,2874318320046⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨92492839694,98594304291⟩,⟨-834438682903,-663430935479⟩,⟨680558729119,893792123546⟩,⟨7335317966566,13197402933697⟩,⟨-9307886074417,-1212117507994⟩,⟨-6377510840664,4542993158833⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-94633841920,-88985362432⟩,⟨618241658612,767428824586⟩,⟨-822015868694,-634202800883⟩,⟨-11520467992702,-6700905391317⟩,⟨1012229191185,7886065842071⟩,⟨-3442169555866,5959537846556⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1004877785856,1010526265344⟩,⟨618241658612,767428824586⟩,⟨-822015868694,-634202800883⟩,⟨-11520467992702,-6700905391317⟩,⟨1012229191185,7886065842071⟩,⟨-3442169555866,5959537846556⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-98956242752,-92793126016⟩,⟨672683052119,839701034295⟩,⟨-899428784841,-690049707615⟩,⟨-13246684801393,-7702525255576⟩,⟨1523538075397,9315629022432⟩,⟨-4502089954650,6087701400289⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-90947544251,-84806516509⟩,⟨545717178224,719566172899⟩,⟨-773113015810,-556676259720⟩,⟨-10852603364057,-4830556228184⟩,⟨-572891647838,7700259578045⟩,⟨-3878040576923,7249669392447⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1545295443,13787787782⟩,⟨-288721504679,56135237420⟩,⟨-92554286691,337115863826⟩,⟨-3517285397491,8366846705513⟩,⟨-9880777722255,6488142070051⟩,⟨-10255551417587,11792662551280⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨772647721,6893893891⟩,⟨-144360752340,28067618710⟩,⟨-46277143346,168557931913⟩,⟨-1758642698746,4183423352757⟩,⟨-4940388861128,3244071035026⟩,⟨-5127775708794,5896331275640⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6893893891,-772647721⟩,⟨-28067618710,144360752340⟩,⟨-168557931913,46277143346⟩,⟨-4183423352757,1758642698746⟩,⟨-3244071035026,4940388861128⟩,⟨-5896331275640,5127775708794⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755229489725,761350755159⟩,⟨-28067618710,144360752340⟩,⟨-168557931913,46277143346⟩,⟨-4183423352757,1758642698746⟩,⟨-3244071035026,4940388861128⟩,⟨-5896331275640,5127775708794⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7201738050,8145038043⟩,⟨-132103628986,-100070716256⟩,⟨102654241512,141500131166⟩,⟨1779890668898,3054398162334⟩,⟨-2504980111868,-877051521376⟩,⟨-294241126250,1821637521055⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8145038043,-7201738050⟩,⟨100070716256,132103628986⟩,⟨-141500131166,-102654241512⟩,⟨-3054398162334,-1779890668898⟩,⟨877051521376,2504980111868⟩,⟨-1821637521055,294241126250⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091366589733,1092309889726⟩,⟨100070716256,132103628986⟩,⟨-141500131166,-102654241512⟩,⟨-3054398162334,-1779890668898⟩,⟨877051521376,2504980111868⟩,⟨-1821637521055,294241126250⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8175356608,-7225427008⟩,⟨100730495217,133089538848⟩,⟨-142556168581,-103331053984⟩,⟨-3093303330126,-1800854023139⟩,⟨892300589477,2540930768488⟩,⟨-1853715673156,286726139501⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4087678304,-3612713504⟩,⟨50365247608,66544769424⟩,⟨-71278084291,-51665526992⟩,⟨-1546651665063,-900427011569⟩,⟨446150294738,1270465384244⟩,⟨-926857836578,143363069751⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3612713504,4087678304⟩,⟨-66544769424,-50365247608⟩,⟨51665526992,71278084291⟩,⟨900427011569,1546651665063⟩,⟨-1270465384244,-446150294738⟩,⟨-143363069751,926857836578⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765736097120,766211081184⟩,⟨-66544769424,-50365247608⟩,⟨51665526992,71278084291⟩,⟨900427011569,1546651665063⟩,⟨-1270465384244,-446150294738⟩,⟨-143363069751,926857836578⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272841647433,273077472432⟩,⟨25017679064,33025907247⟩,⟨-35375032792,-25663560378⟩,⟨-763599540584,-444972667224⟩,⟨219262880344,626245027967⟩,⟨-455409380264,73560281563⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531472194240,1532422162368⟩,⟨-133089538848,-100730495216⟩,⟨103331053984,142556168582⟩,⟨1800854023138,3093303330126⟩,⟨-2540930768488,-892300589476⟩,⟨-286726139502,1853715673156⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1196332902047,1203057562453⟩,⟨-918779441698,-731918469591⟩,⟨750814405608,984132022032⟩,⟨8828586525957,15195859646369⟩,⟨-10944508741186,-2117047964073⟩,⟨-6192447666894,5731117230867⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1293154176318,1306603497130⟩,⟨-1837558883396,-1463836939182⟩,⟨1501628811216,1968264044064⟩,⟨17657173051924,30391719292729⟩,⟨-21889017482366,-4234095928148⟩,⟨-12380053890245,11462234461732⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨178360825088,189737128960⟩,⟨-1562394798717,-1231824145069⟩,⟨1263626143784,1673527598346⟩,⟨12638428726608,24460671818956⟩,⟨-17195572703137,-1184941596245⟩,⟨-13073427525511,8293592859418⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨61122018325,65528681271⟩,⟨-533817603102,-412231129069⟩,⟨421111847581,573183375538⟩,⟨4041116635708,8167829874263⟩,⟨-5793160681880,-44487307814⟩,⟨-4886174530270,2894049065571⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380031812232,380596221293⟩,⟨1791818225,21033118116⟩,⟨-23661840938,-340288286⟩,⟨-625368271574,143889430005⟩,⟨-320965901773,659957632429⟩,⟨-715102701179,558092970901⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176399953492,3181117424130⟩,⟨-176061099017,-14954250746⟩,⟨2839995867,198065246309⟩,⟨-1204308815949,5254234168603⟩,⟨-5546205647285,2686669977089⟩,⟨-4671601920964,6010546396248⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨176576555681,189588199439⟩,⟨-1554939017458,-1191733620717⟩,⟨1216715863256,1670143844915⟩,⟨11613897313967,24115341142770⟩,⟨-17279313340730,24807660590⟩,⟨-14412968937062,8937812254547⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨354937380769,379325328399⟩,⟨-3117333816175,-2423557765786⟩,⟨2480342007040,3343671443261⟩,⟨24252326040575,48576012961726⟩,⟨-34474886043867,-1160133935655⟩,⟨-27486396462573,17231405113965⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518749932007,527193126238⟩,⟨-38870535174,199923611598⟩,⟨-233434018356,64088704736⟩,⟨-5800947094622,2473432639021⟩,⟨-4536939890698,6854041918684⟩,⟨-8179952872441,7153080668264⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356317510927,365051969108⟩,⟨-40373531158,207654001313⟩,⟨-242460145485,66566804547⟩,⟨-6032905954498,2608445716582⟩,⟨-4758341659555,7131687040307⟩,⟨-8510982237746,7483345858243⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712635021854,730103938216⟩,⟨-80747062316,415308002626⟩,⟨-484920290970,133133609094⟩,⟨-12065811908996,5216891433164⟩,⟨-9516683319110,14263374080614⟩,⟨-17021964475492,14966691716486⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523327156197,1525220424318⟩,⟨-33018822592,31373133770⟩,⟨-38169077182,39901927070⟩,⟨-1253544139196,1313412661228⟩,⟨-1663879247112,1612679522392⟩,⟨-2108363660557,2147956799406⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨987325876164,1012785504320⟩,⟨-133936047004,596939477426⟩,⟨-698016925092,211176169478⟩,⟨-17594780942869,8132607171159⟩,⟨-14334464097802,20886360493489⟩,⟨-25047730559866,22221459884211⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67705118066,67822207666⟩,⟨12416175688,16404794726⟩,⟨-17571664180,-12736724042⟩,⟨-378160526867,-218854193078⟩,⟨106694193056,309903710594⟩,⟨-225015217719,38815503479⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49863802732,50576117506⟩,⟨261633124805,269683431755⟩,⟨34127514376,39242768545⟩,⟨-1392700717676,-1190572816294⟩,⟨-301265823015,-109404824952⟩,⟨-282711475020,-73048466511⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133135314334,2135782491420⟩,⟨-370981722718,-280608132988⟩,⟨287852591968,397369571360⟩,⟨5035152744289,8654677737220⟩,⟨-7117253257842,-2504643143628⟩,⟨-779815643885,5204123665817⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2971171325456,2976703784816⟩,⟨-775572444208,-586274227065⟩,⟨601410066300,830738742212⟩,⟨10558499822527,18160781690859⟩,⟨-14951441281265,-5272504765931⟩,⟨-1589708718160,10956994526359⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134745187875,136924536857⟩,⟨671326593089,703524919667⟩,⟨119496039614,144454714154⟩,⟨-3672074509981,-2660882728268⟩,⟨-1387936010101,-349190689607⟩,⟨-801174202267,365911282623⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8829139373881,8971940584151⟩,⟨-46843853040438,-43288341095250⟩,⟨-9618444509445,-7705318656513⟩,⟨596054844768692,733660858524889⟩,⟨98073173877595,192853716178692⟩,⟨-10914930908244,73968850405088⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7928281564173,8264261277190⟩,⟨-44241861889212,-34000544270159⟩,⟨-14555541885721,-5195943638972⟩,⟨340801445721184,753565938739666⟩,⟨-43120701368058,378983433858082⟩,⟨-218136489539711,261672422636391⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15856563128346,16528522554380⟩,⟨-88483723778424,-68001088540318⟩,⟨-29111083771442,-10391887277944⟩,⟨681602891442368,1507131877479332⟩,⟨-86241402736116,757966867716164⟩,⟨-436272979079422,523344845272782⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10909882818222,10952333724170⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145760,2173453475298114⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9810371190446,9852822096394⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145775,2173453475298112⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2406362562496,2411110103296⟩,⟨-12227224809080,-12080350374972⟩,⟨0,0⟩,⟨103760055435140,110865974497594⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7512290922568,7607865528498⟩,⟨-46821885020786,-45472418650088⟩,⟨-21035919357157,-20490657786775⟩,⟨550495415899599,576321678843455⟩,⟨299389641443526,311568336894929⟩,⟨111781362266846,116329580627633⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6412779294792,6508353900722⟩,⟨-46821885020786,-45472418650088⟩,⟨-21035919357158,-20490657786774⟩,⟨550495415899604,576321678843453⟩,⟨299389641443528,311568336894929⟩,⟨111781362266846,116329580627633⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1938908112640,1955174109568⟩,⟨-8027908750381,-7682042773225⟩,⟨-3606741612489,-3461661249664⟩,⟨34385381694093,45141280878319⟩,⟨24244392210079,29234508896646⟩,⟨7052937894063,9046878720663⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99256358666,99685855397⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135647164695,137668819226⟩,⟨688391387870,695846084940⟩,⟨310393135430,312437586659⟩,⟨-1739706366693,-1725980926276⟩,⟨-1563309375492,-1555415695356⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4345270675136,4366284212864⟩,⟨-20255133559461,-19762393148197⟩,⟨-3606741612489,-3461661249664⟩,⟨138145437129233,156007255375913⟩,⟨24244392210079,29234508896646⟩,⟨7052937894063,9046878720663⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨709874761538,758650656798⟩,⟨-6234667632350,-4847115531572⟩,⟨4960684014080,6687342886522⟩,⟨48504652081150,97152025923452⟩,⟨-68949772087734,-2320267871310⟩,⟨-54972792925146,34462810227930⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5055145436674,5124934869662⟩,⟨-26489801191811,-24609508679769⟩,⟨1353942401591,3225681636858⟩,⟨186650089210383,253159281299365⟩,⟨-44705379877655,26914241025336⟩,⟨-47919855031083,43509688948593⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨456343812921,464645851331⟩,⟨1634552777742,1874366606888⟩,⟨122224621577,292452417133⟩,⟨-35742673130304,-26456228401969⟩,⟨-2972119326093,5018171462624⟩,⟨-4344594107601,3944751880134⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35947786954,38040727740⟩,⟨-765308254199,-723273515660⟩,⟨328085346598,330673870673⟩,⟨8934091650286,9651072922213⟩,⟨-6659570832821,-6593775017748⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨492291599875,502686579071⟩,⟨869244523543,1151093091228⟩,⟨450309968175,623126287806⟩,⟨-26808581480018,-16805155479756⟩,⟨-9631690158914,-1575603555124⟩,⟨-4344594107601,3944751880134⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501398014948,502387228948⟩,⟨2512147284185,2552733193796⟩,⟨0,0⟩,⟨2027158573049,4364694834823⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨224494243368,229686809225⟩,⟨1521172165904,1693041835855⟩,⟨205349828460,284717943046⟩,⟨-7369631281495,-322989760189⟩,⟨-3372036340289,728205726706⟩,⟨-1985125522535,1802430202541⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-758650656798,-709874761538⟩,⟨4847115531572,6234667632350⟩,⟨-6687342886522,-4960684014080⟩,⟨-97152025923452,-48504652081150⟩,⟨2320267871310,68949772087734⟩,⟨-34462810227930,54972792925146⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3586620018338,3656409451326⟩,⟨-15408018027889,-13527725515847⟩,⟨-10294084499011,-8422345263744⟩,⟨40993411205781,107502603294763⟩,⟨26564660081389,98184280984380⟩,⟨-27409872333867,64019671645809⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442482665972,457815596539⟩,⟨316317422105,645105129158⟩,⟨-276406558355,-61400259⟩,⟨-20230488046993,-9108972123881⟩,⟨-12814617293117,-1872244068594⟩,⟨-10450072170628,2117332006509⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨317809460508,321852769568⟩,⟨1948197165464,1955928106600⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-321852769568,-317809460508⟩,⟨-1955928106600,-1948197165464⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨777658858208,781702167268⟩,⟨-1955928106600,-1948197165464⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1371344359582,1390038813803⟩,⟨-9185545116456,-8868831992796⟩,⟨-4126839110292,-3996448984409⟩,⟨51543215321375,60655167380917⟩,⟨33292569844793,37526849050974⟩,⟨10516218321666,12197065474677⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1390038813803,-1371344359582⟩,⟨8868831992796,9185545116456⟩,⟨3996448984409,4126839110292⟩,⟨-60655167380917,-51543215321375⟩,⟨-37526849050974,-33292569844793⟩,⟨-12197065474677,-10516218321666⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-290527186027,-271832731806⟩,⟨8868831992796,9185545116456⟩,⟨3996448984409,4126839110292⟩,⟨-60655167380917,-51543215321375⟩,⟨-37526849050974,-33292569844793⟩,⟨-12197065474677,-10516218321666⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13355845414,-11890442183⟩,⟨417988581771,455407588601⟩,⟨58714326108,81194483481⟩,⟨-4883835385003,-4215434290623⟩,⟨1616569788196,2063086574390⟩,⟨2630202593346,2838249294592⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429126820558,445925154356⟩,⟨734306003876,1100512717759⟩,⟨-217692232247,81133083222⟩,⟨-25114323431996,-13324406414504⟩,⟨-11198047504921,190842505796⟩,⟨-7819869577282,4955581301101⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99685855397,-99256358666⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4341647844,4582665371⟩,⟨27030093559,29424611100⟩,⟨39624999436,39835402372⟩,⟨-301556364742,-290285431025⟩,⟨250784818133,251900503000⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9502017593,10049289610⟩,⟨8195388986,16823241776⟩,⟨86722243560,87354729775⟩,⟨-906001011072,-767191825821⟩,⟨105867709348,117030113883⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1474437138092,1492917918278⟩,⟨-7694726634216,-7373493656839⟩,⟨-1453260341542,-1379298400774⟩,⟨107446634972181,115284273243739⟩,⟨22695637178093,24598822990208⟩,⟨5040199280812,5510853780673⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12742136846,13644934848⟩,⟨-59338117840,-40879374280⟩,⟨103011427702,106690389347⟩,⟨-537080105213,-85045365388⟩,⟨-295467261619,-208122173198⟩,⟨-187361608022,-167211999784⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13644934848,-12742136846⟩,⟨40879374280,59338117840⟩,⟨-106690389347,-103011427702⟩,⟨85045365388,537080105213⟩,⟨208122173198,295467261619⟩,⟨167211999784,187361608022⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113330790245,-111998495512⟩,⟨-837870934482,-818553197462⟩,⟨-106690389347,-103011427702⟩,⟨2284068620940,2736103360765⟩,⟨208122173198,295467261619⟩,⟨167211999784,187361608022⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨84811253814,89881444557⟩,⟨-592063596668,-550366305998⟩,⟨608242704344,629886747484⟩,⟨3202528766634,3906559636898⟩,⟨-3720033482891,-3250388025321⟩,⟨-2574067604671,-2348025465078⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨113731277771,122041109626⟩,⟨-1432922997611,-1306794513896⟩,⟨696849832314,748868101302⟩,⟨19964187333103,23015331814769⟩,⟨-7018157852803,-5644293424274⟩,⟨-4771377361030,-4224228930173⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-122041109626,-113731277771⟩,⟨1306794513896,1432922997611⟩,⟨-748868101302,-696849832314⟩,⟨-23015331814769,-19964187333103⟩,⟨5644293424274,7018157852803⟩,⟨4224228930173,4771377361030⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨977470518150,985780350005⟩,⟨1306794513896,1432922997611⟩,⟨-748868101302,-696849832314⟩,⟨-23015331814769,-19964187333103⟩,⟨5644293424274,7018157852803⟩,⟨4224228930173,4771377361030⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120590906917,123428632653⟩,⟨773202607196,803284105392⟩,⟨182175746572,194149042328⟩,⟨-2805145166291,-2183690559542⟩,⟨-810290797315,-533143885060⟩,⟨-219286395072,-107592925112⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11408395036,11681429913⟩,⟨166758994258,172725003956⟩,⟨20985907982,21993957738⟩,⟨654735378716,811661181904⟩,⟨92467953924,120205015160⟩,⟨-19322187404,-13359846393⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164525714427,175602306431⟩,⟨1464839535321,1890935748313⟩,⟨-6634500138,222801528523⟩,⟨-11285788033197,7586485736441⟩,⟨-5925829367504,6985776861376⟩,⟨-6090154175321,4970760075886⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-175602306431,-164525714427⟩,⟨-1890935748313,-1464839535321⟩,⟨-222801528523,6634500138⟩,⟨-7586485736441,11285788033197⟩,⟨-6985776861376,5925829367504⟩,⟨-4970760075886,6090154175321⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48891936937,65161094798⟩,⟨-369763582409,228202300534⟩,⟨-17451700063,291352443184⟩,⟨-14956117017936,10962798273008⟩,⟨-10357813201665,6654035094210⟩,⟨-6955885598421,7892584377862⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27961886087849,29391357536711⟩,⟨-278023941696045,-230701205898612⟩,⟨-105984643033694,-68247540805797⟩,⟨2648061029436860,4650703364365938⟩,⟨482981189164732,2290107193452871⟩,⟨-608641031650046,1257607568987315⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13226023685,13855812867⟩,⟨169604761380,180349632066⟩,⟨39960902536,43589445024⟩,⟨457670538717,694730495479⟩,⟨74297853738,166736818144⟩,⟨11135457927,44963821384⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336353484886,370383668211⟩,⟨809651563921,2045872774301⟩,⟨-319342849227,344252268758⟩,⟨-47714258304783,6004758641065⟩,⟨-20707167939321,14404378705393⟩,⟨-15790166229128,12089236619070⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370383668211,-336353484886⟩,⟨-2045872774301,-809651563921⟩,⟨-344252268758,319342849227⟩,⟨-6004758641065,47714258304783⟩,⟨-14404378705393,20707167939321⟩,⟨-12089236619070,15790166229128⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58743152347,109571669470⟩,⟨-1311566770425,290861153838⟩,⟨-561944501005,400475932449⟩,⟨-31119082073061,34389851890279⟩,⟨-25602426210314,20898010445117⟩,⟨-19909106196352,20745747530229⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234903523361,237354674623⟩,⟨1566282703172,1574596393702⟩,⟨310393135430,312437586659⟩,⟨-3938729622245,-3925004181828⟩,⟨-1563309375492,-1555415695356⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1703656855780,-1615181840284⟩,⟨-5668652218949,-2684382807125⟩,⟨-545295521077,1515013466277⟩,⟨-21156621632698,106557425523258⟩,⟨-61017708453824,44100613673280⟩,⟨-49584478770142,53434376031333⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-191248578830,-177147960999⟩,⟨-1881011908756,-1430248600833⟩,⟨-362041125813,-97544140779⟩,⟨-7449991240778,12532926625689⟩,⟨-7465858857442,6868224510814⟩,⟨-5600758852810,6873231148113⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43654944531,60206713624⟩,⟨-314729205584,144347792869⟩,⟨-51647990383,214893445880⟩,⟨-11388720863023,8607922443861⟩,⟨-9029168232934,5312808815458⟩,⟨-5951915714476,6522760474583⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2612129264,6493619314⟩,⟨-114576996290,39978966257⟩,⟨-35042040338,52768358550⟩,⟨-3879108840979,4012719512640⟩,⟨-3031722921450,2167653922966⟩,⟨-2170886510129,2228242511502⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1733273331,3296780384⟩,⟨-34467686692,15808302538⟩,⟨-5656248990,23534136120⟩,⟨-1329877562461,1122878883186⟩,⟨-1111856890150,638258195080⟩,⟨-672014902307,798342016449⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3056500393,5862402443⟩,⟨-85362062901,16000652952⟩,⟨-20872527404,36391910280⟩,⟨-2541453918185,2635398684194⟩,⟨-2162594688891,1376983659018⟩,⟨-1338271035998,1483862861870⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5862402443,-3056500393⟩,⟨-16000652952,85362062901⟩,⟨-36391910280,20872527404⟩,⟨-2635398684194,2541453918185⟩,⟨-1376983659018,2162594688891⟩,⟨-1483862861870,1338271035998⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3250273179,3437118921⟩,⟨-130577649242,125341029158⟩,⟨-71433950618,73640885954⟩,⟨-6514507525173,6554173430825⟩,⟨-4408706580468,4330248611857⟩,⟨-3654749371999,3566513547500⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48891936937,65161094798⟩,⟨-369763582409,228202300534⟩,⟨-17451700063,291352443184⟩,⟨-14956117017936,10962798273008⟩,⟨-10357813201665,6654035094210⟩,⟨-6955885598421,7892584377862⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3250273179,3437118921⟩,⟨-130577649242,125341029158⟩,⟨-71433950618,73640885954⟩,⟨-6514507525173,6554173430825⟩,⟨-4408706580468,4330248611857⟩,⟨-3654749371999,3566513547500⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (103/1024) u, BivariateJet2.affineZ (115/1024) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000007

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000008Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2149422265088,-2149422225664⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2149422265024,-2149422225664⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-167853814912,-167853814848⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-167853814912,-167853814848⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨80802336576,80802336640⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-87214805440,-87214805376⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨80802460480,80802460544⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-87214949824,-87214949760⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6412489344,-6412489280⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6412468864,-6412468800⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨168017141952,168017142016⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨168017410240,168017410304⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1981568410816,1981568449408⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1981568410880,1981568449472⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2518909148864,-2518909091008⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2156560996736,-2156560957184⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2142324285568,-2142324246336⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-169028908736,-169028908672⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-166680854144,-166680854080⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨78212437504,78212437568⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-84204977088,-84204977024⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨83415604288,83415604352⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-90267389888,-90267389824⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-6851785600,-6851785536⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-5992539520,-5992539456⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨162417414592,162417414656⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨173682994112,173682994176⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1973295337664,1973295376256⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1989880103168,1989880141760⟩



end LaneCBRB2Cell000008Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000008
open Set LaneCBRB2Cell000008Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111024904601,111024904602⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111024904602,-111024904601⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438730909286,438730909287⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨44644297604,44644297606⟩,⟨-111883898061,-111883898060⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨155669202205,155669202208⟩,⟨987627729715,987627729716⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44644297603,44644297607⟩,⟨-111883898061,-111883898060⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2149422265088,-2149422225664⟩,⟨6975741876576,6975741876719⟩,⟨3098812927557,3098812927625⟩,⟨-44256898700596,-44256898698782⟩,⟨-27426101860000,-27426101859018⟩,⟨-8733551622220,-8733551621839⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-304315880580,-304315874992⟩,⟨-943074027561,-943073992105⟩,⟨-418938951579,-418938935826⟩,⟨6265905642393,6265905643042⟩,⟨3833395100449,3833395140217⟩,⟨1236498986468,1236498986607⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨304315874992,304315880580⟩,⟨943073992105,943074027561⟩,⟨418938935826,418938951579⟩,⟨-6265905643042,-6265905642393⟩,⟨-3833395140217,-3833395100449⟩,⟨-1236498986607,-1236498986468⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-155669202208,-155669202205⟩,⟨-987627729716,-987627729715⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨943842425568,943842425571⟩,⟨-987627729716,-987627729715⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-167853814912,-167853814848⟩,⟨-1150518501099,-1150518501092⟩,⟨-511091388943,-511091388939⟩,⟨-1203891607812,-1203891607797⟩,⟨746054396789,746054396802⟩,⟨-237573119968,-237573119963⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-144089018985,-144089018928⟩,⟨-836854351892,-836854351824⟩,⟨-371753303092,-371753303060⟩,⟨1033444255167,1033444255200⟩,⟨1390741660067,1390741660155⟩,⟨203937442886,203937442897⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144089018928,144089018985⟩,⟨836854351824,836854351892⟩,⟨371753303060,371753303092⟩,⟨-1033444255200,-1033444255167⟩,⟨-1390741660155,-1390741660067⟩,⟨-203937442897,-203937442886⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨448404893920,448404899565⟩,⟨1779928343929,1779928379453⟩,⟨790692238886,790692254671⟩,⟨-7299349898242,-7299349897560⟩,⟨-5224136800372,-5224136760516⟩,⟨-1440436429504,-1440436429354⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨808190846064,808190857613⟩,⟨4183923289453,4183923382921⟩,⟨790692238886,790692254671⟩,⟨-19411137062444,-19411137061255⟩,⟨-5224136800372,-5224136760516⟩,⟨-1440436429504,-1440436429354⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89288595206,89288595214⟩,⟨-223767796122,-223767796120⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13539532307761,13539532308976⟩,⟨33931671763248,33931671769642⟩,⟨-133056440355757,-133056440331572⟩,⟨170073577502948,170073577551776⟩,⟨-333455200593201,-333455200346327⟩,⟨2615159211010724,2615159211726691⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9952169485695,9952169628805⟩,⟨76462703019794,76462704536507⟩,⟨-88065822208737,-88065820598114⟩,⟨144217860511136,144217868187165⟩,⟨-791347934932802,-791347918857526⟩,⟨1713152874904827,1713152906758727⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨83845477376,83845610752⟩,⟨-638795684055,-638793614179⟩,⟨735729729709,735732112547⟩,⟨8487812605054,8487864516809⟩,⟨-4552391023373,-4552314368890⟩,⟨-1454712939328,-1454602991181⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1183357105152,1183357238528⟩,⟨-638795684055,-638793614179⟩,⟨735729729709,735732112547⟩,⟨8487812605054,8487864516809⟩,⟨-4552391023373,-4552314368890⟩,⟨-1454712939328,-1454602991181⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨80802336576,80802460544⟩,⟨-593534512393,-593532522277⟩,⟨683600324886,683602615942⟩,⟨7566017289234,7566068560323⟩,⟨-3860818827662,-3860744653637⟩,⟨-1776659116243,-1776553957172⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨86964081765,86964224989⟩,⟨-685740473832,-685738035818⟩,⟨789797907406,789800714162⟩,⟨9456402929481,9456468347244⟩,⟨-5284107013498,-5284015332353⟩,⟨-1104196277059,-1104068610259⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-83845610752,-83845477376⟩,⟨638793614179,638795684055⟩,⟨-735732112547,-735729729709⟩,⟨-8487864516809,-8487812605054⟩,⟨4552314368890,4552391023373⟩,⟨1454602991181,1454712939328⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1015666017024,1015666150400⟩,⟨638793614179,638795684055⟩,⟨-735732112547,-735729729709⟩,⟨-8487864516809,-8487812605054⟩,⟨4552314368890,4552391023373⟩,⟨1454602991181,1454712939328⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-87214949824,-87214805376⟩,⟨691527433755,691529765316⟩,⟨-796468523230,-796465839091⟩,⟨-9623490199409,-9623429862752⟩,⟨5429047597612,5429134604372⟩,⟨997734694688,997857814789⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-80564197875,-80564053861⟩,⟨588123276221,588125761979⟩,⟨-677373094476,-677370232738⟩,⟨-7412839934119,-7412772485536⟩,⟨3728474698406,3728568524902⟩,⟨1872158191345,1872288000382⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6399883890,6400171128⟩,⟨-97617197611,-97612273839⟩,⟨112424812930,112430481424⟩,⟨2043562995362,2043695861708⟩,⟨-1555632315092,-1555446807451⟩,⟨767961914286,768219390123⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3199941945,3200085564⟩,⟨-48808598806,-48806136919⟩,⟨56212406465,56215240712⟩,⟨1021781497681,1021847930854⟩,⟨-777816157546,-777723403725⟩,⟨383980957143,384109695062⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3200085564,-3199941945⟩,⟨48806136919,48808598806⟩,⟨-56215240712,-56212406465⟩,⟨-1021847930854,-1021781497681⟩,⟨777723403725,777816157546⟩,⟨-384109695062,-383980957143⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758923298052,758923460935⟩,⟨48806136919,48808598806⟩,⟨-56215240712,-56212406465⟩,⟨-1021847930854,-1021781497681⟩,⟨777723403725,777816157546⟩,⟨-384109695062,-383980957143⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6393806030,6393826373⟩,⟨-97425462220,-97424991554⟩,⟨112209109660,112209651574⟩,⟨2036762418837,2036777205577⟩,⟨-1549197811716,-1549179477522⟩,⟨762751261046,762774760452⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6393826373,-6393806030⟩,⟨97424991554,97425462220⟩,⟨-112209651574,-112209109660⟩,⟨-2036777205577,-2036762418837⟩,⟨1549179477522,1549197811716⟩,⟨-762774760452,-762751261046⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1093117801403,1093117821746⟩,⟨97424991554,97425462220⟩,⟨-112209651574,-112209109660⟩,⟨-2036777205577,-2036762418837⟩,⟨1549179477522,1549197811716⟩,⟨-762774760452,-762751261046⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6412489344,-6412468800⟩,⟨97994844579,97995319823⟩,⟨-112865984340,-112865437155⟩,⟨-2057424604343,-2057409608270⟩,⟨1568300076352,1568318644342⟩,⟨-778822163702,-778798400226⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3206244672,-3206234400⟩,⟨48997422289,48997659912⟩,⟨-56432992170,-56432718577⟩,⟨-1028712302172,-1028704804135⟩,⟨784150038176,784159322171⟩,⟨-389411081851,-389399200113⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3206234400,3206244672⟩,⟨-48997659912,-48997422289⟩,⟨56432718577,56432992170⟩,⟨1028704804135,1028712302172⟩,⟨-784159322171,-784150038176⟩,⟨389399200113,389411081851⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765329618016,765329647552⟩,⟨-48997659912,-48997422289⟩,⟨56432718577,56432992170⟩,⟨1028704804135,1028712302172⟩,⟨-784159322171,-784150038176⟩,⟨389399200113,389411081851⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273279450350,273279455437⟩,⟨24356247888,24356365555⟩,⟨-28052412894,-28052277415⟩,⟨-509194301395,-509190604709⟩,⟨387294869380,387299452929⟩,⟨-190693690113,-190687815261⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530659236032,1530659295104⟩,⟨-97995319824,-97994844578⟩,⟨112865437154,112865984340⟩,⟨2057409608270,2057424604344⟩,⟨-1568318644342,-1568300076352⟩,⟨778798400226,778822163702⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1190278733950,1190278890257⟩,⟨-748617168611,-748614546266⟩,⟨862215848053,862218867001⟩,⟨10888699225089,10888769147531⟩,⟨-6419608619308,-6419509931025⟩,⟨-455660223184,-455522341624⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1281045840124,1281046152738⟩,⟨-1497234337222,-1497229092532⟩,⟨1724431696106,1724437734002⟩,⟨21777398450186,21777538295053⟩,⟨-12839217238611,-12839019862054⟩,⟨-911320294839,-911044834779⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨168017141952,168017410304⟩,⟨-1285064524406,-1285059709335⟩,⟨1480065879844,1480071423305⟩,⟨17189435033710,17189570878029⟩,⟨-9289965369898,-9289780313416⟩,⟨-2774528561625,-2774277021318⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57873227176,57873331659⟩,⟨-437198521036,-437196804040⟩,⟨503540861022,503542837688⟩,⟨5723962956009,5724008279144⟩,⟨-3017604748243,-3017540491027⟩,⟨-1108619841192,-1108529834988⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380439555279,380439577044⟩,⟨9550611273,9550894965⟩,⟨-11000231023,-10999904387⟩,⟨-201843107078,-201834154697⟩,⟨154364134629,154375206979⟩,⟨-77661567895,-77647413450⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177707821588,3177708003386⟩,⟨-79776024729,-79773645999⟩,⟨91879195321,91881934137⟩,⟨1689870836269,1689946044608⟩,⟨-1294067436771,-1293974530107⟩,⟨653880754747,653999373640⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨167259901588,167260213126⟩,⟨-1267750252467,-1267745085086⟩,⟨1460123783637,1460129732566⟩,⟨16695261093217,16695399288493⟩,⟨-8862389263498,-8862195575765⟩,⟨-3085459042596,-3085189586957⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨335277043540,335277623430⟩,⟨-2552814776873,-2552804794421⟩,⟨2940189663481,2940201155871⟩,⟨33884696126927,33884970166522⟩,⟨-18152354633396,-18151975889181⟩,⟨-5859987604221,-5859466608275⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523836726939,523836951796⟩,⟨67375575590,67378988624⟩,⟨-77603663228,-77599733968⟩,⟨-1406301324519,-1406208875397⟩,⟨1068635580660,1068764358662⟩,⟨-524505639106,-524327226402⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361571343500,361571576307⟩,⟨69757644317,69761192992⟩,⟨-80347364036,-80343278610⟩,⟨-1451535436432,-1451438952071⟩,⟨1101249899357,1101383990814⟩,⟨-537098777526,-536913338236⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨723142687000,723143152614⟩,⟨139515288634,139522385984⟩,⟨-160694728072,-160686557220⟩,⟨-2903070872864,-2902877904142⟩,⟨2202499798714,2202767981628⟩,⟨-1074197555052,-1073826676472⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524265409659,1524265489074⟩,⟨-570328270,-569382358⟩,⟨655785580,656874680⟩,⟨20632402693,20662185507⟩,⟨-19139166820,-19102264636⟩,⟨16023639774,16070902656⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002500888755,1002501586472⟩,⟨193036521158,193046992737⟩,⟨-222341624731,-222329569205⟩,⟨-4011135133482,-4010847564919⟩,⟨3040929081845,3041325589336⟩,⟨-1478825648782,-1478279998588⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67922572255,67922574785⟩,⟨12107306310,12107365030⟩,⟨-13944642196,-13944574588⟩,⟨-252037561197,-252035708462⟩,⟨191278512290,191280806332⟩,⟨-93360972681,-93358036744⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49926166991,49926169565⟩,⟨267362198489,267362257182⟩,⟨38595242941,38595295579⟩,⟨-1292243523345,-1292241665164⟩,⟨-226480043465,-226478039892⟩,⟨-177663857215,-177661597223⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130871231975,2130871396447⟩,⟨-272843766954,-272842433216⟩,⟨314245924178,314247459812⟩,⟨5745816467903,5745858611269⟩,⟨-4386714588474,-4386662526866⟩,⟨2191543119290,2191609591183⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966442236372,2966442579821⟩,⟨-569749565329,-569746758243⟩,⟨656205101535,656208333555⟩,⟨12034830702273,12034919523872⟩,⟨-9202304099942,-9202194622868⟩,⟨4624744024534,4624883478112⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134698976091,134698998632⟩,⟨695462499241,695462869906⟩,⟨133925245120,133925547487⟩,⟨-3217039469227,-3217028564925⟩,⟨-889323067507,-889311651806⟩,⟨-223263757884,-223250972200⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8975017126277,8975018628189⟩,⟨-46338824494136,-46338784287652⟩,⟨-8923484931870,-8923461798529⟩,⟨692853405583579,692854954163962⟩,⟨151400185608237,151401269480622⟩,⟨32619655386827,32620601310479⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8183144605649,8183151670324⟩,⟨-40674639410308,-40674487605671⟩,⟨-9951079868953,-9950954404383⟩,⟨582708708771096,582713809973179⟩,⟨170667627786866,170672558097754⟩,⟨21279124307949,21284668525093⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16366289211298,16366303340648⟩,⟨-81349278820616,-81348975211342⟩,⟨-19902159737906,-19901908808766⟩,⟨1165417417542192,1165427619946358⟩,⟨341335255573732,341345116195508⟩,⟨42558248615898,42569337050186⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10888780530353,10888780530452⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239700,2135836853297982⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9789268902577,9789268902676⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239713,2135836853297977⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2403994945600,2403995003456⟩,⟨-12111787164150,-12111787163733⟩,⟨0,0⟩,⟨106474359377039,106474359411671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7765992260943,7765992261094⟩,⟨-49270563458766,-49270563456798⟩,⟨-21887314882869,-21887314881967⟩,⟨625184352953676,625184352991425⟩,⟨332575976947666,332575976966921⟩,⟨123372400240900,123372400248663⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6666480633167,6666480633318⟩,⟨-49270563458766,-49270563456798⟩,⟨-21887314882870,-21887314881967⟩,⟨625184352953683,625184352991420⟩,⟨332575976947669,332575976966919⟩,⟨123372400240900,123372400248663⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1981568410816,1981568449472⟩,⟨-8126260378034,-8126260377485⟩,⟨-3609904316663,-3609904316414⟩,⟨43053007082490,43053007102427⟩,⟨28172156251801,28172156261353⟩,⟨8495978500159,8495978504183⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99813991382,99813991384⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133629507577,133629507581⟩,⟨707970440279,707970440287⟩,⟨314499588929,314499588935⟩,⟨-1774257784753,-1774257784749⟩,⟨-1576346446732,-1576346446720⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4385563356416,4385563452928⟩,⟨-20238047542184,-20238047541218⟩,⟨-3609904316663,-3609904316414⟩,⟨149527366459529,149527366514098⟩,⟨28172156251801,28172156261353⟩,⟨8495978500159,8495978504183⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨670554087080,670555246860⟩,⟨-5105629553746,-5105609588842⟩,⟨5880379326962,5880402311742⟩,⟨67769392253854,67769940333044⟩,⟨-36304709266792,-36303951778362⟩,⟨-11719975208442,-11718933216550⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5056117443496,5056118699788⟩,⟨-25343677095930,-25343657130060⟩,⟨2270475010299,2270497995328⟩,⟨217296758713383,217297306847142⟩,⟨-8132553014991,-8131795517009⟩,⟨-3223996708283,-3222954712367⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458995839773,458995953829⟩,⟨1734312208637,1734315023782⟩,⟨206114394232,206116480825⟩,⟨-30836857868059,-30836773727839⟩,⟨1073669914140,1073757023182⟩,⟨-292675376534,-292580783829⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33254027415,33254029294⟩,⟨-671027658513,-671027649047⟩,⟨326795816458,326795834885⟩,⟨8362936032156,8362936057490⟩,⟨-6594360098773,-6594360006268⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨492249867188,492249983123⟩,⟨1063284550124,1063287374735⟩,⟨532910210690,532912315710⟩,⟨-22473921835903,-22473837670349⟩,⟨-5520690184633,-5520602983086⟩,⟨-292675376534,-292580783829⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502882001783,502882013886⟩,⟨2533615820870,2533615942923⟩,⟨0,0⟩,⟨3256741201878,3256744126778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225139591374,225139649818⟩,⟨1620609249911,1620610875299⟩,⟨243736352351,243737320988⟩,⟨-3920551109428,-3920497460869⟩,⟨-1296999523386,-1296954669596⟩,⟨-133860505927,-133817238979⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-670555246860,-670554087080⟩,⟨5105609588842,5105629553746⟩,⟨-5880402311742,-5880379326962⟩,⟨-67769940333044,-67769392253854⟩,⟨36303951778362,36304709266792⟩,⟨11718933216550,11719975208442⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3715008109556,3715009365848⟩,⟨-15132437953342,-15132417987472⟩,⟨-9490306628405,-9490283643376⟩,⟨81757426126485,81757974260244⟩,⟨64476108030163,64476865528145⟩,⟨20214911716709,20215953712625⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451504733359,451504886057⟩,⟨552950673187,552953908751⟩,⟨-90782558095,-90779405200⟩,⟨-15545826695078,-15545732337814⟩,⟨-7929187017873,-7929072642651⟩,⟨-4155312617924,-4155172429291⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨311338404410,311338404416⟩,⟨1975255459430,1975255459432⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-311338404416,-311338404410⟩,⟨-1975255459432,-1975255459430⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨788173223360,788173223366⟩,⟨-1975255459432,-1975255459430⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1420466252658,1420466280380⟩,⟨-9385080133257,-9385080063368⟩,⟨-4169106047457,-4169106016404⟩,⟨60059490095500,60059490112030⟩,⟨37128320980508,37128321065731⟩,⟨11851997599269,11851997602612⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1420466280380,-1420466252658⟩,⟨9385080063368,9385080133257⟩,⟨4169106016404,4169106047457⟩,⟨-60059490112030,-60059490095500⟩,⟨-37128321065731,-37128320980508⟩,⟨-11851997602612,-11851997599269⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-320954652604,-320954624882⟩,⟨9385080063368,9385080133257⟩,⟨4169106016404,4169106047457⟩,⟨-60059490112030,-60059490095500⟩,⟨-37128321065731,-37128320980508⟩,⟨-11851997602612,-11851997599269⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13031963162,-13031962035⟩,⟨413729105192,413729110887⟩,⟨41212918547,41212930887⟩,⟨-4348651099039,-4348651083907⟩,⟨2134033275654,2134033338034⟩,⟨2845906454935,2845906479905⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438472770197,438472924022⟩,⟨966679778379,966683019638⟩,⟨-49569639548,-49566474313⟩,⟨-19894477794117,-19894383421721⟩,⟨-5795153742219,-5795039304617⟩,⟨-1309406162989,-1309265949386⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99813991384,-99813991382⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4052822565,4052822567⟩,⟨25471388767,25471388773⟩,⟨39828121951,39828121953⟩,⟨-267865785636,-267865785625⟩,⟨250313839737,250313839741⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8861175012,8861175230⟩,⟨11046873175,11046874554⟩,⟨87081028926,87081031027⟩,⟨-754366195158,-754366180563⟩,⟨108560442911,108560456131⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1495841988593,1495842009969⟩,⟨-7743824856652,-7743824462327⟩,⟨-1463454699166,-1463454628122⟩,⟨116105160078651,116105168127427⟩,⟨24821422730626,24821424371358⟩,⟨5529572233666,5529572547243⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12055277376,12055277846⟩,⟨-47380137647,-47380130841⟩,⟨106676025958,106676031374⟩,⟨-246177138147,-246176988388⟩,⟨-280279540147,-280279453326⟩,⟨-187246569864,-187246549392⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12055277846,-12055277376⟩,⟨47380130841,47380137647⟩,⟨-106676031374,-106676025958⟩,⟨246176988388,246177138147⟩,⟨280279453326,280279540147⟩,⟨187246549392,187246569864⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-111869269230,-111869268758⟩,⟨-830081687733,-830081680925⟩,⟨-106676031374,-106676025958⟩,⟨2445200243940,2445200393699⟩,⟨280279453326,280279540147⟩,⟨187246549392,187246569864⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨80459112589,80459114167⟩,⟨-531596732937,-531596728948⟩,⟨644116578808,644116594259⟩,⟨3401934587837,3401934588932⟩,⟨-3712905583435,-3712905544030⟩,⟨-2535904253808,-2535904253406⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨109461433544,109461437256⟩,⟨-1289887235290,-1289887179557⟩,⟨769203648279,769203689123⟩,⟨20612477104172,20612478364911⟩,⟨-7063835168612,-7063834507645⟩,⟨-4760002916143,-4760002711041⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-109461437256,-109461433544⟩,⟨1289887179557,1289887235290⟩,⟨-769203689123,-769203648279⟩,⟨-20612478364911,-20612477104172⟩,⟨7063834507645,7063835168612⟩,⟨4760002711041,4760002916143⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨990050190520,990050194232⟩,⟨1289887179557,1289887235290⟩,⟨-769203689123,-769203648279⟩,⟨-20612478364911,-20612477104172⟩,⟨7063834507645,7063835168612⟩,⟨4760002711041,4760002916143⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120326075771,120326076227⟩,⟨794255591167,794255600344⟩,⟨189704285485,189704291521⟩,⟨-2441661863029,-2441661631943⟩,⟨-687241359291,-687241231343⟩,⟨-176801947366,-176801897861⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11382083623,11382083720⟩,⟨168912503166,168912505266⟩,⟨21707399386,21707400582⟩,⟨755777029268,755777082402⟩,⟨104037367426,104037394836⟩,⟨-17402930868,-17402924436⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨169422921682,169423069393⟩,⟨1672148369944,1672153721950⟩,⟨117089737641,117092633759⟩,⟨-1680452471124,-1680242655804⟩,⟨418555848721,418704369973⟩,⟨-604330497267,-604205435904⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-169423069393,-169422921682⟩,⟨-1672153721950,-1672148369944⟩,⟨-117092633759,-117089737641⟩,⟨1680242655804,1680452471124⟩,⟨-418704369973,-418555848721⟩,⟨604205435904,604330497267⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨55716521981,55716728136⟩,⟨-51544472039,-51537494645⟩,⟨126643718592,126647583347⟩,⟨-2240308453624,-2240044989745⟩,⟨-1715703893359,-1715510518317⟩,⟨470344929977,470513258288⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29495751462842,29495777502522⟩,⟨-267569709349326,-267569054881532⟩,⟨-89601854497422,-89601355173667⟩,⟨3943658351420103,3943681820890167⟩,⟨1448682202504494,1448703199144098⟩,⟨333846124131717,333867866435176⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13167995812,13167995913⟩,⟨173840196010,173840198680⟩,⟨41520929206,41520930686⟩,⟨613083743970,613083823094⟩,⟨123656051490,123656091956⟩,⟨26764303282,26764318433⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353247680081,353247994648⟩,⟨1459002648159,1459014699467⟩,⟨40758236124,40765247410⟩,⟨-20932293841332,-20931787510199⟩,⟨-3603943884057,-3603584037553⟩,⟨-2051080789670,-2050781374825⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353247994648,-353247680081⟩,⟨-1459014699467,-1459002648159⟩,⟨-40765247410,-40758236124⟩,⟨20931787510199,20932293841332⟩,⟨3603584037553,3603943884057⟩,⟨2050781374825,2051080789670⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨85224775549,85225243941⟩,⟨-492334921088,-492319628521⟩,⟨-90334886958,-90324710437⟩,⟨1037309716082,1037910419611⟩,⟨-2191569704666,-2191095420560⟩,⟨741375211836,741814840284⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨233443498959,233443498965⟩,⟨1585432258851,1585432258861⟩,⟨314499588929,314499588935⟩,⟨-3973281040305,-3973281040301⟩,⟨-1576346446732,-1576346446720⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1665181475542,-1665180030931⟩,⟨-4079009457065,-4078967763206⟩,⟨437030118228,437057108901⟩,⟨40650690023461,40652221643748⟩,⟨-7640391051616,-7639163326203⟩,⟨2317795983937,2318975787450⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-182230681420,-182230522636⟩,⟨-1649269429800,-1649263807857⟩,⟨-239475369156,-239472156835⟩,⟨2253356787557,2253588281679⟩,⟨-183399502446,-183237328307⟩,⟨672217772772,672356512369⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51212817539,51212976329⟩,⟨-63837170949,-63831548996⟩,⟨75024219773,75027432100⟩,⟨-1719924252748,-1719692758622⟩,⟨-1759745949178,-1759583775027⟩,⟨322089941649,322228681248⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4318670180,4318709896⟩,⟨-28943924148,-28942494115⟩,⟨5238705992,5239592130⟩,⟨-74932999660,-74873306987⟩,⟨-296519187889,-296474481249⟩,⟨53214988950,53253632886⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2385379666,2385394459⟩,⟨-5946806642,-5946264484⟩,⟨6988924138,6989245056⟩,⟨-152809613422,-152786246098⟩,⟨-172642770212,-172626014272⟩,⟨40242897674,40256791897⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4298993184,4299019929⟩,⟨-28347440908,-28346354273⟩,⟨4763920098,4764547282⟩,⟨-94099190519,-94048478701⟩,⟨-282155412748,-282120677782⟩,⟨45064714277,45091977812⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4299019929,-4298993184⟩,⟨28346354273,28347440908⟩,⟨-4764547282,-4763920098⟩,⟨94048478701,94099190519⟩,⟨282120677782,282155412748⟩,⟨-45091977812,-45064714277⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨19650251,19716712⟩,⟨-597569875,-595053207⟩,⟨474158710,475672032⟩,⟨19115479041,19225883532⟩,⟨-14398510107,-14319068501⟩,⟨8123011138,8188918609⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨55716521981,55716728136⟩,⟨-51544472039,-51537494645⟩,⟨126643718592,126647583347⟩,⟨-2240308453624,-2240044989745⟩,⟨-1715703893359,-1715510518317⟩,⟨470344929977,470513258288⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨19650251,19716712⟩,⟨-597569875,-595053207⟩,⟨474158710,475672032⟩,⟨19115479041,19225883532⟩,⟨-14398510107,-14319068501⟩,⟨8123011138,8188918609⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110810156236,111239652967⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111239652967,-110810156236⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438516160921,438945657652⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨43851616091,45437734093⟩,⟨-113816633344,-109951162777⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨154661772327,156677387060⟩,⟨985694994432,989560464999⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨43422119360,45867230824⟩,⟨-113816633344,-109951162777⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2156560996736,-2142324246336⟩,⟨6917291181295,7034920273340⟩,⟨3077365706358,3120524530974⟩,⟨-45010986698117,-43518336757937⟩,⟨-27782389021385,-27076465034383⟩,⟨-8856362317971,-8613078253502⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-307304018865,-301348031678⟩,⟨-967890618020,-918103396052⟩,⟨-428064823369,-409752987417⟩,⟨5988544944564,6541390450484⟩,⟨3701030661199,3964819582666⟩,⟨1192672683616,1279993227453⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨301348031678,307304018865⟩,⟨918103396052,967890618020⟩,⟨409752987417,428064823369⟩,⟨-6541390450484,-5988544944564⟩,⟨-3964819582666,-3701030661199⟩,⟨-1279993227453,-1192672683616⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-156677387060,-154661772327⟩,⟨-989560464999,-985694994432⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨942834240716,944849855449⟩,⟨-989560464999,-985694994432⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-169028908736,-166680854080⟩,⟨-1154002676895,-1147042677276⟩,⟨-511888340186,-510296546186⟩,⟨-1211194265381,-1196628457812⟩,⟨742232692467,749868919676⟩,⟨-238314599136,-236834753240⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145252615754,-142929290176⟩,⟨-842249190936,-831466228347⟩,⟨-373407034204,-370101180265⟩,⟨1015788915734,1051092629202⟩,⟨1382383424200,1399107469350⟩,⟨202248929949,205624395230⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨142929290176,145252615754⟩,⟨831466228347,842249190936⟩,⟨370101180265,373407034204⟩,⟨-1051092629202,-1015788915734⟩,⟨-1399107469350,-1382383424200⟩,⟨-205624395230,-202248929949⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨444277321854,452556634619⟩,⟨1749569624399,1810139808956⟩,⟨779854167682,801471857573⟩,⟨-7592483079686,-7004333860298⟩,⟨-5363927052016,-5083414085399⟩,⟨-1485617622683,-1394921613565⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨803119221063,813288031646⟩,⟨4146461708478,4221225488806⟩,⟨779854167682,801471857573⟩,⟨-19810784409331,-19009362082949⟩,⟨-5363927052016,-5083414085399⟩,⟨-1485617622683,-1394921613565⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨86844238720,91734461648⟩,⟨-227633266688,-219902325554⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13178535066281,13920621994424⟩,⟨31591077730308,36488277237784⟩,⟨-140720827687104,-125994102979598⟩,⟨151457834598917,191283748142092⟩,⟨-421794847606788,-251565914620727⟩,⟨2409146981177090,2845038296834071⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9626032640137,10296821766254⟩,⟨72773848628888,80433495491677⟩,⟨-94741362286967,-81882989502503⟩,⟨98082314478408,193816713410419⟩,⟨-897751136357751,-693230293417024⟩,⟨1535758164449734,1908973463620535⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨81061360640,86661370112⟩,⟨-718056901061,-568106991075⟩,⟨639217241673,845788046264⟩,⟨6188974703636,11095467747348⟩,⟨-8559374865403,-895970707039⟩,⟨-7016219902627,4467438528573⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1180572988416,1186172997888⟩,⟨-718056901061,-568106991075⟩,⟨639217241673,845788046264⟩,⟨6188974703636,11095467747348⟩,⟨-8559374865403,-895970707039⟩,⟨-7016219902627,4467438528573⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨78212437504,83415604352⟩,⟨-668753156196,-526601299826⟩,⟨592516261241,787713932664⟩,⟨5330056422281,10081411674392⟩,⟨-7687884461677,-351402172862⟩,⟨-7098802425885,3841390691921⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨83978639918,89990260208⟩,⟨-775939121462,-605836524095⟩,⟨681669400168,913966612662⟩,⟨6707439020810,12591262106341⟩,⟨-9972057557590,-1053337861733⟩,⟨-7501673060741,5694970290378⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-86661370112,-81061360640⟩,⟨568106991075,718056901061⟩,⟨-845788046264,-639217241673⟩,⟨-11095467747348,-6188974703636⟩,⟨895970707039,8559374865403⟩,⟨-4467438528573,7016219902627⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1012850257664,1018450267136⟩,⟨568106991075,718056901061⟩,⟨-845788046264,-639217241673⟩,⟨-11095467747348,-6188974703636⟩,⟨895970707039,8559374865403⟩,⟨-4467438528573,7016219902627⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-90267389888,-84204977024⟩,⟨613324246322,779495197981⟩,⟨-918155259838,-690094364519⟩,⟨-12597437393672,-7023694404738⟩,⟨1352228663450,9942654242702⟩,⟨-5616393251507,7183411980727⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-83612437580,-77568104348⟩,⟨506032391666,678519114886⟩,⟨-801510574554,-566265203433⟩,⟨-10560919164919,-4541059717615⟩,⟨-656293849828,8427886142046⟩,⟨-4975947952032,8433145333539⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨366202338,12422155860⟩,⟨-269906729796,72682590791⟩,⟨-119841174386,347701409229⟩,⟨-3853480144109,8050202388726⟩,⟨-10628351407418,7374548280313⟩,⟨-12477621012773,14128115623917⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨183101169,6211077930⟩,⟨-134953364898,36341295396⟩,⟨-59920587193,173850704615⟩,⟨-1926740072055,4025101194363⟩,⟨-5314175703709,3687274140157⟩,⟨-6238810506387,7064057811959⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6211077930,-183101169⟩,⟨-36341295396,134953364898⟩,⟨-173850704615,59920587193⟩,⟨-4025101194363,1926740072055⟩,⟨-3687274140157,5314175703709⟩,⟨-7064057811959,6238810506387⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755912305686,761940301711⟩,⟨-36341295396,134953364898⟩,⟨-173850704615,59920587193⟩,⟨-4025101194363,1926740072055⟩,⟨-3687274140157,5314175703709⟩,⟨-7064057811959,6238810506387⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨5976238925,6830480807⟩,⟨-113191699466,-83767237238⟩,⟨94252426340,133326740822⟩,⟨1499633551705,2686927746583⟩,⟨-2453982409122,-792665356886⟩,⟨-362772966977,2005457214147⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6830480807,-5976238925⟩,⟨83767237238,113191699466⟩,⟨-133326740822,-94252426340⟩,⟨-2686927746583,-1499633551705⟩,⟨792665356886,2453982409122⟩,⟨-2005457214147,362772966977⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092681146969,1093535388851⟩,⟨83767237238,113191699466⟩,⟨-133326740822,-94252426340⟩,⟨-2686927746583,-1499633551705⟩,⟨792665356886,2453982409122⟩,⟨-2005457214147,362772966977⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6851785600,-5992539456⟩,⟨84225030400,113899274346⟩,⟨-134160182259,-94767521713⟩,⟨-2715522969374,-1514280966567⟩,⟨804256724812,2483220306077⟩,⟨-2034363521307,356872638612⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3425892800,-2996269728⟩,⟨42112515200,56949637173⟩,⟨-67080091130,-47383760856⟩,⟨-1357761484687,-757140483283⟩,⟨402128362406,1241610153039⟩,⟨-1017181760654,178436319306⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨2996269728,3425892800⟩,⟨-56949637173,-42112515200⟩,⟨47383760856,67080091130⟩,⟨757140483283,1357761484687⟩,⟨-1241610153039,-402128362406⟩,⟨-178436319306,1017181760654⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765119653344,765549295680⟩,⟨-56949637173,-42112515200⟩,⟨47383760856,67080091130⟩,⟨757140483283,1357761484687⟩,⟨-1241610153039,-402128362406⟩,⟨-178436319306,1017181760654⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273170286742,273383847213⟩,⟨20941809309,28297924867⟩,⟨-33331685206,-23563106585⟩,⟨-671731936646,-374908387926⟩,⟨198166339221,613495602281⟩,⟨-501364303537,90693241745⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530239306688,1531098591360⟩,⟨-113899274346,-84225030400⟩,⟨94767521712,134160182260⟩,⟨1514280966566,2715522969374⟩,⟨-2483220306078,-804256724812⟩,⟨-356872638612,2034363521308⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1187024893237,1193587907460⟩,⟨-846190270961,-662140471840⟩,⟨745020942638,996714348106⟩,⟨7952082257146,14275201638942⟩,⟨-11499983811747,-1875440369077⟩,⟨-7333020722845,6929256041810⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1274538158698,1287664187144⟩,⟨-1692380541923,-1324280943680⟩,⟨1490041885275,1993428696212⟩,⟨15904164514294,28550403277874⟩,⟨-22999967623487,-3750880738154⟩,⟨-14661278275858,13858512083617⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨162417414592,173682994176⟩,⟨-1459973616144,-1130777970339⟩,⟨1272318043080,1719680196055⟩,⟨11641650663838,23466772773446⟩,⟨-18532988226278,-919347584452⟩,⟨-15337560244943,10483101782749⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨55729542530,60054654105⟩,⟨-500463900873,-379935792803⟩,⟨425758151987,590837589097⟩,⟨3761390838681,7888273297286⟩,⟨-6289192534269,20222710695⟩,⟨-5686345806325,3679766049968⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380183255576,380694130735⟩,⟨825601038,18480147626⟩,⟨-22870540477,563918444⟩,⟨-565048578521,150205701995⟩,⟨-338023885416,661399209861⟩,⟨-795030213102,628057374651⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175583025881,3179850248226⟩,⟨-154567833154,-6886800795⟩,⟨-4716610156,191289050074⟩,⟨-1256289632774,4741089222063⟩,⟨-5550535197101,2827688088530⟩,⟨-5253635219957,6672642077732⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨160956723719,173681479976⟩,⟨-1455812505061,-1097670476890⟩,⟨1229406831214,1719184048933⟩,⟨10799700199556,23213000092458⟩,⟨-18661997876448,212411944847⟩,⟨-16737255346760,11212132196019⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨323374138311,347364474152⟩,⟨-2915786121205,-2228448447229⟩,⟨2501724874294,3438864244988⟩,⟨22441350863394,46679772865904⟩,⟨-37194986102726,-706935639605⟩,⟨-32074815591703,21695233978768⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519688377505,528009898855⟩,⟨-50367630282,187040145770⟩,⟨-240950354650,83047617018⟩,⟨-5587555640067,2703515424434⟩,⟨-5153096041652,7379951282744⟩,⟨-9809459837659,8701727396420⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357284843337,365900652142⟩,⟨-52355691078,194422807591⟩,⟨-250460906391,86325589611⟩,⟨-5817375192341,2844661669611⟩,⟨-5400855043978,7686535167093⟩,⟨-10216345811020,9102340554960⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714569686674,731801304284⟩,⟨-104711382156,388845615182⟩,⟨-500921812782,172651179222⟩,⟨-11634750384682,5689323339222⟩,⟨-10801710087956,15373070334186⟩,⟨-20432691622040,18204681109920⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523408825881,1525122352435⟩,⟨-30132037108,28966669066⟩,⟨-38559219110,39907755920⟩,⟨-1172646780017,1215889417669⟩,⟨-1690554949192,1649725684310⟩,⟨-2362329852759,2397136488285⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨990059349884,1015074782758⟩,⟨-165299146408,558643465014⟩,⟨-720487824159,266044226410⟩,⟨-16940244441479,8721354589488⟩,⟨-16134966641497,22449691050739⟩,⟨-29950653798972,26882138623694⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67868318691,67974477058⟩,⟨10405856398,14072057764⟩,⟨-16575257790,-11708362912⟩,⟨-333242681809,-184833078091⟩,⟨96751933930,304182929388⟩,⟨-248309665341,47121045253⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49573237667,50279439755⟩,⟨263544759905,271375239487⟩,⟨35876776021,40996764342⟩,⟨-1392759281668,-1200327263936⟩,⟨-317195052696,-122676603032⟩,⟨-299679018351,-67857066552⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2129702202849,2132094683898⟩,⟨-317215414740,-234439452696⟩,⟨263784362178,373643099148⟩,⟨4227888188606,7586470815861⟩,⟨-6943693479260,-2253158618936⟩,⟨-977572765083,5698548332100⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2964001416639,2968997402752⟩,⟨-662596095936,-489419743036⟩,⟨550680669441,780461627224⟩,⟨8853148338652,15895828326088⟩,⟨-14561970123562,-4734041516014⟩,⟨-2007846122657,11971452318482⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨133636737402,135768938021⟩,⟨680149315683,710724871141⟩,⟨121542906213,146392685766⟩,⟨-3688768457937,-2743496575385⟩,⟨-1415132172361,-367487002109⟩,⟨-865098910465,422717018462⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8904288692511,9046358382561⟩,⟨-48111559895394,-44607006205781⟩,⟨-9909855072571,-7971286667057⟩,⟨626857190354080,761452934673035⟩,⟨103967379480897,201203308697551⟩,⟨-14343166013318,80273251115156⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8017899994308,8351644528311⟩,⟨-45776856975594,-35570241899926⟩,⟨-15076725551415,-4988865364437⟩,⟨376188730107861,789199267280953⟩,⟨-55810863251214,403475714283165⟩,⟨-264459825881004,308272022134182⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16035799988616,16703289056622⟩,⟨-91553713951188,-71140483799852⟩,⟨-30153451102830,-9977730728874⟩,⟨752377460215722,1578398534561906⟩,⟨-111621726502428,806951428566330⟩,⟨-528919651762008,616544044268364⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10867759718499,10909882818322⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108414,2148278590204846⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9768248090723,9810371190546⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108424,2148278590204831⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2401631390336,2406362620352⟩,⟨-12184942684160,-12039116462039⟩,⟨0,0⟩,⟨102958094106835,109987257462969⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7716019792643,7816578081484⟩,⟨-50012207442321,-48543329891207⟩,⟨-22184234377654,-21595965062681⟩,⟨610795446422614,639978483469272⟩,⟨325879335650599,339448464044555⟩,⟨120887638840235,125922174586458⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6616508164867,6717066453708⟩,⟨-50012207442321,-48543329891207⟩,⟨-22184234377655,-21595965062680⟩,⟨610795446422620,639978483469269⟩,⟨325879335650601,339448464044554⟩,⟨120887638840235,125922174586459⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1973295337664,1989880141760⟩,⟨-8310879733474,-7946021679834⟩,⟨-3686510020669,-3535027509847⟩,⟨37161198122951,48924896071200⟩,⟨25477719552795,30861369895178⟩,⟨7427651077487,9559944748019⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99599284960,100028781692⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨132622894561,134638509295⟩,⟨704226516661,711713007605⟩,⟨313480261794,315518313565⟩,⟨-1781208837000,-1767320322048⟩,⟨-1580290266898,-1572402626556⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4374926728000,4396242762112⟩,⟨-20495822417634,-19985138141873⟩,⟨-3686510020669,-3535027509847⟩,⟨140119292229786,158912153534169⟩,⟨25477719552795,30861369895178⟩,⟨7427651077487,9559944748019⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨646748276622,694728948304⟩,⟨-5831572242410,-4456896894458⟩,⟨5003449748588,6877728489976⟩,⟨44882701726788,93359545731808⟩,⟨-74389972205452,-1413871279210⟩,⟨-64149631183406,43390467957536⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5021675004622,5090971710416⟩,⟨-26327394660044,-24442035036331⟩,⟨1316939727919,3342700980129⟩,⟨185001993956574,252271699265977⟩,⟨-48912252652657,29447498615968⟩,⟨-56721980105919,52950412705555⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨454888540627,463154445080⟩,⟨1610418690571,1850740444249⟩,⟨119295014188,304104384307⟩,⟨-35465092081341,-26085452974216⟩,⟨-3399358625170,5347943052172⟩,⟨-5160318837764,4817198053411⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32232127817,34282984479⟩,⟨-691690179732,-650554317739⟩,⟨325509421405,328085365043⟩,⟨8026374536105,8707216374130⟩,⟨-6627114036394,-6561817940510⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨487120668444,497437429559⟩,⟨918728510839,1200186126510⟩,⟨444804435593,632189749350⟩,⟨-27438717545236,-17378236600086⟩,⟨-10026472661564,-1213874888338⟩,⟨-5160318837764,4817198053411⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502387216868,503376923070⟩,⟨2513460839922,2553938535635⟩,⟨0,0⟩,⟨2096765778922,4420352332343⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨222574450980,227736129738⟩,⟨1533331837043,1704912046892⟩,⟨203239380833,289428254132⟩,⟨-7432629894614,-365027536450⟩,⟨-3573492383419,913804375087⟩,⟨-2362490175632,2205403083231⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-694728948304,-646748276622⟩,⟨4456896894458,5831572242410⟩,⟨-6877728489976,-5003449748588⟩,⟨-93359545731808,-44882701726788⟩,⟨1413871279210,74389972205452⟩,⟨-43390467957536,64149631183406⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3680197779696,3749494485490⟩,⟨-16038925523176,-14153565899463⟩,⟨-10564238510645,-8538477258435⟩,⟨46759746497978,114029451807381⟩,⟨26891590832005,105251342100630⟩,⟨-35962816880049,73709575931425⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443904793519,459136888946⟩,⟨393116206291,719844246597⟩,⟨-244366639416,46053726353⟩,⟨-21197996491577,-10082627105986⟩,⟨-13586149836241,-1878792767538⟩,⟨-11661986127794,2986399245237⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨309323544654,313354774120⟩,⟨1971389988864,1979120929998⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-313354774120,-309323544654⟩,⟨-1979120929998,-1971389988864⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨786156853656,790188083122⟩,⟨-1979120929998,-1971389988864⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1410917006061,1430070892512⟩,⟨-9554579776156,-9219506024822⟩,⟨-4238185994464,-4101575447202⟩,⟨55064397907942,65080113834369⟩,⟨34839687819923,39430394925684⟩,⟨10950284895993,12757359106257⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1430070892512,-1410917006061⟩,⟨9219506024822,9554579776156⟩,⟨4101575447202,4238185994464⟩,⟨-65080113834369,-55064397907942⟩,⟨-39430394925684,-34839687819923⟩,⟨-12757359106257,-10950284895993⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-330559264736,-311405378285⟩,⟨9219506024822,9554579776156⟩,⟨4101575447202,4238185994464⟩,⟨-65080113834369,-55064397907942⟩,⟨-39430394925684,-34839687819923⟩,⟨-12757359106257,-10950284895993⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13789611419,-12298079587⟩,⟨395238998396,432796931503⟩,⟨30014730126,52602958302⟩,⟨-4692978845535,-4018514731580⟩,⟨1904806717951,2358873631295⟩,⟨2739461254202,2951475925697⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430115182100,446838809359⟩,⟨788355204687,1152641178100⟩,⟨-214351909290,98656684655⟩,⟨-25890975337112,-14101141837566⟩,⟨-11681343118290,480080863757⟩,⟨-8922524873592,5937875170934⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100028781692,-99599284960⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨3933393636,4172801000⟩,⟨24281383040,26662188617⟩,⟨39722996071,39933365192⟩,⟨-273485398020,-262250703087⟩,⟨249756374792,250871388573⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8591597749,9132484001⟩,⟨6793553158,15283430904⟩,⟨86765789348,87397126939⟩,⟨-821168948405,-687148148515⟩,⟨102988436616,114103164432⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1486466998866,1505288116520⟩,⟨-7911852186834,-7578592395166⟩,⟨-1502200459521,-1425359084457⟩,⟨112021168641605,120301394918576⟩,⟨23825164338594,25844866917598⟩,⟨5283059902881,5782734638641⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11615271906,12502841529⟩,⟨-56530981002,-38295411689⟩,⟨104824412877,108513399663⟩,⟨-468840454950,-23413688091⟩,⟨-324368362480,-235977343355⟩,⟨-197529591722,-176927715587⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12502841529,-11615271906⟩,⟨38295411689,56530981002⟩,⟨-108513399663,-104824412877⟩,⟨23413688091,468840454950⟩,⟨235977343355,324368362480⟩,⟨176927715587,197529591722⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112531623221,-111214556866⟩,⟨-839595903615,-820501340840⟩,⟨-108513399663,-104824412877⟩,⟨2222436943643,2667863710502⟩,⟨235977343355,324368362480⟩,⟨176927715587,197529591722⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨77929749463,83009846798⟩,⟨-552680373931,-511135311805⟩,⟨633219214962,654791493617⟩,⟨3056781339867,3761562951623⟩,⟨-3948065531790,-3473367864502⟩,⟨-2650113655615,-2420934099349⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨105355866987,113644760804⟩,⟨-1353969161783,-1228166710998⟩,⟨742658845487,795418580123⟩,⟨19118450441188,22186111184610⟩,⟨-7765583351149,-6354040922318⟩,⟨-5042905489790,-4478119307970⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-113644760804,-105355866987⟩,⟨1228166710998,1353969161783⟩,⟨-795418580123,-742658845487⟩,⟨-22186111184610,-19118450441188⟩,⟨6354040922318,7765583351149⟩,⟨4478119307970,5042905489790⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨985866866972,994155760789⟩,⟨1228166710998,1353969161783⟩,⟨-795418580123,-742658845487⟩,⟨-22186111184610,-19118450441188⟩,⟨6354040922318,7765583351149⟩,⟨4478119307970,5042905489790⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨118915083976,121737366171⟩,⟨779579398872,809313838648⟩,⟨183677758885,195705782340⟩,⟨-2754030750922,-2137869030038⟩,⟨-827155509937,-546088877067⟩,⟨-233248603970,-119589546818⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11249246798,11517264489⟩,⟨165985862676,171860101334⟩,⟨21205779606,22212023406⟩,⟨678489261999,832649569053⟩,⟨90052477328,117985637504⟩,⟨-20445746588,-14373253323⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164064360137,174965132739⟩,⟨1461801508670,1882974256923⟩,⟨-6578949291,235351664770⟩,⟨-11027680811143,7703593543694⟩,⟨-6418560434423,7366788465544⟩,⟨-7069281365464,5863733434922⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-174965132739,-164064360137⟩,⟨-1882974256923,-1461801508670⟩,⟨-235351664770,6578949291⟩,⟨-7703593543694,11027680811143⟩,⟨-7366788465544,6418560434423⟩,⟨-5863733434922,7069281365464⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47609318241,63671769601⟩,⟨-349642419880,243110538222⟩,⟨-32112283937,296007203423⟩,⟨-15136223438308,10662653274693⟩,⟨-10940280848963,7332364809510⟩,⟨-8226223610554,9274684448695⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28779476773023,30229369436574⟩,⟨-291947748154492,-243564499546148⟩,⟨-110575088947755,-69463570643997⟩,⟨2920514933083855,4983862156634746⟩,⟨470398472263698,2464128915277635⟩,⟨-784744115061764,1463243524993400⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨12860980129,13478699041⟩,⟨168627138342,179213630188⟩,⟨39730468638,43336888642⟩,⟨495630209432,728985495137⟩,⟨77299161900,169983092342⟩,⟨9717857025,43800814164⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336633346615,370575956217⟩,⟨834847904245,2078228905003⟩,⟨-315582152335,378965719619⟩,⟨-48037117196839,6429746278785⟩,⟨-22004547018490,15426266051117⟩,⟨-18082223999223,14121769400078⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370575956217,-336633346615⟩,⟨-2078228905003,-834847904245⟩,⟨-378965719619,315582152335⟩,⟨-6429746278785,48037117196839⟩,⟨-15426266051117,22004547018490⟩,⟨-14121769400078,18082223999223⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59539225883,110205462744⟩,⟨-1289873700316,317793273855⟩,⟨-593317628909,414238836990⟩,⟨-32320721615897,33935975359273⟩,⟨-27107609169407,22484627882247⟩,⟨-23044294273670,24020099170157⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨232222179521,234667290987⟩,⟨1581258838503,1589604322909⟩,⟨313480261794,315518313565⟩,⟨-3980232092552,-3966343577600⟩,⟨-1580290266898,-1572402626556⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1709530106993,-1622005938521⟩,⟨-5558973214470,-2596341209266⟩,⟨-639249064579,1557303657589⟩,⟨-22955164401320,104249028731505⟩,⟨-64919247733546,48412868061665⟩,⟨-58618484307014,63085906563643⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-189278300801,-175424222460⟩,⟨-1873814772735,-1430841209593⟩,⟨-375062358647,-98538630556⟩,⟨-7571336840580,12142656878106⟩,⟨-7842222792146,7358866751439⟩,⟨-6541353659429,7901875760371⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨42943878720,59243068527⟩,⟨-292555934232,158763113316⟩,⟨-61582096853,216979683009⟩,⟨-11551568933132,8176313300506⟩,⟨-9422513059044,5786464124883⟩,⟨-6891824332962,7552090603887⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2578073647,6381903252⟩,⟨-109740581811,42770415782⟩,⟨-37577167387,53657395819⟩,⟨-3959190350840,3854288812650⟩,⟨-3145319656280,2311226865199⟩,⟨-2478462519684,2543637011517⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1677268955,3192090998⟩,⟨-31526562926,17108712204⟩,⟨-6636241568,23382276104⟩,⟨-1329312873784,1036785513525⟩,⟨-1130860765856,686225140600⟩,⟨-766985767929,899470622257⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3010197368,5776999831⟩,⟨-81184376438,18841702684⟩,⟨-22712811882,36924334374⟩,⟨-2607722185378,2494997325568⟩,⟨-2241852704720,1487382248147⟩,⟨-1533544100660,1700103971397⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5776999831,-3010197368⟩,⟨-18841702684,81184376438⟩,⟨-36924334374,22712811882⟩,⟨-2494997325568,2607722185378⟩,⟨-1487382248147,2241852704720⟩,⟨-1700103971397,1533544100660⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3198926184,3371705884⟩,⟨-128582284495,123954792220⟩,⟨-74501501761,76370207701⟩,⟨-6454187676408,6462010998028⟩,⟨-4632701904427,4553079569919⟩,⟨-4178566491081,4077181112177⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47609318241,63671769601⟩,⟨-349642419880,243110538222⟩,⟨-32112283937,296007203423⟩,⟨-15136223438308,10662653274693⟩,⟨-10940280848963,7332364809510⟩,⟨-8226223610554,9274684448695⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3198926184,3371705884⟩,⟨-128582284495,123954792220⟩,⟨-74501501761,76370207701⟩,⟨-6454187676408,6462010998028⟩,⟨-4632701904427,4553079569919⟩,⟨-4178566491081,4077181112177⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (517/5120) u, BivariateJet2.affineZ (521/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000008

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000009Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2138581618496,-2138581579328⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2138581618432,-2138581579264⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-169652090304,-169652090240⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-169652090304,-169652090240⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨83194711744,83194711808⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-90008753792,-90008753728⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨83194835392,83194835456⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-90008898560,-90008898496⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6814063104,-6814063040⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6814041984,-6814041920⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨173203465472,173203465536⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨173203733888,173203733952⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1968929489024,1968929527616⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1968929489024,1968929527616⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2518909148864,-2518909091008⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2145655400192,-2145655360896⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2131547809152,-2131547770048⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-170829990528,-170829990464⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-168476330624,-168476330560⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨80605471488,80605471552⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-86985481536,-86985481472⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨85807041472,85807041536⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-93074687488,-93074687424⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7267646016,-7267645952⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6380010048,-6380009984⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨167590953024,167590953088⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨178881728896,178881728960⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1960717779584,1960717818176⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1977179030336,1977179068928⟩



end LaneCBRB2Cell000009Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000009
open Set LaneCBRB2Cell000009Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111024904601,111024904602⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨115749368627,115749368628⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111024904602,-111024904601⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438730909286,438730909287⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46186710957,46186710959⟩,⟨-115749368628,-115749368627⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157211615558,157211615561⟩,⟨983762259148,983762259149⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46186710956,46186710960⟩,⟨-115749368628,-115749368627⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2138581618496,-2138581579264⟩,⟨6880267969007,6880267969148⟩,⟨3068410273014,3068410273081⟩,⟨-43053739616220,-43053739614472⟩,⟨-26890583287070,-26890583286118⟩,⟨-8563021405234,-8563021404864⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-305781096589,-305781090972⟩,⟨-929683521015,-929683485871⟩,⟨-414613279511,-414613263835⟩,⟨6155958508732,6155958509367⟩,⟨3784458127262,3784458166832⟩,⟨1224367614743,1224367614880⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305781090972,305781096589⟩,⟨929683485871,929683521015⟩,⟨414613263835,414613279511⟩,⟨-6155958509367,-6155958508732⟩,⟨-3784458166832,-3784458127262⟩,⟨-1224367614880,-1224367614743⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157211615561,-157211615558⟩,⟨-983762259149,-983762259148⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨942300012215,942300012218⟩,⟨-983762259149,-983762259148⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-169652090304,-169652090240⟩,⟨-1147891360374,-1147891360368⟩,⟨-511927974077,-511927974073⟩,⟨-1198399854932,-1198399854918⟩,⟨748498769147,748498769159⟩,⟨-238351504452,-238351504448⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145394703183,-145394703127⟩,⟨-831970027632,-831970027565⟩,⟨-371035749063,-371035749030⟩,⟨1027048890973,1027048891003⟩,⟨1387895093952,1387895094039⟩,⟨204271259963,204271259973⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145394703127,145394703183⟩,⟨831970027565,831970027632⟩,⟨371035749030,371035749063⟩,⟨-1027048891003,-1027048890973⟩,⟨-1387895094039,-1387895093952⟩,⟨-204271259973,-204271259963⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨451175794099,451175799772⟩,⟨1761653513436,1761653548647⟩,⟨785649012865,785649028574⟩,⟨-7183007400370,-7183007399705⟩,⟨-5172353260871,-5172353221214⟩,⟨-1428638874853,-1428638874706⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨810961746243,810961757820⟩,⟨4165648458960,4165648552115⟩,⟨785649012865,785649028574⟩,⟨-19294794564572,-19294794563400⟩,⟨-5172353260871,-5172353221214⟩,⟨-1428638874853,-1428638874706⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92373421912,92373421920⟩,⟨-231498737256,-231498737254⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13087377239977,13087377241111⟩,⟨32798517604395,32798517610363⟩,⟨-124317943372170,-124317943350341⟩,⟨164393940408446,164393940454022⟩,⟨-311555492042508,-311555491819729⟩,⟨2361810278021117,2361810278645847⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9652796780094,9652796918731⟩,⟨73774350259718,73774351722575⟩,⟨-82341114535742,-82341113022876⟩,⟨140110505852998,140110513254269⟩,⟨-738917938784147,-738917923773747⟩,⟨1547323434872692,1547323463788237⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨86423091200,86423224576⟩,⟨-654642300023,-654640240705⟩,⟨730657821580,730660118964⟩,⟨8630020093410,8630071533061⟩,⟨-4463029801858,-4462956186828⟩,⟨-1430859530824,-1430757234079⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1185934718976,1185934852352⟩,⟨-654642300023,-654640240705⟩,⟨730657821580,730660118964⟩,⟨8630020093410,8630071533061⟩,⟨-4463029801858,-4462956186828⟩,⟨-1430859530824,-1430757234079⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨83194711744,83194835456⟩,⟨-606936292018,-606934314509⟩,⟨677412228133,677414434285⟩,⟨7666088240641,7666139014750⟩,⟨-3763859710512,-3763788558548⟩,⟨-1743946247552,-1743848537895⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨89733927863,89734071392⟩,⟨-704176054838,-704173618792⟩,⟨785943072743,785945790519⟩,⟨9644372302144,9644437488609⟩,⟨-5204057494413,-5203969056417⟩,⟨-1088968631840,-1088849366263⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-86423224576,-86423091200⟩,⟨654640240705,654642300023⟩,⟨-730660118964,-730657821580⟩,⟨-8630071533061,-8630020093410⟩,⟨4462956186828,4463029801858⟩,⟨1430757234079,1430859530824⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1013088403200,1013088536576⟩,⟨654640240705,654642300023⟩,⟨-730660118964,-730657821580⟩,⟨-8630071533061,-8630020093410⟩,⟨4462956186828,4463029801858⟩,⟨1430757234079,1430859530824⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-90008898560,-90008753728⟩,⟨710485343263,710487671793⟩,⟨-792990319716,-792987721949⟩,⟨-9825380738053,-9825320667841⟩,⟨5356090508321,5356174398910⟩,⟨980889331874,981004306770⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-82934078202,-82933933834⟩,⟨601049423063,601051909568⟩,⟨-670846750471,-670843976383⟩,⟨-7500583385717,-7500516063304⟩,⟨3625455765516,3625546389934⟩,⟨1840583426653,1840704812527⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6799849661,6800137558⟩,⟨-103126631775,-103121709224⟩,⟨115096322272,115101814136⟩,⟨2143788916427,2143921425305⟩,⟨-1578601728897,-1578422666483⟩,⟨751614794813,751855446264⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3399924830,3400068779⟩,⟨-51563315888,-51560854612⟩,⟨57548161136,57550907068⟩,⟨1071894458213,1071960712653⟩,⟨-789300864449,-789211333241⟩,⟨375807397406,375927723132⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3400068779,-3399924830⟩,⟨51560854612,51563315888⟩,⟨-57550907068,-57548161136⟩,⟨-1071960712653,-1071894458213⟩,⟨789211333241,789300864449⟩,⟨-375927723132,-375807397406⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758723314837,758723478050⟩,⟨51560854612,51563315888⟩,⟨-57550907068,-57548161136⟩,⟨-1071960712653,-1071894458213⟩,⟨789211333241,789300864449⟩,⟨-375927723132,-375807397406⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6792971082,6792992050⟩,⟨-102911687486,-102911204932⟩,⟨114861372912,114861911334⟩,⟨2136197250983,2136212335588⟩,⟨-1571662228652,-1571644100744⟩,⟨746151922915,746174458108⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6792992050,-6792971082⟩,⟨102911204932,102911687486⟩,⟨-114861911334,-114861372912⟩,⟨-2136212335588,-2136197250983⟩,⟨1571644100744,1571662228652⟩,⟨-746174458108,-746151922915⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092718635726,1092718656694⟩,⟨102911204932,102911687486⟩,⟨-114861911334,-114861372912⟩,⟨-2136212335588,-2136197250983⟩,⟨1571644100744,1571662228652⟩,⟨-746174458108,-746151922915⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6814063104,-6814041920⟩,⟨103550960494,103551448036⟩,⟨-115575961617,-115575417629⟩,⟨-2159244730984,-2159229419520⟩,⟨1592299132371,1592317505804⟩,⟨-762961975425,-762939171367⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3407031552,-3407020960⟩,⟨51775480247,51775724018⟩,⟨-57787980809,-57787708814⟩,⟨-1079622365492,-1079614709760⟩,⟨796149566185,796158752902⟩,⟨-381480987713,-381469585683⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3407020960,3407031552⟩,⟨-51775724018,-51775480247⟩,⟨57787708814,57787980809⟩,⟨1079614709760,1079622365492⟩,⟨-796158752902,-796149566185⟩,⟨381469585683,381480987713⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765530404576,765530434432⟩,⟨-51775724018,-51775480247⟩,⟨57787708814,57787980809⟩,⟨1079614709760,1079622365492⟩,⟨-796158752902,-796149566185⟩,⟨381469585683,381480987713⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273179658931,273179664174⟩,⟨25727801233,25727921872⟩,⟨-28715477834,-28715343228⟩,⟨-534053083897,-534049312745⟩,⟨392911025186,392915557163⟩,⟨-186543614527,-186537980728⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531060809152,1531060868864⟩,⟨-103551448036,-103550960494⟩,⟨115575417628,115575961618⟩,⟨2159229419520,2159244730984⟩,⟨-1592317505804,-1592299132370⟩,⟨762939171366,762961975426⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1193307175008,1193307332111⟩,⟨-771097027724,-771094399036⟩,⟨860634771284,860637703964⟩,⟨11161752734984,11161822665109⟩,⟨-6369222920361,-6369127390344⟩,⟨-443985222994,-443855987885⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1287102722240,1287103036446⟩,⟨-1542194055447,-1542188798072⟩,⟨1721269542567,1721275407928⟩,⟨22323505469970,22323645330208⟩,⟨-12738445840718,-12738254780689⟩,⟨-887970295396,-887712126360⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨173203465472,173203733952⟩,⟨-1317424217161,-1317419404422⟩,⟨1470399667312,1470405036772⟩,⟨17491396498375,17491532162931⟩,⟨-9120045958109,-9119867218208⟩,⟨-2724961756198,-2724726667940⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59636671934,59636776800⟩,⟨-447686429027,-447684711093⟩,⟨499670376879,499672293477⟩,⟨5809528461717,5809573700680⟩,⟨-2949175474998,-2949113395045⟩,⟨-1093409001514,-1093324805377⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380400406035,380400428173⟩,⟨10097827156,10098118170⟩,⟨-11270723258,-11270398550⟩,⟨-212038275462,-212029135105⟩,⟨156914132634,156925088110⟩,⟨-76240943462,-76227362167⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178034855062,3178035040014⟩,⟨-84364193291,-84361752210⟩,⟨94157936662,94160660378⟩,⟨1775864779335,1775941607084⟩,⟨-1316021517538,-1315929549044⟩,⟨642416755404,642530616210⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨172374186191,172374499329⟩,⟨-1298571411965,-1298566230681⟩,⟨1449357241418,1449363021931⟩,⟨16956915298020,16957053622175⟩,⟨-8672373205580,-8672185646882⟩,⟨-3039972088297,-3039719502514⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨345577651663,345578233281⟩,⟨-2615995629126,-2615985635103⟩,⟨2919756908730,2919768058703⟩,⟨34448311796395,34448585785106⟩,⟨-17792419163689,-17792052865090⟩,⟨-5764933844495,-5764446170454⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523560691796,523560917049⟩,⟨71159634038,71163046178⟩,⟨-79426580444,-79422773668⟩,⟨-1474587840694,-1474495622360⟩,⟨1083800313174,1083924625588⟩,⟨-512797485027,-512630735821⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361285586766,361285819922⟩,⟨73656074282,73659621974⟩,⟨-82213061475,-82209103463⟩,⟨-1521314557840,-1521218296259⟩,⟨1116235218543,1116364668740⟩,⟨-524552238576,-524378927945⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722571173532,722571639844⟩,⟨147312148564,147319243948⟩,⟨-164426122950,-164418206926⟩,⟨-3042629115680,-3042436592518⟩,⟨2232470437086,2232729337480⟩,⟨-1049104477152,-1048757855890⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524267817102,1524267897782⟩,⟨-640243104,-639273008⟩,⟨713506294,714588706⟩,⟨23017083932,23047480001⟩,⟨-20673405060,-20636903718⟩,⟨16764713258,16810052511⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001710175278,1001710874755⟩,⟨203800069006,203810554039⟩,⟨-227477268428,-227465570632⟩,⟨-4203083376344,-4202796002109⟩,⟨3081509057621,3081892434403⟩,⟨-1443584161745,-1443073422075⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67872975754,67872978360⟩,⟨12784424990,12784485184⟩,⟨-14269034348,-14268967186⟩,⟨-264172781234,-264170890919⟩,⟨193897922654,193900190994⟩,⟨-91195672274,-91192856935⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50060759295,50060761932⟩,⟨266575294944,266575355100⟩,⟨37973855090,37973907611⟩,⟨-1289043535930,-1289041634838⟩,⟨-221202694227,-221200705569⟩,⟨-175844510596,-175842333352⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131989459777,2131989626075⟩,⟨-288389073836,-288387704790⟩,⟨321875618158,321877145716⟩,⟨6032922726469,6032965786838⟩,⟨-4456347746106,-4456296198480⟩,⟨2149070391541,2149134212069⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2968777614468,2968777961822⟩,⟨-602369108435,-602366225364⟩,⟨672313687187,672316904076⟩,⟨12641932300944,12642023119429⟩,⟨-9353612535928,-9353504073559⟩,⟨4539595049560,4539729008696⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135168430968,135168453904⟩,⟨692350760497,692351139852⟩,⟨133143170924,133143472811⟩,⟨-3197031064085,-3197019894545⟩,⟨-880939063335,-880927718113⟩,⟨-221668458497,-221656127713⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8943845880439,8943847398073⟩,⟨-45811606277985,-45811565629711⟩,⟨-8809859627306,-8809836662206⟩,⟨680846715058561,680848279106676⟩,⟨148539658393474,148540728892735⟩,⟨32022245551844,32023153973744⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8148291658066,8148298730520⟩,⟨-40078910197772,-40078758450595⟩,⟨-9876616030932,-9876494035695⟩,⟨569112278977170,569117369247018⟩,⟨168237639519666,168242416152854⟩,⟨21076340820124,21081542313155⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16296583316132,16296597461040⟩,⟨-80157820395544,-80157516901190⟩,⟨-19753232061864,-19752988071390⟩,⟨1138224557954340,1138234738494036⟩,⟨336475279039332,336484832305708⟩,⟨42152681640248,42163084626310⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10888780530353,10888780530452⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239700,2135836853297982⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9789268902577,9789268902676⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239713,2135836853297977⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2403994945600,2403995003456⟩,⟨-12111787164150,-12111787163733⟩,⟨0,0⟩,⟨106474359377039,106474359411671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7689799607367,7689799607515⟩,⟨-48119438296223,-48119438294320⟩,⟨-21459945959244,-21459945958368⟩,⟨602221243722042,602221243758050⟩,⟨322355277230109,322355277248578⟩,⟨119776666246258,119776666253723⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6590287979591,6590287979739⟩,⟨-48119438296224,-48119438294320⟩,⟨-21459945959244,-21459945958367⟩,⟨602221243722049,602221243758047⟩,⟨322355277230112,322355277248577⟩,⟨119776666246258,119776666253722⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1968929489024,1968929527616⟩,⟨-8028159329713,-8028159329176⟩,⟨-3580338247244,-3580338246999⟩,⟨41855339752055,41855339769292⟩,⟨27639082051671,27639082060040⟩,⟨8324669898884,8324669902421⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99813991382,99813991384⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134733006471,134733006475⟩,⟨702439442396,702439442403⟩,⟨313268670772,313268670779⟩,⟨-1760396448892,-1760396448888⟩,⟨-1570176793318,-1570176793308⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4372924434624,4372924531072⟩,⟨-20139946493863,-20139946492909⟩,⟨-3580338247244,-3580338246999⟩,⟨148329699129094,148329699180963⟩,⟨27639082051671,27639082060040⟩,⟨8324669898884,8324669902421⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨691155303326,691156466562⟩,⟨-5231991258252,-5231971270206⟩,⟨5839513817460,5839536117406⟩,⟨68896623592790,68897171570212⟩,⟨-35584838327378,-35584105730180⟩,⟨-11529867688990,-11528892340908⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5064079737950,5064080997634⟩,⟨-25371937752115,-25371917763115⟩,⟨2259175570216,2259197870407⟩,⟨217226322721884,217226870751175⟩,⟨-7945756275707,-7945023670140⟩,⟨-3205197790106,-3204222438487⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459718659223,459718773587⟩,⟨1738100982102,1738103802053⟩,⟨205088627713,205090652136⟩,⟨-30904283320639,-30904199146201⟩,⟨1081609894637,1081694197406⟩,⟨-290968805172,-290880262456⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34402918957,34402920901⟩,⟨-694210955737,-694210945945⟩,⟨326795816458,326795834885⟩,⟨8651866643662,8651866669853⟩,⟨-6594360098773,-6594360006268⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨494121578180,494121694488⟩,⟨1043890026365,1043892856108⟩,⟨531884444171,531886487021⟩,⟨-22252416676977,-22252332476348⟩,⟨-5512750204136,-5512665808862⟩,⟨-290968805172,-290880262456⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502882001783,502882013886⟩,⟨2533615820870,2533615942923⟩,⟨0,0⟩,⟨3256741201878,3256744126778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225995653053,225995711689⟩,⟨1616051808022,1616053436610⟩,⟨243267199040,243268139231⟩,⟨-3903079630492,-3903025942901⟩,⟨-1295731710416,-1295688283588⟩,⟨-133079973897,-133039474042⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-691156466562,-691155303326⟩,⟨5231971270206,5231991258252⟩,⟨-5839536117406,-5839513817460⟩,⟨-68897171570212,-68896623592790⟩,⟨35584105730180,35584838327378⟩,⟨11528892340908,11529867688990⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3681767968062,3681769227746⟩,⟨-14907975223657,-14907955234657⟩,⟨-9419874364650,-9419852064459⟩,⟨79432527558882,79433075588173⟩,⟨63223187781851,63223920387418⟩,⟨19853562239792,19854537591411⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451160001344,451160155719⟩,⟨525344799987,525348054266⟩,⟨-105306240877,-105303149271⟩,⟨-15209561599015,-15209466886198⟩,⟨-7776062657071,-7775951143014⟩,⟨-4107335177578,-4107202550303⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨314423231116,314423231122⟩,⟨1967524518296,1967524518298⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-314423231122,-314423231116⟩,⟨-1967524518298,-1967524518296⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨785088396654,785088396660⟩,⟨-1967524518298,-1967524518296⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1405882081292,1405882108859⟩,⟨-9255683705016,-9255683635524⟩,⟨-4127780355681,-4127780324682⟩,⟨58618154263267,58618154277756⟩,⟨36486790956922,36486791041123⟩,⟨11658650657606,11658650660583⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1405882108859,-1405882081292⟩,⟨9255683635524,9255683705016⟩,⟨4127780324682,4127780355681⟩,⟨-58618154277756,-58618154263267⟩,⟨-36486791041123,-36486790956922⟩,⟨-11658650660583,-11658650657606⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-306370481083,-306370453516⟩,⟨9255683635524,9255683705016⟩,⟨4127780324682,4127780355681⟩,⟨-58618154277756,-58618154263267⟩,⟨-36486791041123,-36486790956922⟩,⟨-11658650660583,-11658650657606⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12869572726,-12869571566⟩,⟨421052183205,421052189061⟩,⟨51144886129,51144898449⟩,⟨-4411102817166,-4411102801693⟩,⟨2032374624690,2032374686935⟩,⟨2804422276418,2804422301334⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438290428618,438290584153⟩,⟨946396983192,946400243327⟩,⟨-54161354748,-54158250822⟩,⟨-19620664416181,-19620569687891⟩,⟨-5743688032381,-5743576456079⟩,⟨-1302912901160,-1302780248969⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99813991384,-99813991382⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4192843306,4192843308⟩,⟨26351398360,26351398366⟩,⟨39828121951,39828121953⟩,⟨-277120265754,-277120265743⟩,⟨250313839737,250313839741⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9167319254,9167319480⟩,⟨11428530986,11428532410⟩,⟨87081028926,87081031027⟩,⟨-780428750868,-780428735780⟩,⟨108560442911,108560456131⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1490730984484,1490731005767⟩,⟨-7657403674760,-7657403284869⟩,⟨-1444200508807,-1444200438692⟩,⟨114135404769449,114135412672215⟩,⟨24344735966768,24344737575091⟩,⟨5424405641590,5424405948604⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12429160830,12429161315⟩,⟨-48349648412,-48349641433⟩,⟨106024290765,106024296182⟩,⟨-265681060367,-265680907511⟩,⟨-271310742950,-271310656396⟩,⟨-183533921112,-183533900811⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12429161315,-12429160830⟩,⟨48349641433,48349648412⟩,⟨-106024296182,-106024290765⟩,⟨265680907511,265681060367⟩,⟨271310656396,271310742950⟩,⟨183533900811,183533921112⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112243152699,-112243152212⟩,⟨-829112177141,-829112170160⟩,⟨-106024296182,-106024290765⟩,⟨2464704163063,2464704315919⟩,⟨271310656396,271310742950⟩,⟨183533900811,183533921112⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨82707972253,82707973882⟩,⟨-544511407677,-544511403559⟩,⟨635251287598,635251303024⟩,⟨3448503072169,3448503073174⟩,⟨-3634415740764,-3634415701466⟩,⟨-2507586929927,-2507586929544⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨112136455665,112136459475⟩,⟨-1314263846830,-1314263790031⟩,⟨752644954802,752644995429⟩,⟨20845423106082,20845424381295⟩,⟨-6805225475582,-6805224822070⟩,⟨-4660575091203,-4660574889469⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-112136459475,-112136455665⟩,⟨1314263790031,1314263846830⟩,⟨-752644995429,-752644954802⟩,⟨-20845424381295,-20845423106082⟩,⟨6805224822070,6805225475582⟩,⟨4660574889469,4660575091203⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨987375168301,987375172111⟩,⟨1314263790031,1314263846830⟩,⟨-752644995429,-752644954802⟩,⟨-20845424381295,-20845423106082⟩,⟨6805224822070,6805225475582⟩,⟨4660574889469,4660575091203⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120991921849,120991922320⟩,⟨791847900821,791847910228⟩,⟨189090845636,189090851711⟩,⟨-2455960381838,-2455960146801⟩,⟨-682516694661,-682516566950⟩,⟨-172198684003,-172198634888⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11458291936,11458292036⟩,⟨169279089306,169279091468⟩,⟨21646884500,21646885702⟩,⟨747205936600,747205991051⟩,⟨104506865054,104506892486⟩,⟨-17024423326,-17024416926⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨169830863520,169831012410⟩,⟨1673651302091,1673656681948⟩,⟨114989193360,114992034143⟩,⟨-1745386677932,-1745176294485⟩,⟨436157694571,436302699227⟩,⟨-590839004152,-590720623838⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-169831012410,-169830863520⟩,⟨-1673656681948,-1673651302091⟩,⟨-114992034143,-114989193360⟩,⟨1745176294485,1745386677932⟩,⟨-436302699227,-436157694571⟩,⟨590720623838,590839004152⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56164640643,56164848169⟩,⟨-57604873926,-57597865481⟩,⟨128275164897,128278945871⟩,⟨-2157903336007,-2157639264969⟩,⟨-1732034409643,-1731845978159⟩,⟨457640649941,457799530110⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29182795934929,29182821836652⟩,⟨-262531812400587,-262531162822407⟩,⟨-88439313060151,-88438829381858⟩,⟨3829170566868673,3829193808187744⟩,⟨1417438271960068,1417458516602050⟩,⟨327512763650163,327533090246528⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13314134005,13314134110⟩,⟨174272280368,174272283118⟩,⟨41615685072,41615686572⟩,⟨600033181933,600033262867⟩,⟨122149107988,122149148670⟩,⟨27140591744,27140606884⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353378396283,353378712718⟩,⟨1446431848900,1446443918207⟩,⟨33623264669,33630150216⟩,⟨-20928656084367,-20928150773889⟩,⟨-3548254458733,-3547903392716⟩,⟨-2008471976211,-2008187911217⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353378712718,-353378396283⟩,⟨-1446443918207,-1446431848900⟩,⟨-33630150216,-33623264669⟩,⟨20928150773889,20928656084367⟩,⟨3547903392716,3548254458733⟩,⟨2008187911217,2008471976211⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84911715900,84912187870⟩,⟨-500046935015,-500031605573⟩,⟨-87791504964,-87781515491⟩,⟨1307486357708,1308086396476⟩,⟨-2195784639665,-2195321997346⟩,⟨705275010057,705691727242⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234546997853,234546997859⟩,⟨1579901260968,1579901260977⟩,⟨313268670772,313268670779⟩,⟨-3959419704444,-3959419704440⟩,⟨-1570176793318,-1570176793308⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1663630862180,-1663629410984⟩,⟨-4105982070940,-4105940283584⟩,⟨445017913780,445044274451⟩,⟨41224072236259,41225604721302⟩,⟨-7703961283306,-7702767347627⟩,⟨2225579975352,2226691890135⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-183068455996,-183068295591⟩,⟨-1649944611367,-1649938951904⟩,⟨-237136013328,-237132853602⟩,⟨2338275057003,2338507567991⟩,⟨-200706924203,-200548246923⟩,⟨658519219774,658650950888⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51478541857,51478702268⟩,⟨-70043350399,-70037690927⟩,⟨76132657444,76135817177⟩,⟨-1621144647441,-1620912136449⟩,⟨-1770883717521,-1770725040231⟩,⟨308391388651,308523119767⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4337412983,4337453120⟩,⟨-29991875690,-29990432292⟩,⟨5421741490,5422615395⟩,⟨-47472245332,-47412047146⟩,⟨-299665960372,-299622027195⟩,⟨50883469992,50920290664⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2410197586,2410212608⟩,⟨-6558804274,-6558253888⟩,⟨7128979982,7129298074⟩,⟨-142880061484,-142856374307⟩,⟨-175524480014,-175507918594⟩,⟨39420630015,39433930366⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4316015384,4316042370⟩,⟨-29343386120,-29342290610⟩,⟨4917712911,4918331697⟩,⟨-68339176200,-68288144570⟩,⟨-284429967267,-284395811625⟩,⟨42409686162,42435690250⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4316042370,-4316015384⟩,⟨29342290610,29343386120⟩,⟨-4918331697,-4917712911⟩,⟨68288144570,68339176200⟩,⟨284395811625,284429967267⟩,⟨-42435690250,-42409686162⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨21370613,21437736⟩,⟨-649585080,-647046172⟩,⟨503409793,504902484⟩,⟨20815899238,20927129054⟩,⟨-15270148747,-15192059928⟩,⟨8447779742,8510604502⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56164640643,56164848169⟩,⟨-57604873926,-57597865481⟩,⟨128275164897,128278945871⟩,⟨-2157903336007,-2157639264969⟩,⟨-1732034409643,-1731845978159⟩,⟨457640649941,457799530110⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨21370613,21437736⟩,⟨-649585080,-647046172⟩,⟨503409793,504902484⟩,⟨20815899238,20927129054⟩,⟨-15270148747,-15192059928⟩,⟨8447779742,8510604502⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110810156236,111239652967⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨113816633344,117682103911⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111239652967,-110810156236⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438516160921,438945657652⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨45393274470,46980902421⟩,⟨-117682103911,-113816633344⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156203430706,158220555388⟩,⟨981829523865,985694994432⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44963777739,47410399152⟩,⟨-117682103911,-113816633344⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2145655400192,-2131547770048⟩,⟨6822962890858,6938279799108⟩,⟨3047351317393,3089726341918⟩,⟨-43782826260848,-42339545516394⟩,⟨-27236620794938,-26550945307442⟩,⟨-8682408286349,-8445886170755⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308761435999,-302820876090⟩,⟨-954234180076,-904981833544⟩,⟨-423660267542,-405507241453⟩,⟨5885003452487,6425100829534⟩,⟨3654556417377,3913446466859⟩,⟨1181333700686,1267078484500⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨302820876090,308761435999⟩,⟨904981833544,954234180076⟩,⟨405507241453,423660267542⟩,⟨-6425100829534,-5885003452487⟩,⟨-3913446466859,-3654556417377⟩,⟨-1267078484500,-1181333700686⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158220555388,-156203430706⟩,⟨-985694994432,-981829523865⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941291072388,943308197070⟩,⟨-985694994432,-981829523865⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-170829990528,-168476330560⟩,⟨-1151379355027,-1144411742987⟩,⟨-512727538493,-511130529129⟩,⟨-1205693860523,-1191145418020⟩,⟨744666302911,752324029479⟩,⟨-239096633531,-237609508810⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146560824188,-144232459083⟩,⟨-837363175487,-826583609748⟩,⟨-372693190221,-369379923862⟩,⟨1009442322952,1044648512095⟩,⟨1379525447167,1396272342213⟩,⟨202577375988,205963573357⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144232459083,146560824188⟩,⟨826583609748,837363175487⟩,⟨369379923862,372693190221⟩,⟨-1044648512095,-1009442322952⟩,⟨-1396272342213,-1379525447167⟩,⟨-205963573357,-202577375988⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨447053335173,455322260187⟩,⟨1731565443292,1791597355563⟩,⟨774887165315,796353457763⟩,⟨-7469749341629,-6894445775439⟩,⟨-5309718809072,-5034081864544⟩,⟨-1473042057857,-1383911076674⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨805895234382,816053657214⟩,⟨4128457527371,4202683035413⟩,⟨774887165315,796353457763⟩,⟨-19688050671274,-18899473998090⟩,⟨-5309718809072,-5034081864544⟩,⟨-1473042057857,-1383911076674⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89927555478,94820798304⟩,⟨-235364207822,-227633266688⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12749584914258,13443330169365⟩,⟨30607521924080,35184752203971⟩,⟨-131236557490292,-117925584469596⟩,⟨146957003641019,184175613045034⟩,⟨-391281381385432,-237466928818093⟩,⟨2181473917153848,2562316599372212⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9344903194459,9977592298898⟩,⟨70306283182601,77498681418061⟩,⟨-88417967151123,-76697710093444⟩,⟨96845444105848,186516860055463⟩,⟨-835384692641636,-649731362727944⟩,⟨1390813368144493,1719477492166768⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨83633618944,89244103424⟩,⟨-733523847118,-584070119022⟩,⟨637166959128,836874721379⟩,⟨6345258145660,11212143843149⟩,⟨-8312146994453,-941058442471⟩,⟨-6622513072377,4087262218864⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1183145246720,1188755731200⟩,⟨-733523847118,-584070119022⟩,⟨637166959128,836874721379⟩,⟨6345258145660,11212143843149⟩,⟨-8312146994453,-941058442471⟩,⟨-6622513072377,4087262218864⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨80605471488,85807041536⟩,⟨-681672855800,-540221906356⟩,⟨589332578601,777718111703⟩,⟨5446275069153,10154158384369⟩,⟨-7435025663684,-388241848538⟩,⟨-6704487701927,3482464503275⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨86736672938,92771745043⟩,⟨-794247194202,-624131851513⟩,⟨680870636883,906153769869⟩,⟨6899655937766,12762885906990⟩,⟨-9724880941822,-1112879595694⟩,⟨-7082462562409,5267994103668⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-89244103424,-83633618944⟩,⟨584070119022,733523847118⟩,⟨-836874721379,-637166959128⟩,⟨-11212143843149,-6345258145660⟩,⟨941058442471,8312146994453⟩,⟨-4087262218864,6622513072377⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1010267524352,1015878008832⟩,⟨584070119022,733523847118⟩,⟨-836874721379,-637166959128⟩,⟨-11212143843149,-6345258145660⟩,⟨941058442471,8312146994453⟩,⟨-4087262218864,6622513072377⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-93074687488,-86985481472⟩,⟨632154532057,798321216626⟩,⟨-910801807412,-689622645932⟩,⟨-12782228337179,-7231092337172⟩,⟨1415024902895,9707722837292⟩,⟨-5202799473927,6774989733637⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-85995023436,-79925127485⟩,⟨518750940748,691390002829⟩,⟨-791114190940,-562805789816⟩,⟨-10636353355211,-4629869790234⟩,⟨-618716939962,8162194501666⟩,⟨-4568381315052,7992128077410⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨741649502,12846617558⟩,⟨-275496253454,67258151316⟩,⟨-110243554057,343347980053⟩,⟨-3736697417445,8133016116756⟩,⟨-10343597881784,7049314905972⟩,⟨-11650843877461,13260122181078⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨370824751,6423308779⟩,⟨-137748126727,33629075658⟩,⟨-55121777029,171673990027⟩,⟨-1868348708723,4066508058378⟩,⟨-5171798940892,3524657452986⟩,⟨-5825421938731,6630061090539⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6423308779,-370824751⟩,⟨-33629075658,137748126727⟩,⟨-171673990027,55121777029⟩,⟨-4066508058378,1868348708723⟩,⟨-3524657452986,5171798940892⟩,⟨-6630061090539,5825421938731⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755700074837,761752578129⟩,⟨-33629075658,137748126727⟩,⟨-171673990027,55121777029⟩,⟨-4066508058378,1868348708723⟩,⟨-3524657452986,5171798940892⟩,⟨-6630061090539,5825421938731⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6361535468,7243679644⟩,⟨-119075917750,-88853808430⟩,⟨96931359918,135853286680⟩,⟨1585821893584,2798833445985⟩,⟨-2465963318594,-820099203038⟩,⟨-336583084853,1937448089785⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7243679644,-6361535468⟩,⟨88853808430,119075917750⟩,⟨-135853286680,-96931359918⟩,⟨-2798833445985,-1585821893584⟩,⟨820099203038,2465963318594⟩,⟨-1937448089785,336583084853⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092267948132,1093150092308⟩,⟨88853808430,119075917750⟩,⟨-135853286680,-96931359918⟩,⟨-2798833445985,-1585821893584⟩,⟨820099203038,2465963318594⟩,⟨-1937448089785,336583084853⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7267646016,-6380009984⟩,⟨89370888982,119865602922⟩,⟨-136754235655,-97495447400⟩,⟨-2830462094976,-1602314785270⟩,⟨832796390798,2497225596748⟩,⟨-1967305933483,330170152872⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3633823008,-3190004992⟩,⟨44685444491,59932801461⟩,⟨-68377117828,-48747723700⟩,⟨-1415231047488,-801157392635⟩,⟨416398195399,1248612798374⟩,⟨-983652966742,165085076436⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3190004992,3633823008⟩,⟨-59932801461,-44685444491⟩,⟨48747723700,68377117828⟩,⟨801157392635,1415231047488⟩,⟨-1248612798374,-416398195399⟩,⟨-165085076436,983652966742⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765313388608,765757225888⟩,⟨-59932801461,-44685444491⟩,⟨48747723700,68377117828⟩,⟨801157392635,1415231047488⟩,⟨-1248612798374,-416398195399⟩,⟨-165085076436,983652966742⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273066987033,273287523077⟩,⟨22213452107,29768979438⟩,⟨-33963321670,-24232839979⟩,⟨-699708361497,-396455473396⟩,⟨205024800759,616490829649⟩,⟨-484362022447,84145771214⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530626777216,1531514451776⟩,⟨-119865602922,-89370888982⟩,⟨97495447400,136754235656⟩,⟨1602314785270,2830462094976⟩,⟨-2497225596748,-832796390798⟩,⟨-330170152872,1967305933484⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1190030504749,1196639296498⟩,⟨-868842597850,-684197563590⟩,⟨746396822637,991259397843⟩,⟨8219775786108,14542212925206⟩,⟨-11284997558594,-1960653147371⟩,⟨-6907926348009,6483528662532⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1280549381722,1293766965220⟩,⟨-1737685195700,-1368395127180⟩,⟨1492793645274,1982518795686⟩,⟨16439551572221,29084425850397⟩,⟨-22569995117178,-3921306294740⟩,⟨-13811075071607,12967057325058⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨167590953024,178881728960⟩,⟨-1492019835672,-1162934588818⟩,⟨1268655032143,1702240069189⟩,⟨11946553591478,23742597246038⟩,⟨-18037325891188,-1022620819705⟩,⟨-14493904592968,9670020116729⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57481822382,61829201392⟩,⟨-510922180519,-390253830652⟩,⟨423993903836,584269191816⟩,⟨3847269106788,7964403305023⟩,⟨-6107193947492,-7640196637⟩,⟨-5387618793423,3388438139414⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380135718229,380663360450⟩,⟨1130257154,19269812439⟩,⟨-23094371407,256288853⟩,⟨-583177780125,148005837785⟩,⟨-331340494961,659290419034⟩,⟨-765183428241,601890357955⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175839718814,3180247900005⟩,⟨-161212897405,-9429632413⟩,⟨-2144134444,193209484527⟩,⟨-1238173488996,4895259524240⟩,⟨-5535268302296,2772240273378⟩,⟨-5035726689176,6425066040496⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨166031035978,178835933081⟩,⟨-1486866364179,-1127705807683⟩,⟨1224547404686,1700815899714⟩,⟨11049555415078,23461490275371⟩,⟨-18151275694860,131184371111⟩,⟨-15868703318875,10367423490694⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨333621989002,357717662041⟩,⟨-2978886199851,-2290640396501⟩,⟨2493202436829,3403055968903⟩,⟨22996109006556,47204087521409⟩,⟨-36188601586048,-891436448594⟩,⟨-30362607911843,20037443607423⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519396601802,527749753280⟩,⟨-46597115366,190866541138⟩,⟨-237874891356,76377829398⟩,⟨-5643060539347,2623335589544⟩,⟨-4926850437858,7179958808262⟩,⟨-9203957423363,8125429557132⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356983992652,365630271670⟩,⟨-48424416624,198351353616⟩,⟨-247203131625,79372978402⟩,⟨-5873109211837,2762077415989⟩,⟨-5164758263769,7475873238920⟩,⟨-9582777760849,8499778930784⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713967985304,731260543340⟩,⟨-96848833248,396702707232⟩,⟨-494406263250,158745956804⟩,⟨-11746218423674,5524154831978⟩,⟨-10329516527538,14951746477840⟩,⟨-19165555521698,16999557861568⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523383097572,1525152916308⟩,⟨-31011794492,29705028768⟩,⟨-38357839280,39822875738⟩,⟨-1196518660715,1244640201392⟩,⟨-1677126393710,1633166927796⟩,⟨-2267618242657,2303889018337⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989208966547,1014345025630⟩,⟨-154966057526,570029811861⟩,⟨-711311011974,246684755187⟩,⟨-17111552639174,8511874741748⟩,⟨-15470879247824,21854339636420⟩,⟨-28128852139314,25147162064815⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67816999405,67926585207⟩,⟨11033553962,14798371296⟩,⟨-16883408634,-12036595944⟩,⟨-346932442945,-195309820765⟩,⟨99997944172,305482820850⟩,⟨-239711638377,43927678439⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49706974669,50414872276⟩,⟨262727089859,270620305238⟩,⟨35263615305,40375503609⟩,⟨-1390939744433,-1195730094577⟩,⟨-311491981983,-118246857363⟩,⟨-293372611597,-69721283072⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130780859379,2133253034116⟩,⟨-333922622570,-248825882916⟩,⟨271446228810,380971120192⟩,⟨4475683584424,7911260338779⟩,⟨-6986609550358,-2334515939818⟩,⟨-902500684616,5514555940255⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966253523249,2971417280645⟩,⟨-697683375039,-519584626893⟩,⟨566819198489,795984455568⟩,⟨9376215890855,16584047503446⟩,⟨-14659816081314,-4907904440327⟩,⟨-1849548224137,11592949065713⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134099071821,136245601137⟩,⟨676792785912,707858700108⟩,⟨120758787198,145611851441⟩,⟨-3678554679021,-2713726537973⟩,⟨-1404165207086,-361633387936⟩,⟨-841283505843,401926255482⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8873136523497,9015169181994⟩,⟨-47587696557203,-44076834315376⟩,⟨-9789146619869,-7864541653291⟩,⟨614632930098269,749695888745752⟩,⟨101685136385304,197745232269476⟩,⟨-13079384553637,77816680758375⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7982986253808,8316867038019⟩,⟨-45172226700791,-34981243997270⟩,⟨-14863109111492,-5052943669023⟩,⟨363328628872032,774830588654135⟩,⟨-51117249147472,393783102419110⟩,⟨-247094281863900,290642800861595⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15965972507616,16633734076038⟩,⟨-90344453401582,-69962487994540⟩,⟨-29726218222984,-10105887338046⟩,⟨726657257744064,1549661177308270⟩,⟨-102234498294944,787566204838220⟩,⟨-494188563727800,581285601723190⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10867759718499,10909882818322⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108414,2148278590204846⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9768248090723,9810371190546⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108424,2148278590204831⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2401631390336,2406362620352⟩,⟨-12184942684160,-12039116462039⟩,⟨0,0⟩,⟨102958094106835,109987257462969⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7640763342348,7739431932773⟩,⟨-48838359576370,-47414364182868⟩,⟨-21748498251478,-21176756706330⟩,⟨588454799641736,616372205823158⟩,⟨315920001199464,328957993406502⟩,⟨117384874915209,122230463502517⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6541251714572,6639920304997⟩,⟨-48838359576371,-47414364182868⟩,⟨-21748498251479,-21176756706330⟩,⟨588454799641739,616372205823153⟩,⟨315920001199465,328957993406500⟩,⟨117384874915208,122230463502518⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1960717779584,1977179068928⟩,⟨-8209184813376,-7851396153547⟩,⟨-3655680557423,-3506682184062⟩,⟨36151372016631,47540034535628⟩,⟨25019457653133,30253650957013⟩,⟨7283401653968,9361688255037⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99599284960,100028781692⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133725638806,135742763489⟩,⟨698701256585,706176277220⟩,⟨312248741132,314287997914⟩,⟨-1767320322048,-1753486165276⟩,⟨-1574120613484,-1566232973144⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4362349169920,4383541689280⟩,⟨-20394127497536,-19890512615586⟩,⟨-3655680557423,-3506682184062⟩,⟨139109466123466,157527291998597⟩,⟨25019457653133,30253650957013⟩,⟨7283401653968,9361688255037⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨667243978004,715435324082⟩,⟨-5957772399702,-4581280793002⟩,⟨4986404873658,6806111937806⟩,⟨45992218013112,94408175042818⟩,⟨-72377203172096,-1782872897188⟩,⟨-60725215823686,40074887214846⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5029593147924,5098977013362⟩,⟨-26351899897238,-24471793408588⟩,⟨1330724316235,3299429753744⟩,⟨185101684136578,251935467041415⟩,⟨-47357745518963,28470778059825⟩,⟨-53441814169718,49436575469883⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨455605805812,463882732695⟩,⟨1614505267256,1854436515516⟩,⟨120543691424,300167756492⟩,⟨-35511204050731,-26179352108224⟩,⟨-3246940969933,5224535897847⟩,⟨-4861903619538,4497524437536⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33376496878,35436409591⟩,⟨-714988627521,-673623208946⟩,⟨325509421405,328085365043⟩,⟨8310340911970,9001121512395⟩,⟨-6627114036394,-6561817940510⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨488982302690,499319142286⟩,⟨899516639735,1180813306570⟩,⟨446053112829,628253121535⟩,⟨-27200863138761,-17178230595829⟩,⟨-9874055006327,-1337282042663⟩,⟨-4861903619538,4497524437536⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502387216868,503376923070⟩,⟨2513460839922,2553938535635⟩,⟨0,0⟩,⟨2096765778922,4420352332343⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨223425066129,228597612908⟩,⟨1528809234867,1700413638943⟩,⟨203809924577,287625992521⟩,⟨-7408021461011,-356074188391⟩,⟨-3500858288761,848273388002⟩,⟨-2225870124918,2059050541720⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-715435324082,-667243978004⟩,⟨4581280793002,5957772399702⟩,⟨-6806111937806,-4986404873658⟩,⟨-94408175042818,-45992218013112⟩,⟨1782872897188,72377203172096⟩,⟨-40074887214846,60725215823686⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3646913845838,3716297711276⟩,⟨-15812846704534,-13932740215884⟩,⟨-10461792495229,-8493087057720⟩,⟨44701291080648,111535073985485⟩,⟨26802330550321,102630854129109⟩,⟨-32791485560878,70086904078723⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443547727359,458804171355⟩,⟨365274696780,692304363023⟩,⟨-255903039007,29325997368⟩,⟨-20848796519954,-9753766788809⟩,⟨-13299904520182,-1878226748237⟩,⟨-11213789427256,2668677761531⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨312406861412,316441110776⟩,⟨1963659047730,1971389988864⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-316441110776,-312406861412⟩,⟨-1971389988864,-1963659047730⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨783070517000,787104766364⟩,⟨-1971389988864,-1963659047730⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1396420234732,1415398464004⟩,⟨-9421709835122,-9093471865575⟩,⟨-4195637233776,-4061432534884⟩,⟨53791158064788,63469994794787⟩,⟨34265685854616,38721009084765⟩,⟨10781481555013,12539394331297⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1415398464004,-1396420234732⟩,⟨9093471865575,9421709835122⟩,⟨4061432534884,4195637233776⟩,⟨-63469994794787,-53791158064788⟩,⟨-38721009084765,-34265685854616⟩,⟨-12539394331297,-10781481555013⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-315886836228,-296908606956⟩,⟨9093471865575,9421709835122⟩,⟨4061432534884,4195637233776⟩,⟨-63469994794787,-53791158064788⟩,⟨-38721009084765,-34265685854616⟩,⟨-12539394331297,-10781481555013⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13620884595,-12141874878⟩,⟨402606006803,440069244600⟩,⟨39981564194,62498305383⟩,⟨-4753629636134,-4082385550504⟩,⟨1804945827165,2255516491245⟩,⟨2698934545790,2909052772668⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429926842764,446662296477⟩,⟨767880703583,1132373607623⟩,⟨-215921474813,91824302751⟩,⟨-25602426156088,-13836152339313⟩,⟨-11494958693017,377289743008⟩,⟨-8514854881466,5577730534199⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100028781692,-99599284960⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4073044794,4313191737⟩,⟨25159432796,27544158341⟩,⟨39722996071,39933365192⟩,⟨-282744407988,-271500653359⟩,⟨249756374792,250871388573⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8896633727,9439739525⟩,⟨7155621882,15684574839⟩,⟨86765789348,87397126939⟩,⟨-847904290487,-712537298238⟩,⟨102988436616,114103164432⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1481429326279,1500102951399⟩,⟨-7822924067859,-7494627343770⟩,⟨-1482341775186,-1406697416408⟩,⟨110140718789587,118239492416170⟩,⟨23371769014723,25344175331640⟩,⟨5183764527568,5671519746044⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11986898342,12878973505⟩,⟨-57521735854,-39243311575⟩,⟨104177583682,107856809689⟩,⟨-488817541891,-42456193602⟩,⟨-315095193907,-227313780513⟩,⟨-193710339097,-173321272361⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12878973505,-11986898342⟩,⟨39243311575,57521735854⟩,⟨-107856809689,-104177583682⟩,⟨42456193602,488817541891⟩,⟨227313780513,315095193907⟩,⟨173321272361,193710339097⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112907755197,-111586183302⟩,⟨-838648003729,-819510585988⟩,⟨-107856809689,-104177583682⟩,⟨2241479449154,2687840797443⟩,⟨227313780513,315095193907⟩,⟨173321272361,193710339097⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨80182215651,85254986382⟩,⟨-565595947916,-524042414507⟩,⟨624358252891,645923581380⟩,⟨3103870049753,3807181468346⟩,⟨-3868289522610,-3396280817161⟩,⟨-2620982704443,-2393455580150⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨108033678508,116316420366⟩,⟨-1378244119807,-1252617609649⟩,⟨726291180471,778672761234⟩,⟨19358136524463,22410766887520⟩,⟨-7498487617933,-6104126999172⟩,⟨-4939517731858,-4382651451464⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-116316420366,-108033678508⟩,⟨1252617609649,1378244119807⟩,⟨-778672761234,-726291180471⟩,⟨-22410766887520,-19358136524463⟩,⟨6104126999172,7498487617933⟩,⟨4382651451464,4939517731858⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨983195207410,991477949268⟩,⟨1252617609649,1378244119807⟩,⟨-778672761234,-726291180471⟩,⟨-22410766887520,-19358136524463⟩,⟨6104126999172,7498487617933⟩,⟨4382651451464,4939517731858⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119578914729,122405214618⟩,⟨777133042824,806944510937⟩,⟨183083351054,195073760174⟩,⟨-2768454180169,-2151984302630⟩,⟨-821437020396,-542370159587⟩,⟨-228161376054,-115478829544⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11324551727,11594385054⟩,⟨166339411344,172239858334⟩,⟨21145349726,22151416970⟩,⟨669605523906,824388439430⟩,⟨90581928148,118395875608⟩,⟨-20042408514,-14019256687⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164443446496,175403254401⟩,⟨1462724038192,1885108019068⟩,⟨-6412981646,231026329294⟩,⟨-11097527587072,7644292355908⟩,⟨-6239510947395,7221681442126⟩,⟨-6712205777338,5537397539024⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-175403254401,-164443446496⟩,⟨-1885108019068,-1462724038192⟩,⟨-231026329294,6412981646⟩,⟨-7644292355908,11097527587072⟩,⟨-7221681442126,6239510947395⟩,⟨-5537397539024,6712205777338⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48021811728,64154166412⟩,⟨-356298784201,237689600751⟩,⟨-27216404717,294038974167⟩,⟨-15052313816919,10741453398681⟩,⟨-10722539730887,7087784335397⟩,⟨-7763267663942,8771256319058⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28471518966427,29911344293630⟩,⟨-286651410921055,-238771344128289⟩,⟨-108758899594239,-68941866926124⟩,⟨2819950200244862,4854914155484565⟩,⟨474761325741821,2396235760366664⟩,⟨-718442991976274,1384582604933090⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13004971013,13626992373⟩,⟨169036367626,179669252332⟩,⟨39822968436,43433911708⟩,⟨482145948199,716368042613⟩,⟨75909969232,168361411736⟩,⟨10170645016,44101286763⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336759766336,370711550710⟩,⟨824480190702,2063583866729⟩,⟨-316719064488,366144109795⟩,⟨-47843142273612,6242160382193⟩,⟨-21514545405237,15031342736107⟩,⟨-17233371494962,13365830262353⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370711550710,-336759766336⟩,⟨-2063583866729,-824480190702⟩,⟨-366144109795,316719064488⟩,⟨-6242160382193,47843142273612⟩,⟨-15031342736107,21514545405237⟩,⟨-13365830262353,17233371494962⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59215292054,109902530141⟩,⟨-1295703163146,307893416921⟩,⟨-582065584608,408543367239⟩,⟨-31844586538281,34006989934299⟩,⟨-26526301429124,21891835148245⟩,⟨-21880685143819,22811102029161⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨233324923766,235771545181⟩,⟨1575733578427,1584067592524⟩,⟨312248741132,314287997914⟩,⟨-3966343577600,-3952509420828⟩,⟨-1574120613484,-1566232973144⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1708101604045,-1620339330501⟩,⟨-5587026742257,-2622704466841⟩,⟨-606072802589,1539796479007⟩,⟨-22292957980491,104735872891511⟩,⟨-63412373569963,46801119841231⟩,⟨-55259802958721,59510237193678⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-190157646496,-176222255171⟩,⟨-1875582184740,-1430489090234⟩,⟨-370521114870,-98387350581⟩,⟨-7511217178168,12253292352283⟩,⟨-7696263247529,7179692879411⟩,⟨-6196779352324,7525917632125⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43167277270,59549290010⟩,⟨-299848606313,153578502290⟩,⟨-58272373738,215900647333⟩,⟨-11477560755768,8300782931455⟩,⟨-9270383861013,5613459906267⟩,⟨-6547250025857,7176132475641⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2586262422,6412579031⟩,⟨-111215644410,41723373231⟩,⟨-36682726312,53228528841⟩,⟨-3922833104421,3897655843278⟩,⟨-3098428111207,2256765393491⟩,⟨-2363994835057,2426227950139⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1694765002,3225175479⟩,⟨-32479459364,16635550806⟩,⟨-6312035992,23386256110⟩,⟨-1327008965608,1062680743060⟩,⟨-1121920441164,668360826202⟩,⟨-732079813624,862103995062⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3022210759,5799619840⟩,⟨-82485502197,17812627846⟩,⟨-22073651725,36648829195⟩,⟨-2578958531641,2535393691598⟩,⟨-2208827818520,1445726927518⟩,⟨-1460734523434,1619697865123⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5799619840,-3022210759⟩,⟨-17812627846,82485502197⟩,⟨-36648829195,22073651725⟩,⟨-2535393691598,2578958531641⟩,⟨-1445726927518,2208827818520⟩,⟨-1619697865123,1460734523434⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3213357418,3390368272⟩,⟨-129028272256,124208875428⟩,⟨-73331555507,75302180566⟩,⟨-6458226796019,6476614374919⟩,⟨-4544155038725,4465593212011⟩,⟨-3983692700180,3886962473573⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48021811728,64154166412⟩,⟨-356298784201,237689600751⟩,⟨-27216404717,294038974167⟩,⟨-15052313816919,10741453398681⟩,⟨-10722539730887,7087784335397⟩,⟨-7763267663942,8771256319058⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3213357418,3390368272⟩,⟨-129028272256,124208875428⟩,⟨-73331555507,75302180566⟩,⟨-6458226796019,6476614374919⟩,⟨-4544155038725,4465593212011⟩,⟨-3983692700180,3886962473573⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (517/5120) u, BivariateJet2.affineZ (539/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000009

end


