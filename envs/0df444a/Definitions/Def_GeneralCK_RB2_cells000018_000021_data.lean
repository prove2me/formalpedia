-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000018_000021_data
-- name    : GeneralCK_RB2_cells000018_000021_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T01:20:11.082822+00:00
-- url     : https://prove2.me/theorems/65aa072d-76d9-476f-a97e-7b8ca757fc10
-- title:
--   Exact certificate data for RB2 cells 000018–000021
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000018 through 000021. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000018Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2525295488000,-2525295430144⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-116561173120,-116561173056⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2109269613568,-2109269574720⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2109269613568,-2109269574720⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-174619424960,-174619424896⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-174619424960,-174619424896⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨90496699200,90496699264⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-98618625024,-98618624960⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨90496822528,90496822592⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-98618771456,-98618771392⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-8121948928,-8121948864⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-8121925760,-8121925696⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨189115324160,189115324224⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨189115593920,189115593984⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1934650149760,1934650188352⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1934650149824,1934650188416⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2116177416384,-2116177377472⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2102399829696,-2102399790912⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-175806205056,-175806204992⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-173434808448,-173434808384⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨87902486336,87902486400⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-95545468480,-95545468416⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨93113316864,93113316928⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-101734433344,-101734433280⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-8621116416,-8621116352⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-7642982080,-7642982016⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨183447954752,183447954816⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨194847750208,194847750272⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1926593585856,1926593624448⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1942742569088,1942742607680⟩



end LaneCBRB2Cell000018Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000018
open Set LaneCBRB2Cell000018Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110595407872,110595407872⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨127345780326,127345780327⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110595407872,-110595407872⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439160406016,439160406016⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50863695462,50863695463⟩,⟨-127345780327,-127345780326⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161459103334,161459103335⟩,⟨972165847449,972165847450⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨50863695462,50863695463⟩,⟨-127345780327,-127345780326⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2109269613568,-2109269574720⟩,⟨6620299700160,6620299700209⟩,⟨2990614730911,2990614730931⟩,⟨-39861668593023,-39861668592438⟩,⟨-25494377454772,-25494377454479⟩,⟨-8134317312267,-8134317312163⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309738225495,-309738219788⟩,⟨-892807500337,-892807465971⟩,⟨-403311539250,-403311523727⟩,⟨5853534519954,5853534520177⟩,⟨3653998745108,3653998784066⟩,⟨1194493579030,1194493579069⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309738219788,309738225495⟩,⟨892807465971,892807500337⟩,⟨403311523727,403311539250⟩,⟨-5853534520177,-5853534519954⟩,⟨-3653998784066,-3653998745108⟩,⟨-1194493579069,-1194493579030⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161459103335,-161459103334⟩,⟨-972165847450,-972165847449⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938052524441,938052524442⟩,⟨-972165847450,-972165847449⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-174619424960,-174619424896⟩,⟨-1139496590595,-1139496590590⟩,⟨-514749398667,-514749398665⟩,⟨-1180935651043,-1180935651033⟩,⟨755292497778,755292497786⟩,⟨-240986031193,-240986031191⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148977226127,-148977226072⟩,⟨-817770898918,-817770898854⟩,⟨-369414952129,-369414952099⟩,⟨1007519739366,1007519739389⟩,⟨1380023165262,1380023165341⟩,⟨205598148488,205598148494⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148977226072,148977226127⟩,⟨817770898854,817770898918⟩,⟨369414952099,369414952129⟩,⟨-1007519739389,-1007519739366⟩,⟨-1380023165341,-1380023165262⟩,⟨-205598148494,-205598148488⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨458715445860,458715451622⟩,⟨1710578364825,1710578399255⟩,⟨772726475826,772726491379⟩,⟨-6861054259566,-6861054259320⟩,⟨-5034021949407,-5034021910370⟩,⟨-1400091727563,-1400091727518⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨817561412353,817561423993⟩,⟨4119312621847,4119312714201⟩,⟨772726475826,772726491379⟩,⟨-19014596785180,-19014596784924⟩,⟨-5034021949407,-5034021910370⟩,⟨-1400091727563,-1400091727518⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨101727390924,101727390926⟩,⟨-254691560654,-254691560652⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11883975482021,11883975482256⟩,⟨29753522966765,29753522968176⟩,⟨-102607005850983,-102607005846923⟩,⟨148985855831346,148985855842526⟩,⟨-256893823956517,-256893823911835⟩,⟨1771830927251321,1771830927356450⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8836541182472,8836541308457⟩,⟨66646991817828,66646993132946⟩,⟨-67943317228277,-67943315970736⟩,⟨128206202240882,128206208842165⟩,⟨-608933699163868,-608933686932423⟩,⟨1158121118648321,1158121140393335⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨94325235200,94325369088⟩,⟨-703889497887,-703887457210⟩,⟨717578492421,717580571912⟩,⟨9095370370599,9095420774490⟩,⟨-4221499993379,-4221434020572⟩,⟨-1371586022114,-1371502340351⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1193836862976,1193836996864⟩,⟨-703889497887,-703887457210⟩,⟨717578492421,717580571912⟩,⟨9095370370599,9095420774490⟩,⟨-4221499993379,-4221434020572⟩,⟨-1371586022114,-1371502340351⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨90496699200,90496822592⟩,⟨-648275079786,-648273127638⟩,⟨660882430626,660884419934⟩,⟨7994518041318,7994567704218⟩,⟨-3498301700561,-3498238157970⟩,⟨-1660455177179,-1660375574034⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨98260257330,98260402328⟩,⟨-761824173796,-761821728279⟩,⟨776639619975,776642112106⟩,⟨10258985623997,10259050596019⟩,⟨-4992046831207,-4991966507459⟩,⟨-1053164817307,-1053066045064⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-94325369088,-94325235200⟩,⟨703887457210,703889497887⟩,⟨-717580571912,-717578492421⟩,⟨-9095420774490,-9095370370599⟩,⟨4221434020572,4221499993379⟩,⟨1371502340351,1371586022114⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1005186258688,1005186392576⟩,⟨703887457210,703889497887⟩,⟨-717580571912,-717578492421⟩,⟨-9095420774490,-9095370370599⟩,⟨4221434020572,4221499993379⟩,⟨1371502340351,1371586022114⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-98618771456,-98618624960⟩,⟨769939236706,769941571433⟩,⟨-784917398010,-784915018832⟩,⟨-10488080787090,-10488021058374⟩,⟨5167208456658,5167284568064⟩,⟨939866702657,939961833715⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-90158434542,-90158288604⟩,⟨640753226651,640755731662⟩,⟨-653218815890,-653216263112⟩,⟨-7786731683982,-7786664222126⟩,⟨3340298978421,3340381629147⟩,⟨1760739212700,1760840059973⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8101822788,8102113724⟩,⟨-121070947145,-121065996617⟩,⟨123420804085,123425848994⟩,⟨2472253940015,2472386373893⟩,⟨-1651747852786,-1651584878312⟩,⟨707574395393,707774014909⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4050911394,4051056862⟩,⟨-60535473573,-60532998308⟩,⟨61710402042,61712924497⟩,⟨1236126970007,1236193186947⟩,⟨-825873926393,-825792439156⟩,⟨353787197696,353887007455⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4051056862,-4050911394⟩,⟨60532998308,60535473573⟩,⟨-61712924497,-61710402042⟩,⟨-1236193186947,-1236126970007⟩,⟨825792439156,825873926393⟩,⟨-353887007455,-353787197696⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758072326754,758072491486⟩,⟨60532998308,60535473573⟩,⟨-61712924497,-61710402042⟩,⟨-1236193186947,-1236126970007⟩,⟨825792439156,825873926393⟩,⟨-353887007455,-353787197696⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8092001731,8092024704⟩,⟨-120771140584,-120770619024⟩,⟨123119680342,123120211896⟩,⟨2461784791840,2461800880702⟩,⟨-1643078527992,-1643060854348⟩,⟨701299604793,701319725259⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8092024704,-8092001731⟩,⟨120770619024,120771140584⟩,⟨-123120211896,-123119680342⟩,⟨-2461800880702,-2461784791840⟩,⟨1643060854348,1643078527992⟩,⟨-701319725259,-701299604793⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091419603072,1091419626045⟩,⟨120770619024,120771140584⟩,⟨-123120211896,-123119680342⟩,⟨-2461800880702,-2461784791840⟩,⟨1643060854348,1643078527992⟩,⟨-701319725259,-701299604793⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8121948928,-8121925696⟩,⟨121666036363,121666564352⟩,⟨-124033052195,-124032514088⟩,⟨-2493516238567,-2493499861364⟩,⟨1668967603783,1668985562412⟩,⟨-720511310377,-720490904455⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4060974464,-4060962848⟩,⟨60833018181,60833282176⟩,⟨-62016526098,-62016257044⟩,⟨-1246758119284,-1246749930682⟩,⟨834483801891,834492781206⟩,⟨-360255655189,-360245452227⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4060962848,4060974464⟩,⟨-60833282176,-60833018181⟩,⟨62016257044,62016526098⟩,⟨1246749930682,1246758119284⟩,⟨-834492781206,-834483801891⟩,⟨360245452227,360255655189⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766184346464,766184377344⟩,⟨-60833282176,-60833018181⟩,⟨62016257044,62016526098⟩,⟨1246749930682,1246758119284⟩,⟨-834492781206,-834483801891⟩,⟨360245452227,360255655189⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272854900768,272854906512⟩,⟨30192654756,30192785146⟩,⟨-30780052974,-30779920085⟩,⟨-615450220176,-615446197960⟩,⟨410765213587,410769631998⟩,⟨-175329931315,-175324901198⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532368692928,1532368754688⟩,⟨-121666564352,-121666036362⟩,⟨124032514088,124033052196⟩,⟨2493499861364,2493516238568⟩,⟨-1668985562412,-1668967603782⟩,⟨720490904454,720511310378⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1202688206429,1202688366625⟩,⟨-842191885516,-842189219523⟩,⟨858570307353,858573024150⟩,⟨12061949528766,12062020045639⟩,⟨-6253398260431,-6253310528412⟩,⟨-415253928877,-415145773349⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1305864785082,1305865105474⟩,⟨-1684383771032,-1684378439046⟩,⟨1717140614706,1717146048300⟩,⟨24123899057538,24124040091265⟩,⟨-12506796520857,-12506621056827⟩,⟨-830507708483,-830291695971⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨189115324160,189115593984⟩,⟨-1418216926473,-1418212089091⟩,⟨1445797168850,1445802098552⟩,⟨18482525690461,18482661900567⟩,⟨-8665597961779,-8665434921501⟩,⟨-2600427150947,-2600232136678⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨65033737446,65033843889⟩,⟨-480112681627,-480110949476⟩,⟨489449396807,489451161962⟩,⟨6087360482260,6087405821687⟩,⟨-2760712592223,-2760655923429⟩,⟨-1056569223671,-1056499191198⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380272747542,380272770874⟩,⟨11886149752,11886464833⟩,⟨-12117663684,-12117342564⟩,⟨-245636270030,-245626494721⟩,⟨165112028837,165122734077⟩,⟨-72501390701,-72489242661⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179101719105,3179101914163⟩,⟨-99371525695,-99368879405⟩,⟨101301664296,101304361310⟩,⟨2059663216451,2059745521063⟩,⟨-1386768588707,-1386678586037⟩,⟨612470068161,612572044206⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨188036998692,188037317997⟩,⟨-1394064072397,-1394058812778⟩,⟨1421174096906,1421179456795⟩,⟨17809454170572,17809594035534⟩,⟨-8152754704120,-8152582231041⟩,⟨-2928523778649,-2928312283589⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨377152322852,377152911981⟩,⟨-2812280998870,-2812270901869⟩,⟨2866971265756,2866981555347⟩,⟨36291979861033,36292255936101⟩,⟨-16818352665899,-16818017152542⟩,⟨-5528950929596,-5528544420267⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522662642279,522662869433⟩,⟨83470496742,83473928090⟩,⟨-85097545582,-85094048810⟩,⟨-1697953494483,-1697861270722⟩,⟨1131910857394,1132024025306⟩,⟨-481056907533,-480918604958⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360356430373,360356665295⟩,⟨86324699187,86328266628⟩,⟨-88007402700,-88003767233⟩,⟨-1749120815820,-1749024490710⟩,⟨1163587799164,1163705668315⟩,⟨-490342455383,-490198727293⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720712860746,720713330590⟩,⟨172649398374,172656533256⟩,⟨-176014805400,-176007534466⟩,⟨-3498241631640,-3498048981420⟩,⟨2327175598328,2327411336630⟩,⟨-980684910766,-980397454586⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524276668224,1524276752957⟩,⟨-895945328,-894895778⟩,⟨912302192,913371854⟩,⟨31698980662,31731446728⟩,⟨-25924708064,-25889075790⟩,⟨19171179195,19211705585⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨999139772942,999140479839⟩,⟨238760303530,238770896425⟩,⟨-243415132104,-243404337148⟩,⟨-4829191233448,-4828902252904⟩,⟨3209506941420,3209857645180⟩,⟨-1347270726906,-1346845217459⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67711695804,67711698656⟩,⟨14985223636,14985288670⟩,⟨-15276761546,-15276695266⟩,⟨-303802182112,-303800165051⟩,⟨202180610476,202182822318⟩,⟨-85296466819,-85293953555⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50348234848,50348237687⟩,⟨264823924018,264823988909⟩,⟨36227838015,36227890424⟩,⟨-1284597556583,-1284595514388⟩,⟨-206380164704,-206378206927⟩,⟨-171118887667,-171116920750⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135633450112,2135633622260⟩,⟨-339128822278,-339127336908⟩,⟨345723567976,345725081814⟩,⟨6977213611713,6977259774741⟩,⟨-4679517593454,-4679467110536⟩,⟨2036252717653,2036309920114⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2976392205274,2976392565154⟩,⟨-708956228309,-708953094536⟩,⟨722742659455,722745853296⟩,⟨14642306243371,14642403826885⟩,⟨-9840018351685,-9839911921467⟩,⟨4315330732518,4315450997041⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136293323294,136293347460⟩,⟨684417651904,684418059577⟩,⟨131164662738,131164964587⟩,⟨-3148442898107,-3148430849839⟩,⟨-858545183346,-858533968104⟩,⟨-217988501261,-217977323181⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8870028083868,8870029656603⟩,⟨-44542229503554,-44542187176559⟩,⟨-8536273807665,-8536251136091⟩,⟨652251852573892,652253480228730⟩,⟨141605901424886,141606945096655⟩,⟨30616123667450,30616940533156⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8060303885672,8060311017548⟩,⟨-38549964266765,-38549811369651⟩,⟨-9720712249743,-9720598725950⟩,⟨534405373663431,534410486902334⟩,⟨162577682838962,162582089929112⟩,⟨20731910485981,20736284736954⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16120607771344,16120622035096⟩,⟨-77099928533530,-77099622739302⟩,⟨-19441424499486,-19441197451900⟩,⟨1068810747326862,1068820973804668⟩,⟨325155365677924,325164179858224⟩,⟨41463820971962,41472569473908⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10931067056724,10931067056725⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603222,2160817149603840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9831555428948,9831555428949⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603232,2160817149603830⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2408734257088,2408734314944⟩,⟨-12153542525660,-12153542525558⟩,⟨0,0⟩,⟨107314718406763,107314718418708⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7487504851964,7487504852011⟩,⟨-45083221381973,-45083221381359⟩,⟨-20365625740247,-20365625739990⟩,⟨542903648226036,542903648237389⟩,⟨296236813363294,296236813368812⟩,⟨110786896297657,110786896299747⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6387993224188,6387993224235⟩,⟨-45083221381974,-45083221381359⟩,⟨-20365625740248,-20365625739989⟩,⟨542903648226038,542903648237388⟩,⟨296236813363294,296236813368812⟩,⟨110786896297656,110786896299748⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1934650149760,1934650188416⟩,⟨-7759796290890,-7759796290660⟩,⟨-3505364129637,-3505364129536⟩,⟨38680732936729,38680732945095⟩,⟨26249669950071,26249669954035⟩,⟨7893331280043,7893331281683⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99471065088,99471065088⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137749447709,137749447711⟩,⟨686648128387,686648128392⟩,⟨310182333234,310182333236⟩,⟨-1719138590394,-1719138590390⟩,⟨-1553186842216,-1553186842212⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4343384406848,4343384503360⟩,⟨-19913338816550,-19913338816218⟩,⟨-3505364129637,-3505364129536⟩,⟨145995451343492,145995451363803⟩,⟨26249669950071,26249669954035⟩,⟨7893331280043,7893331281683⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨754304645704,754305823962⟩,⟨-5624561997740,-5624541803738⟩,⟨5733942531512,5733963110694⟩,⟨72583959722066,72584511872202⟩,⟨-33636705331798,-33636034305084⟩,⟨-11057901859192,-11057088840534⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5097689052552,5097690327322⟩,⟨-25537900814290,-25537880619956⟩,⟨2228578401875,2228598981158⟩,⟨218579411065558,218579963236005⟩,⟨-7387035381727,-7386364351049⟩,⟨-3164570579149,-3163757558851⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461179806320,461179921647⟩,⟨1761804191132,1761807036405⟩,⟨201615937172,201617798948⟩,⟨-31221636450924,-31221551683797⟩,⟨1111957785131,1112034931519⟩,⟨-286293658114,-286220105462⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38148665418,38148667558⟩,⟨-767490923198,-767490912472⟩,⟨329378021832,329378040293⟩,⟨9579437751730,9579437779163⟩,⟨-6626565812353,-6626565719884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨499328471738,499328589205⟩,⟨994313267934,994316123933⟩,⟨530993959004,530995839241⟩,⟨-21642198699194,-21642113904634⟩,⟨-5514608027222,-5514530788365⟩,⟨-286293658114,-286220105462⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501892554988,501892567044⟩,⟨2532355881864,2532356003553⟩,⟨0,0⟩,⟨3194096148032,3194099067279⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227927778231,227927837327⟩,⟨1603908293772,1603909934160⟩,⟨242382079493,242382943586⟩,⟨-3848295280931,-3848241294825⟩,⟨-1294279267047,-1294239560200⟩,⟨-130684074065,-130650496447⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-754305823962,-754304645704⟩,⟨5624541803738,5624561997740⟩,⟨-5733963110694,-5733942531512⟩,⟨-72584511872202,-72583959722066⟩,⟨33636034305084,33636705331798⟩,⟨11057088840534,11057901859192⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3589078582886,3589079857656⟩,⟨-14288797012812,-14288776818478⟩,⟨-9239327240331,-9239306661048⟩,⟨73410939471290,73411491641737⟩,⟨59885704255155,59886375285833⟩,⟨18950420120577,18951233140875⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449648353039,449648512752⟩,⟨451255068221,451258394357⟩,⟨-145012978081,-145010040209⟩,⟨-14261386942031,-14261290548517⟩,⟨-7368351432441,-7368247014330⟩,⟨-3983987501135,-3983873625994⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨322918206668,322918206670⟩,⟨1944331694898,1944331694900⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-322918206670,-322918206668⟩,⟨-1944331694900,-1944331694898⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨776593421106,776593421108⟩,⟨-1944331694900,-1944331694898⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1366458107845,1366458135153⟩,⟨-8901959907713,-8901959839173⟩,⟨-4021318314838,-4021318283878⟩,⟨54764712758683,54764712765507⟩,⟨34807128775844,34807128856375⟩,⟨11175486797706,11175486799042⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1366458135153,-1366458107845⟩,⟨8901959839173,8901959907713⟩,⟨4021318283878,4021318314838⟩,⟨-54764712765507,-54764712758683⟩,⟨-34807128856375,-34807128775844⟩,⟨-11175486799042,-11175486797706⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-266946507377,-266946480069⟩,⟨8901959839173,8901959907713⟩,⟨4021318283878,4021318314838⟩,⟨-54764712765507,-54764712758683⟩,⟨-34807128856375,-34807128775844⟩,⟨-11175486799042,-11175486797706⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12349015248,-12349013983⟩,⟨442724815078,442724821422⟩,⟨79405046546,79405058891⟩,⟨-4595485492245,-4595485475985⟩,⟨1746577195535,1746577257568⟩,⟨2695361202620,2695361227426⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437299337791,437299498769⟩,⟨893979883299,893983215779⟩,⟨-65607931535,-65604981318⟩,⟨-18856872434276,-18856776024502⟩,⟨-5621774236906,-5621669756762⟩,⟨-1288626298515,-1288512398568⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99471065088,-99471065088⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4601557486,4601557487⟩,⟨29110580632,29110580635⟩,⟨39730142208,39730142208⟩,⟨-305182172777,-305182172772⟩,⟨251342618624,251342618624⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10080774839,10080775084⟩,⟨12909757250,12909758803⟩,⟨87038055949,87038058040⟩,⟨-863002501705,-863002485413⟩,⟨111463671483,111463684713⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1478697238074,1478697259128⟩,⟨-7450469564669,-7450469185466⟩,⟨-1397605767095,-1397605699165⟩,⟨109470007550685,109470015104021⟩,⟨23188647767330,23188649298031⟩,⟨5174223611099,5174223902496⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13557304475,13557304998⟩,⟨-50947060629,-50947053154⟩,⟨104240810782,104240816197⟩,⟨-331915058496,-331914896460⟩,⟨-243686914128,-243686828038⟩,⟨-173831359060,-173831339162⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13557304998,-13557304475⟩,⟨50947053154,50947060629⟩,⟨-104240816197,-104240810782⟩,⟨331914896460,331915058496⟩,⟨243686828038,243686914128⟩,⟨173831339162,173831359060⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113028370086,-113028369563⟩,⟨-827373758878,-827373751403⟩,⟨-104240816197,-104240810782⟩,⟨2530938152012,2530938314048⟩,⟨243686828038,243686914128⟩,⟨173831339162,173831359060⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨89497421907,89497423698⟩,⟨-583041995287,-583041990788⟩,⟨610567414414,610567429864⟩,⟨3586864884664,3586864885155⟩,⟨-3413712983121,-3413712944148⟩,⟨-2435035885722,-2435035885556⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨120362156475,120362160598⟩,⟨-1390563222019,-1390563161799⟩,⟨707370630926,707370671203⟩,⟨21636008953118,21636010278738⟩,⟨-6099685454600,-6099684817442⟩,⟨-4405834569197,-4405834375475⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-120362160598,-120362156475⟩,⟨1390563161799,1390563222019⟩,⟨-707370671203,-707370630926⟩,⟨-21636010278738,-21636008953118⟩,⟨6099684817442,6099685454600⟩,⟨4405834375475,4405834569197⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨979149467178,979149471301⟩,⟨1390563161799,1390563222019⟩,⟨-707370671203,-707370630926⟩,⟨-21636010278738,-21636008953118⟩,⟨6099684817442,6099685454600⟩,⟨4405834375475,4405834569197⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122670188219,122670188738⟩,⟨785694698233,785694708363⟩,⟨187605971430,187605977645⟩,⟨-2504736515710,-2504736267913⟩,⟨-668442664403,-668442536589⟩,⟨-159548609670,-159548561346⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11619169823,11619169932⟩,⟨170105897522,170105899848⟩,⟨21431640350,21431641566⟩,⟨724829973632,724830031857⟩,⟨106779363614,106779391116⟩,⟨-15973871183,-15973864870⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170355705763,170355858096⟩,⟨1679266717627,1679272197629⟩,⟨108773613645,108776310773⟩,⟨-1934415336249,-1934201959172⟩,⟨491040381947,491176560687⟩,⟨-553933973794,-553832325251⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170355858096,-170355705763⟩,⟨-1679272197629,-1679266717627⟩,⟨-108776310773,-108773613645⟩,⟨1934201959172,1934415336249⟩,⟨-491176560687,-491040381947⟩,⟨553832325251,553933973794⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57571920135,57572131564⟩,⟨-75363903857,-75356783467⟩,⟨133605768720,133609329941⟩,⟨-1914093321759,-1913825958576⟩,⟨-1785455827734,-1785279942147⟩,⟨423148251186,423283477347⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28365080869710,28365106534313⟩,⟨-249432682120671,-249432040678847⟩,⟨-85602556100883,-85602110438977⟩,⟨3536012199628718,3536035049480487⟩,⟨1339999011289129,1340017449641532⟩,⟨312648114590151,312665059642034⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13686053605,13686053722⟩,⟨175316593440,175316596444⟩,⟨41861603360,41861604926⟩,⟨563995231842,563995318456⟩,⟨118967417266,118967458760⟩,⟨28420149564,28420164742⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353071315924,353071638401⟩,⟨1418011618807,1418023799336⟩,⟨14412383375,14418957340⟩,⟨-20979818936402,-20979312821766⟩,⟨-3397310562216,-3396980991558⟩,⟨-1893442524132,-1893196335064⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353071638401,-353071315924⟩,⟨-1418023799336,-1418011618807⟩,⟨-14418957340,-14412383375⟩,⟨20979312821766,20979818936402⟩,⟨3396980991558,3397310562216⟩,⟨1893196335064,1893442524132⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84227699390,84228182845⟩,⟨-524043916037,-524028403028⟩,⟨-80026888875,-80017364693⟩,⟨2122440387490,2123042911900⟩,⟨-2224793245348,-2224359194546⟩,⟨604570036549,604930125564⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237220512797,237220512799⟩,⟨1564968940419,1564968940424⟩,⟨310182333234,310182333236⟩,⟨-3918161845946,-3918161845942⟩,⟨-1553186842216,-1553186842212⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1657179048743,-1657177574779⟩,⟨-4204898683824,-4204856368943⟩,⟨470190618033,470215399168⟩,⟨43267916093451,43269464343366⟩,⟨-7914726514181,-7913615495027⟩,⟨1971622874407,1972568018264⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-184887964390,-184887799160⟩,⟨-1653327239708,-1653321448198⟩,⟨-230300724034,-230297698166⟩,⟨2592917457860,2593154497146⟩,⟨-257033085630,-256883082723⟩,⟨620894554556,621008751870⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52332548407,52332713639⟩,⟨-88358299289,-88352507774⟩,⟨79881609200,79884635070⟩,⟨-1325244388086,-1325007348796⟩,⟨-1810219927846,-1810069924935⟩,⟨270080870844,270195068158⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4410276580,4410318092⟩,⟨-33213009333,-33211517685⟩,⟨6044490827,6045336471⟩,⟨36334819002,36397012926⟩,⟨-311464732115,-311422564710⟩,⟨44621977902,44654327086⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2490829158,2490844888⟩,⟨-8411060798,-8410482932⟩,⟨7604118182,7604430232⟩,⟨-111954194715,-111929370480⟩,⟨-185158917890,-185142766830⟩,⟨37316734478,37328565759⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4382748560,4382776326⟩,⟨-32378838371,-32377710271⟩,⟨5438769272,5439368760⟩,⟨9351571923,9403965419⟩,⟨-293185909333,-293153064017⟩,⟨35054810476,35077732200⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4382776326,-4382748560⟩,⟨32377710271,32378838371⟩,⟨-5439368760,-5438769272⟩,⟨-9403965419,-9351571923⟩,⟨293153064017,293185909333⟩,⟨-35077732200,-35054810476⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨27500254,27569532⟩,⟨-835299062,-832679314⟩,⟨605122067,606567199⟩,⟨26930853583,27045441003⟩,⟨-18311668098,-18236655377⟩,⟨9544245702,9599516610⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57571920135,57572131564⟩,⟨-75363903857,-75356783467⟩,⟨133605768720,133609329941⟩,⟨-1914093321759,-1913825958576⟩,⟨-1785455827734,-1785279942147⟩,⟨423148251186,423283477347⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨27500254,27569532⟩,⟨-835299062,-832679314⟩,⟨605122067,606567199⟩,⟨26930853583,27045441003⟩,⟨-18311668098,-18236655377⟩,⟨9544245702,9599516610⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110380659507,110810156237⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨125413045043,129278515610⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110810156237,-110380659507⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438945657651,439375154381⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50067239075,51660906824⟩,⟨-129278515610,-125413045043⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160447898582,162471063061⟩,⟨970233112166,974098582733⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49637742345,52090403554⟩,⟨-129278515610,-125413045043⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2116177416384,-2102399790912⟩,⟨6565985156871,6675267970355⟩,⟨2970534232103,3010934362291⟩,⟨-40526358567188,-39210282084475⟩,⟨-25814440396097,-25180093090717⟩,⟨-8245229522819,-8025448209173⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312700280543,-306795871830⟩,⟨-916649607072,-868822106706⟩,⟨-412164630521,-394401970168⟩,⟨5599496824261,6105920670335⟩,⟨3530417223810,3776733540933⟩,⟨1153416631873,1235269519553⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306795871830,312700280543⟩,⟨868822106706,916649607072⟩,⟨394401970168,412164630521⟩,⟨-6105920670335,-5599496824261⟩,⟨-3776733540933,-3530417223810⟩,⟨-1235269519553,-1153416631873⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162471063061,-160447898582⟩,⟨-974098582733,-970233112166⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937040564715,939063729194⟩,⟨-974098582733,-970233112166⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175806205056,-173434808384⟩,⟨-1142995040606,-1136006593924⟩,⟨-515557286835,-513943664891⟩,⟨-1188198132559,-1173712900198⟩,⟨751427051549,759150660362⟩,⟨-241743069645,-240232194011⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150151418471,-147806941449⟩,⟨-823159090384,-812389485062⟩,⟨-371085381961,-367746164095⟩,⟨990065615719,1024966968032⟩,⟨1371615312528,1388438710372⟩,⟨203885548648,207309143891⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147806941449,150151418471⟩,⟨812389485062,823159090384⟩,⟨367746164095,371085381961⟩,⟨-1024966968032,-990065615719⟩,⟨-1388438710372,-1371615312528⟩,⟨-207309143891,-203885548648⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨454602813279,462851699014⟩,⟨1681211591768,1739808697456⟩,⟨762148134263,783250012482⟩,⟨-7130887638367,-6589562439980⟩,⟨-5165172251305,-4902032536338⟩,⟨-1442578663444,-1357302180521⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨812503990181,822643851852⟩,⟨4082818473092,4155658106934⟩,⟨762148134263,783250012482⟩,⟨-19391761267025,-18635526228580⟩,⟨-5165172251305,-4902032536338⟩,⟨-1442578663444,-1357302180521⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨99275484690,104180807108⟩,⟨-258557031220,-250826090086⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11604112630471,12177485946200⟩,⟨27938103771851,31715530010301⟩,⟨-107790655151005,-97783363201591⟩,⟨134527760497108,165202382212263⟩,⟨-316531761278795,-201107105839689⟩,⟨1647965066093338,1908246971372329⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8575068763791,9111075946436⟩,⟨63734938707281,69754654728608⟩,⟨-72604295342884,-63584008562656⟩,⟨92126223770264,166666520781034⟩,⟨-682066325768843,-540853394325018⟩,⟨1048244618227199,1277846000253877⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨91511789568,97169711360⟩,⟨-782055685772,-633369436092⟩,⟨631869559533,814004487661⟩,⟨6839363285998,11620459368985⟩,⟨-7673332203090,-1040327002881⟩,⟨-5659840937841,3164149247421⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1191023417344,1196681339136⟩,⟨-782055685772,-633369436092⟩,⟨631869559533,814004487661⟩,⟨6839363285998,11620459368985⟩,⟨-7673332203090,-1040327002881⟩,⟨-5659840937841,3164149247421⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨87902486336,93113316928⟩,⟨-721966761992,-581940268378⟩,⟨580562180776,751460790958⟩,⟨5809950250544,10419601748437⟩,⟨-6776479841468,-462425256903⟩,⟨-5738554993241,2614485740634⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨95218565246,101342237752⟩,⟨-852000039666,-681010747335⟩,⟨679398051807,886806231823⟩,⟨7510743852470,13351563131406⟩,⟨-9094169175155,-1252944750382⟩,⟨-6057734115646,4226163256335⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-97169711360,-91511789568⟩,⟨633369436092,782055685772⟩,⟨-814004487661,-631869559533⟩,⟨-11620459368985,-6839363285998⟩,⟨1040327002881,7673332203090⟩,⟨-3164149247421,5659840937841⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1002341916416,1007999838208⟩,⟨633369436092,782055685772⟩,⟨-814004487661,-631869559533⟩,⟨-11620459368985,-6839363285998⟩,⟨1040327002881,7673332203090⟩,⟨-3164149247421,5659840937841⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-101734433344,-95545468416⟩,⟨690870209759,857870259632⟩,⟨-892916263989,-689234166127⟩,⟨-13416312627718,-7894381757886⟩,⟨1567848953527,9113884267083⟩,⟨-4196029984051,5776471324293⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-93267128570,-87101605383⟩,⟨557453111476,731431558471⟩,⟨-763691038257,-553005529257⟩,⟨-10909405899771,-4901143495423⟩,⟨-550919013364,7470876540175⟩,⟨-3578303292432,6910577924818⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1951436676,14240632369⟩,⟨-294546928190,50420811136⟩,⟨-84292986450,333800702566⟩,⟨-3398662047301,8450419635983⟩,⟨-9645088188519,6217931789793⟩,⟨-9636037408078,11136741181153⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨975718338,7120316185⟩,⟨-147273464095,25210405568⟩,⟨-42146493225,166900351283⟩,⟨-1699331023651,4225209817992⟩,⟨-4822544094260,3108965894897⟩,⟨-4818018704039,5568370590577⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7120316185,-975718338⟩,⟨-25210405568,147273464095⟩,⟨-166900351283,42146493225⟩,⟨-4225209817992,1699331023651⟩,⟨-3108965894897,4822544094260⟩,⟨-5568370590577,4818018704039⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755003067431,761147684542⟩,⟨-25210405568,147273464095⟩,⟨-166900351283,42146493225⟩,⟨-4225209817992,1699331023651⟩,⟨-3108965894897,4822544094260⟩,⟨-5568370590577,4818018704039⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7616479369,8587406052⟩,⟨-138228870590,-105430027458⟩,⟨105180359544,143875842900⟩,⟨1868173451624,3166438142952⟩,⟨-2514229551094,-901143816688⟩,⟨-274132562499,1764533908508⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8587406052,-7616479369⟩,⟨105430027458,138228870590⟩,⟨-143875842900,-105180359544⟩,⟨-3166438142952,-1868173451624⟩,⟨901143816688,2514229551094⟩,⟨-1764533908508,274132562499⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090924221724,1091895148407⟩,⟨105430027458,138228870590⟩,⟨-143875842900,-105180359544⟩,⟨-3166438142952,-1868173451624⟩,⟨901143816688,2514229551094⟩,⟨-1764533908508,274132562499⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8621116416,-7642982016⟩,⟨106165451211,139316963985⟩,⟨-145008387453,-105914041747⟩,⟨-3209015909340,-1891455843733⟩,⟨917656449465,2552394489464⟩,⟨-1797548092648,266087930896⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4310558208,-3821491008⟩,⟨53082725605,69658481993⟩,⟨-72504193727,-52957020873⟩,⟨-1604507954670,-945727921866⟩,⟨458828224732,1276197244732⟩,⟨-898774046324,133043965448⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3821491008,4310558208⟩,⟨-69658481993,-53082725605⟩,⟨52957020873,72504193727⟩,⟨945727921866,1604507954670⟩,⟨-1276197244732,-458828224732⟩,⟨-133043965448,898774046324⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765944874624,766433961088⟩,⟨-69658481993,-53082725605⟩,⟨52957020873,72504193727⟩,⟨945727921866,1604507954670⟩,⟨-1276197244732,-458828224732⟩,⟨-133043965448,898774046324⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272731055431,272973787102⟩,⟨26357506864,34557217648⟩,⟨-35968960725,-26295089886⟩,⟨-791609535738,-467043362906⟩,⟨225285954172,628557387774⟩,⟨-441133477127,68533140625⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531889749248,1532867922176⟩,⟨-139316963986,-106165451210⟩,⟨105914041746,145008387454⟩,⟨1891455843732,3209015909340⟩,⟨-2552394489464,-917656449464⟩,⟨-266087930896,1797548092648⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1199331362754,1206101231342⟩,⟨-941034501442,-753591221070⟩,⟨751806648365,979477959375⟩,⟨9084590926027,15451147821693⟩,⟨-10761625206352,-2182579227229⟩,⟨-5867844510041,5398240983284⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1299151097732,1312690834908⟩,⟨-1882069002884,-1507182442140⟩,⟨1503613296731,1958955918750⟩,⟨18169181852063,30902295643379⟩,⟨-21523250412700,-4365158454458⟩,⟨-11730838813434,10796481966566⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨183447954752,194847750272⟩,⟨-1592853022687,-1262418062382⟩,⟨1259428541335,1657924790064⟩,⟨12910978966973,24704104415091⟩,⟨-16769761729708,-1254441295322⟩,⟨-12428111932073,7694791207438⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62838518560,67266683627⟩,⟨-543613680058,-421901265389⟩,⟨419136810435,567227283293⟩,⟨4113486049240,8230418760943⟩,⟨-5635337079794,-60425219343⟩,⟨-4657310507919,2678612171866⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379981345864,380562379945⟩,⟨2134507042,21843365953⟩,⟨-23873888221,-634545328⟩,⟨-643197316962,140900531130⟩,⟨-314721806679,657786784172⟩,⟨-690548393934,536752599804⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176682413509,3181539917087⟩,⟨-182891979987,-17817449488⟩,⟨5296763658,199893308390⟩,⟨-1179544001821,5406444062945⟩,⟨-5530554641759,2635069916434⟩,⟨-4494149854078,5807000172511⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨181551528658,194642451834⟩,⟨-1584186210981,-1219965226599⟩,⟨1211262656710,1653554503530⟩,⟨11826095202750,24327095660920⟩,⟨-16837910145944,-22193469205⟩,⟨-13747272265729,8312325978430⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨364999483410,389490202106⟩,⟨-3177039233668,-2482383288981⟩,⟨2470691198045,3311479293594⟩,⟨24737074169723,49031200076011⟩,⟨-33607671875652,-1276634764527⟩,⟨-26175384197802,16007117185868⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518438930003,526911933488⟩,⟨-34904299946,203902993582⟩,⟨-231076803046,58352644792⟩,⟨-5856639278916,2392209984736⟩,⟨-4349134879000,6688197265258⟩,⟨-7722313323420,6721310470164⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355997128670,364759942506⟩,⟨-36244264836,211730764163⟩,⟨-239947767463,60592784127⟩,⟨-6088486639116,2525013666435⟩,⟨-4562523951114,6956679033034⟩,⟨-8032056915470,7031953875035⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711994257340,729519885012⟩,⟨-72488529672,423461528326⟩,⟨-479895534926,121185568254⟩,⟨-12176973278232,5050027332870⟩,⟨-9125047902228,13913358066068⟩,⟨-16064113830940,14063907750070⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523302343196,1525251442807⟩,⟨-33886936528,32063419380⟩,⟨-37961801154,39828027910⟩,⟨-1274982299220,1340842457716⟩,⟨-1651250672776,1596573101630⟩,⟨-2030621839404,2071680655147⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨986422056074,1011995898054⟩,⟨-123040470962,608703166175⟩,⟨-690902421280,194535278905⟩,⟨-17764041904076,7919777963613⟩,⟨-13782551044295,20390170099907⟩,⟨-23666342162289,20917253294436⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67650242814,67770714345⟩,⟨13075824726,17158917350⟩,⟨-17859899212,-13044859982⟩,⟨-391799284824,-229525590848⟩,⟨109502232316,310840946514⟩,⟨-217781133174,36382547614⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49991369654,50705385995⟩,⟨260868383369,268980871937⟩,⟨33530495840,38637528697⟩,⟨-1391283466374,-1186504182222⟩,⟨-295886213305,-105257978153⟩,⟨-277303506063,-74374997318⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134298669126,2137025209628⟩,⟨-388453381874,-295829097800⟩,⟨295128547534,404322610076⟩,⟨5291027120980,8982909577088⟩,⟨-7153513735706,-2577495106918⟩,⟨-721520099451,5050299009274⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2973602252557,2979302182867⟩,⟨-812334831156,-618243888014⟩,⟨616779830140,845520606884⟩,⟨11100396985882,18858916634153⟩,⟨-15036294919104,-5429370669531⟩,⟨-1466210157878,10641185579169⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135200434134,137394333413⟩,⟨668050289491,700736964218⟩,⟨118725462418,143686813614⟩,⟨-3662657838238,-2632535532692⟩,⟨-1377378641479,-343532693566⟩,⟨-781395852645,349010784798⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8798949633393,8941730308473⟩,⟨-46344532777208,-42782993328664⟩,⟨-9502992682309,-7603365714341⟩,⟨584637864764245,722639343877509⟩,⟨95939824254841,189602533418820⟩,⟨-9942001810946,71878027000386⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7893939244843,8230012457425⟩,⟨-43656356661935,-33432323738824⟩,⟨-14365334877122,-5239276689798⟩,⟨328726205272707,739900385004996⟩,⟨-39474656699357,370518310466465⟩,⟨-204978867912475,248208368743415⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15787878489686,16460024914850⟩,⟨-87312713323870,-66864647477648⟩,⟨-28730669754244,-10478553379596⟩,⟨657452410545414,1479800770009992⟩,⟨-78949313398714,741036620932930⟩,⟨-409957735824950,496416737486830⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10909882818222,10952333724170⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145760,2173453475298114⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9810371190446,9852822096394⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145775,2173453475298112⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2406362562496,2411110103296⟩,⟨-12227224809080,-12080350374972⟩,⟨0,0⟩,⟨103760055435140,110865974497594⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7440868526604,7534694005337⟩,⟨-45744037888880,-44434848223240⟩,⟨-20633223439302,-20102883968193⟩,⟨530705717904571,555435164559327⟩,⟨290453499402386,302167068051077⟩,⟨108623325998507,113005228664783⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6341356898828,6435182377561⟩,⟨-45744037888880,-44434848223240⟩,⟨-20633223439303,-20102883968192⟩,⟨530705717904578,555435164559322⟩,⟨290453499402388,302167068051075⟩,⟨108623325998507,113005228664784⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1926593585856,1942742607680⟩,⟨-7931441545215,-7592113079849⟩,⟨-3577541755184,-3434767404871⟩,⟨33461800373166,43882041058529⟩,⟨23819751179497,28674950877909⟩,⟨6918874806250,8863807744071⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99256358666,99685855397⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136739062777,138762227257⟩,⟨682925884635,690369037077⟩,⟨309159202978,311204860397⟩,⟨-1725980926281,-1712309844048⟩,⟨-1557133682282,-1549240002148⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4332956148352,4353852710976⟩,⟨-20158666354295,-19672463454821⟩,⟨-3577541755184,-3434767404871⟩,⟨137221855808306,154748015556123⟩,⟨23819751179497,28674950877909⟩,⟨6918874806250,8863807744071⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨729998966820,778980404212⟩,⟨-6354078467336,-4964766577962⟩,⟨4941382396090,6622958587188⟩,⟨49474148339446,98062400152022⟩,⟨-67215343751304,-2553269529054⟩,⟨-52350768395604,32014234371736⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5062955115172,5132833115188⟩,⟨-26512744821631,-24637230032783⟩,⟨1363840640906,3188191182317⟩,⟨186696004147752,252810415708145⟩,⟨-43395592571807,26121681348855⟩,⟨-45431893589354,40878042115807⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457048817062,465361935947⟩,⟨1638708162232,1878176539436⟩,⟨123118166645,289053391661⟩,⟨-35790998694430,-26547744759861⟩,⟨-2845465962195,4916351950235⟩,⟨-4119026175213,3706156890320⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37101212001,39203253066⟩,⟨-788720807906,-746454755961⟩,⟨328085346598,330673870673⟩,⟨9219844159056,9946881843075⟩,⟨-6659570832821,-6593775017748⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨494150029063,504565189013⟩,⟨849987354326,1131721783475⟩,⟨451203513243,619727262334⟩,⟨-26571154535374,-16600862916786⟩,⟨-9505036795016,-1677423067513⟩,⟨-4119026175213,3706156890320⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501398014948,502387228948⟩,⟨2512147284185,2552733193796⟩,⟨0,0⟩,⟨2027158573049,4364694834823⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225341722087,230545180905⟩,⟨1516636644445,1688552290187⟩,⟨205757301844,283164865348⟩,⟨-7345717114428,-312319673816⟩,⟨-3312124514277,673882602662⟩,⟨-1882059356040,1693411732208⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-778980404212,-729998966820⟩,⟨4964766577962,6354078467336⟩,⟨-6622958587188,-4941382396090⟩,⟨-98062400152022,-49474148339446⟩,⟨2553269529054,67215343751304⟩,⟨-32014234371736,52350768395604⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3553975744140,3623853744156⟩,⟨-15193899776333,-13318384987485⟩,⟨-10200500342372,-8376149800961⟩,⟨39159455656284,105273867216677⟩,⟨26373020708551,95890294629213⟩,⟨-25095359565486,61214576139675⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441984695849,457343064039⟩,⟨289912946167,619050241739⟩,⟨-288036824880,-15994351008⟩,⟨-19898717339685,-8793368637478⟩,⟨-12557509442787,-1853369517217⟩,⟨-10098774205392,1882271189969⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨320895797164,324942126122⟩,⟨1940466224332,1948197165466⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-324942126122,-320895797164⟩,⟨-1948197165466,-1940466224332⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨774569501654,778615830612⟩,⟨-1948197165466,-1940466224332⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1357221329896,1375747296283⟩,⟨-9058923377044,-8748528695038⟩,⟨-4086101681975,-3957944367564⟩,⟨50370516005387,59181980505520⟩,⟨32757068015687,36869478465609⟩,⟨10359012194676,11995355519493⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1375747296283,-1357221329896⟩,⟨8748528695038,9058923377044⟩,⟨3957944367564,4086101681975⟩,⟨-59181980505520,-50370516005387⟩,⟨-36869478465609,-32757068015687⟩,⟨-11995355519493,-10359012194676⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-276235668507,-257709702120⟩,⟨8748528695038,9058923377044⟩,⟨3957944367564,4086101681975⟩,⟨-59181980505520,-50370516005387⟩,⟨-36869478465609,-32757068015687⟩,⟨-11995355519493,-10359012194676⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13086926128,-11634372452⟩,⟨424349647566,461654337104⟩,⟨68296079222,90700387679⟩,⟨-4934064765690,-4269748334846⟩,⟨1523123795246,1965986875311⟩,⟨2591879890085,2798028741746⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428897769721,445708691587⟩,⟨714262593733,1080704578843⟩,⟨-219740745658,74706036671⟩,⟨-24832782105375,-13063116972324⟩,⟨-11034385647541,112617358094⟩,⟨-7506894315307,4680299931715⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99685855397,-99256358666⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4480954482,4722711707⟩,⟨27911758936,30310198806⟩,⟨39624999436,39835402372⟩,⟨-310824434404,-299544440992⟩,⟨250784818133,251900503000⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9806900479,10356396080⟩,⟨8567580159,17234675778⟩,⟨86722243560,87354729775⟩,⟨-932875153292,-792708440708⟩,⟨105867709348,117030113883⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1469561605417,1487901393993⟩,⟨-7610066615050,-7293500408995⟩,⟨-1434329922686,-1361492744680⟩,⟨105686233542222,113356610897392⟩,⟨22271234654672,24130880306237⟩,⟨4947411291797,5407102878353⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13107496135,14014673220⟩,⟨-60228810260,-41730467763⟩,⟨102399272402,106068182827⟩,⟨-558325999169,-105449750481⟩,⟨-286949781359,-200211791981⟩,⟨-183783627511,-163841206599⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14014673220,-13107496135⟩,⟨41730467763,60228810260⟩,⟨-106068182827,-102399272402⟩,⟨105449750481,558325999169⟩,⟨200211791981,286949781359⟩,⟨163841206599,183783627511⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113700528617,-112363854801⟩,⟨-837019840999,-817662505042⟩,⟨-106068182827,-102399272402⟩,⟨2304473006033,2757349254721⟩,⟨200211791981,286949781359⟩,⟨163841206599,183783627511⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86976575419,92039268962⟩,⟨-604183579880,-562500027693⟩,⟨599642857933,621274679102⟩,⟨3242592597081,3944081260432⟩,⟨-3645093901728,-3178363902112⟩,⟨-2546884022220,-2322515822383⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨116249280660,124551076252⟩,⟨-1454637239234,-1328764603508⟩,⟨681391105396,733032252082⟩,⟨20156771469547,23189766748727⟩,⟨-6774431826331,-5417596019430⟩,⟨-4676102544670,-4136593893572⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-124551076252,-116249280660⟩,⟨1328764603508,1454637239234⟩,⟨-733032252082,-681391105396⟩,⟨-23189766748727,-20156771469547⟩,⟨5417596019430,6774431826331⟩,⟨4136593893572,4676102544670⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨974960551524,983262347116⟩,⟨1328764603508,1454637239234⟩,⟨-733032252082,-681391105396⟩,⟨-23189766748727,-20156771469547⟩,⟨5417596019430,6774431826331⟩,⟨4136593893572,4676102544670⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121249460844,124091159946⟩,⟨770814789273,800957953235⟩,⟨181626855095,193561609496⟩,⟨-2819488377675,-2198412011234⟩,⟨-805391101735,-530291875097⟩,⟨-214542294329,-103814581322⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11482948926,11757774890⟩,⟨167120944738,173112491002⟩,⟨20929250196,21937027590⟩,⟨645850203559,803379851248⟩,⟨92953457640,120570993754⟩,⟨-18936924993,-13022818421⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164883569911,176017481529⟩,⟨1465998084592,1893233805299⟩,⟨-6712333230,218969332685⟩,⟨-11353900491833,7525023276124⟩,⟨-5775063592141,6863893448793⟩,⟨-5813875777309,4722584931578⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176017481529,-164883569911⟩,⟨-1893233805299,-1465998084592⟩,⟨-218969332685,6712333230⟩,⟨-7525023276124,11353900491833⟩,⟨-6863893448793,5775063592141⟩,⟨-4722584931578,5813875777309⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49324240558,65661610994⟩,⟨-376597160854,222554205595⟩,⟨-13212030841,289877198578⟩,⟨-14870740390552,11041580818017⟩,⟨-10176017963070,6448946194803⟩,⟨-6604644287618,7507287509517⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27663941575613,29083450249849⟩,⟨-273010167630990,-226177107593293⟩,⟨-104321518577307,-67680597711493⟩,⟨2555882351670444,4531287104035731⟩,⟨483763884544924,2229966711279593⟩,⟨-559544076906472,1196784782941388⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13370874289,14004959646⟩,⟨170004346018,180792633702⟩,⟨40058072508,43690824248⟩,⟨444346107762,682079865830⟩,⟨72866441788,165049835454⟩,⟨11578799477,45253972819⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336413982173,370448603568⟩,⟨799895056136,2031709204978⟩,⟨-320919280414,332630542823⟩,⟨-47520832668602,5816715528883⟩,⟨-20285808453094,14064969722219⟩,⟨-15126591508195,11509433239652⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370448603568,-336413982173⟩,⟨-2031709204978,-799895056136⟩,⟨-332630542823,320919280414⟩,⟨-5816715528883,47520832668602⟩,⟨-14064969722219,20285808453094⟩,⟨-11509433239652,15126591508195⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58449166153,109294709414⟩,⟨-1317446611245,280809522707⟩,⟨-552371288481,395625317085⟩,⟨-30649497634258,34457715696278⟩,⟨-25099355369760,20398425811188⟩,⟨-19016327554959,19806891439910⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235995421443,238448082654⟩,⟨1560817199937,1569119345839⟩,⟨309159202978,311204860397⟩,⟨-3925004181833,-3911333099600⟩,⟨-1557133682282,-1549240002148⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1702131643349,-1613431674041⟩,⟨-5697254797787,-2711799075101⟩,⟨-517024347152,1500689057560⟩,⟨-20487240986152,107026696315765⟩,⟨-59736089155130,42754455250647⟩,⟨-47030105562407,50688244506246⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192103007070,-177922375392⟩,⟨-1882940372125,-1430145104318⟩,⟨-358000298930,-97152474150⟩,⟨-7386753177650,12641628574292⟩,⟨-7343274280509,6717332255698⟩,⟨-5337528589242,6581189030013⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43892414373,60525707262⟩,⟨-322123172188,138974241521⟩,⟨-48841095952,214052386247⟩,⟨-11311757359483,8730295474692⟩,⟨-8900407962791,5168092253550⟩,⟨-5688685450908,6230718356483⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2622037510,6526958435⟩,⟨-116111317908,38892178849⟩,⟨-34300313692,52440955055⟩,⟨-3841883161421,4057827752614⟩,⟨-2993272700112,2122443163579⟩,⟨-2083411403880,2137698834099⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1752181596,3331807639⟩,⟨-35464350408,15300455306⟩,⟨-5377190748,23566230210⟩,⟨-1326805319132,1149911706803⟩,⟨-1105317497680,623095196472⟩,⟨-645316073939,769318029297⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3070219303,5887017925⟩,⟨-86696802210,14935799871⟩,⟨-20341920868,36165859728⟩,⟨-2511769169853,2676420837718⟩,⟨-2134823319651,1342029532418⟩,⟨-1282549649059,1421170659868⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5887017925,-3070219303⟩,⟨-14935799871,86696802210⟩,⟨-36165859728,20341920868⟩,⟨-2676420837718,2511769169853⟩,⟨-1342029532418,2134823319651⟩,⟨-1421170659868,1282549649059⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3264980415,3456739132⟩,⟨-131047117779,125588981059⟩,⟨-70466173420,72782875923⟩,⟨-6518303999139,6569596922467⟩,⟨-4335302232530,4257266483230⟩,⟨-3504582063748,3420248483158⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49324240558,65661610994⟩,⟨-376597160854,222554205595⟩,⟨-13212030841,289877198578⟩,⟨-14870740390552,11041580818017⟩,⟨-10176017963070,6448946194803⟩,⟨-6604644287618,7507287509517⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3264980415,3456739132⟩,⟨-131047117779,125588981059⟩,⟨-70466173420,72782875923⟩,⟨-6518303999139,6569596922467⟩,⟨-4335302232530,4257266483230⟩,⟨-3504582063748,3420248483158⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (103/1024) u, BivariateJet2.affineZ (593/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000018

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000019Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2525295488000,-2525295430144⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-116561173120,-116561173056⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2098805683968,-2098805645184⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2098805683968,-2098805645184⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-176430581696,-176430581632⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-176430581696,-176430581632⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨92809917824,92809917888⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-101372319232,-101372319168⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨92810040832,92810040896⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-101372466048,-101372465984⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-8562425152,-8562425088⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-8562401344,-8562401280⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨194182236992,194182237056⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨194182506816,194182506880⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1922375063488,1922375102080⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1922375063488,1922375102080⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2105652978176,-2105652939328⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2091995706880,-2091995668160⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-177620206720,-177620206656⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-175243127808,-175243127744⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨90216851968,90216852032⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-98286349376,-98286349312⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨95425122688,95425122752⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-104500845312,-104500845248⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-9075722624,-9075722560⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-8069497344,-8069497280⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨188503201280,188503201344⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨199925967936,199925968000⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1914375461440,1914375500032⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1930409811520,1930409850112⟩



end LaneCBRB2Cell000019Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000019
open Set LaneCBRB2Cell000019Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110595407872,110595407872⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨131211250892,131211250893⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110595407872,-110595407872⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439160406016,439160406016⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨52407618764,52407618765⟩,⟨-131211250893,-131211250892⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163003026636,163003026637⟩,⟨968300376883,968300376884⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52407618764,52407618765⟩,⟨-131211250893,-131211250892⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2098805683968,-2098805645184⟩,⟨6531519969463,6531519969513⟩,⟨2962288387127,2962288387146⟩,⟨-38799728929130,-38799728928556⟩,⟨-25013712109976,-25013712109686⟩,⟨-7980954695650,-7980954695547⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311148759293,-311148753540⟩,⟨-880042363167,-880042328994⟩,⟨-399132098619,-399132083121⟩,⟨5752074910519,5752074910742⟩,⟨3608074942668,3608074981559⟩,⟨1183179638982,1183179639023⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨311148753540,311148759293⟩,⟨880042328994,880042363167⟩,⟨399132083121,399132098619⟩,⟨-5752074910742,-5752074910519⟩,⟨-3608074981559,-3608074942668⟩,⟨-1183179639023,-1183179638982⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-163003026637,-163003026636⟩,⟨-968300376884,-968300376883⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨936508601139,936508601140⟩,⟨-968300376884,-968300376883⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-176430581696,-176430581632⟩,⟨-1136836887851,-1136836887847⟩,⟨-515598011899,-515598011898⟩,⟨-1175429233243,-1175429233234⟩,⟨757784893280,757784893286⟩,⟨-241781262843,-241781262841⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150274679311,-150274679256⟩,⟨-812924304117,-812924304055⟩,⟨-368691550659,-368691550630⟩,⟨1001171392043,1001171392064⟩,⟨1377149685849,1377149685926⟩,⟨205937096548,205937096553⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150274679256,150274679311⟩,⟨812924304055,812924304117⟩,⟨368691550630,368691550659⟩,⟨-1001171392064,-1001171392043⟩,⟨-1377149685926,-1377149685849⟩,⟨-205937096553,-205937096548⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨461423432796,461423438604⟩,⟨1692966633049,1692966667284⟩,⟨767823633751,767823649278⟩,⟨-6753246302806,-6753246302562⟩,⟨-4985224667485,-4985224628517⟩,⟨-1389116735576,-1389116735530⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨820269399289,820269410975⟩,⟨4101700890071,4101700982230⟩,⟨767823633751,767823649278⟩,⟨-18906788828420,-18906788828166⟩,⟨-4985224667485,-4985224628517⟩,⟨-1389116735576,-1389116735530⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨104815237528,104815237530⟩,⟨-262422501786,-262422501784⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11533874731415,11533874731637⟩,⟨28876987102324,28876987103657⟩,⟨-96650472384433,-96650472380710⟩,⟨144596747151515,144596747162072⟩,⟨-241980644813717,-241980644772757⟩,⟨1619804970825889,1619804970919442⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8604624324482,8604624447234⟩,⟨64569952078737,64569953354225⟩,⟨-64049749603993,-64049748410945⟩,⟨124991202393127,124991208795089⟩,⟨-573206472978267,-573206461442395⟩,⟨1058864213653229,1058864233674593⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨96839544832,96839678720⟩,⟨-718586795013,-718584764459⟩,⟨712795532501,712797545893⟩,⟨9213514083671,9213564041916⟩,⟨-4140040220988,-4139976591284⟩,⟨-1349563062642,-1349484551743⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1196351172608,1196351306496⟩,⟨-718586795013,-718584764459⟩,⟨712795532501,712797545893⟩,⟨9213514083671,9213564041916⟩,⟨-4140040220988,-4139976591284⟩,⟨-1349563062642,-1349484551743⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨92809917824,92810040896⟩,⟨-660420246809,-660418306709⟩,⟨655097689078,655099612811⟩,⟨8071037740850,8071086933486⟩,⟨-3411439124204,-3411377907817⟩,⟨-1630636322167,-1630561735235⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨100984156250,100984301464⟩,⟨-779242959597,-779240516368⟩,⟨772962615244,772965037920⟩,⟨10422840220732,10422904952321⟩,⟨-4917645872287,-4917568080292⟩,⟨-1038793457363,-1038700430994⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-96839678720,-96839544832⟩,⟨718584764459,718586795013⟩,⟨-712797545893,-712795532501⟩,⟨-9213564041916,-9213514083671⟩,⟨4139976591284,4140040220988⟩,⟨1349484551743,1349563062642⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1002671949056,1002672082944⟩,⟨718584764459,718586795013⟩,⟨-712797545893,-712795532501⟩,⟨-9213564041916,-9213514083671⟩,⟨4139976591284,4140040220988⟩,⟨1349484551743,1349563062642⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-101372466048,-101372319168⟩,⟨787986738141,787989070032⟩,⟨-781640685868,-781638373644⟩,⟨-10668154572152,-10668095097339⟩,⟨5099998209222,5100071905436⟩,⟨924152905873,924242484592⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-92444080734,-92443934445⟩,⟨652332603823,652335109494⟩,⟨-647079612819,-647077128212⟩,⟨-7849116579049,-7849049248091⟩,⟨3247428782981,3247508938327⟩,⟨1731778266856,1731873347848⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8540075516,8540367019⟩,⟨-126910355774,-126905406874⟩,⟨125883002425,125887909708⟩,⟨2573723641683,2573855704230⟩,⟨-1670217089306,-1670059141965⟩,⟨692984809493,693172916854⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4270037758,4270183510⟩,⟨-63455177887,-63452703437⟩,⟨62941501212,62943954854⟩,⟨1286861820841,1286927852115⟩,⟨-835108544653,-835029570982⟩,⟨346492404746,346586458427⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4270183510,-4270037758⟩,⟨63452703437,63455177887⟩,⟨-62943954854,-62941501212⟩,⟨-1286927852115,-1286861820841⟩,⟨835029570982,835108544653⟩,⟨-346586458427,-346492404746⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757853200106,757853365122⟩,⟨63452703437,63455177887⟩,⟨-62943954854,-62941501212⟩,⟨-1286927852115,-1286861820841⟩,⟨835029570982,835108544653⟩,⟨-346586458427,-346492404746⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8529148038,8529171623⟩,⟨-126579315042,-126578782352⟩,⟨125559008530,125559536786⟩,⟨2562222241755,2562238594062⟩,⟨-1660968462394,-1660950981282⟩,⟨686461531138,686480910524⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8529171623,-8529148038⟩,⟨126578782352,126579315042⟩,⟨-125559536786,-125559008530⟩,⟨-2562238594062,-2562222241755⟩,⟨1660950981282,1660968462394⟩,⟨-686480910524,-686461531138⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090982456153,1090982479738⟩,⟨126578782352,126579315042⟩,⟨-125559536786,-125559008530⟩,⟨-2562238594062,-2562222241755⟩,⟨1660950981282,1660968462394⟩,⟨-686480910524,-686461531138⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8562425152,-8562401280⟩,⟨127568357522,127568897135⟩,⟨-126541146374,-126540611251⟩,⟨-2597070828179,-2597054166989⟩,⟨1688617652243,1688635430401⟩,⟨-706411167975,-706391498953⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4281212576,-4281200640⟩,⟨63784178761,63784448568⟩,⟨-63270573187,-63270305625⟩,⟨-1298535414090,-1298527083494⟩,⟨844308826121,844317715201⟩,⟨-353205583988,-353195749476⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4281200640,4281212576⟩,⟨-63784448568,-63784178761⟩,⟨63270305625,63270573187⟩,⟨1298527083494,1298535414090⟩,⟨-844317715201,-844308826121⟩,⟨353195749476,353205583988⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766404584256,766404615456⟩,⟨-63784448568,-63784178761⟩,⟨63270305625,63270573187⟩,⟨1298527083494,1298535414090⟩,⟨-844317715201,-844308826121⟩,⟨353195749476,353205583988⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272745614038,272745619935⟩,⟨31644695588,31644828761⟩,⟨-31389884197,-31389752132⟩,⟨-640559648516,-640555560438⟩,⟨415237745320,415242115599⟩,⟨-171620227631,-171615382784⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532809168512,1532809230912⟩,⟨-127568897136,-127568357522⟩,⟨126540611250,126541146374⟩,⟨2597054166988,2597070828180⟩,⟨-1688635430402,-1688617652242⟩,⟨706391498952,706411167976⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1205704078311,1205704239311⟩,⟨-864094329034,-864091656542⟩,⟨857130157662,857132807658⟩,⟨12317703779044,12317774308054⟩,⟨-6206928084043,-6206842806327⟩,⟨-404177034259,-404074819448⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1311896528846,1311896850846⟩,⟨-1728188658068,-1728183313083⟩,⟨1714260315324,1714265615317⟩,⟨24635407558097,24635548616103⟩,⟨-12413856168085,-12413685612657⟩,⟨-808353920122,-808149787294⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨194182236992,194182506880⟩,⟨-1448409598438,-1448404763252⟩,⟨1436735783394,1436740578006⟩,⟨18739119157587,18739255186246⟩,⟨-8511522639242,-8511364507452⟩,⟨-2554888614952,-2554704832947⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨66747960725,66748067544⟩,⟨-489707135616,-489705402516⟩,⟨485760122465,485761840972⟩,⟨6154249919733,6154295178053⟩,⟨-2697763122601,-2697708146160⟩,⟨-1042341703259,-1042275648196⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380229701357,380229725058⟩,⟨12470465296,12470787290⟩,⟨-12370317144,-12369997829⟩,⟨-256108615341,-256098670992⟩,⟨167275160559,167285757229⟩,⟨-71249914849,-71238207141⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179461625285,3179461823472⟩,⟨-104280102148,-104277396650⟩,⟨103437292800,103439975792⟩,⟨2148324074065,2148407849700⟩,⟨-1405620425453,-1405531290641⟩,⟨602420507756,602518830019⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨193015311825,193015632746⟩,⟨-1422418461221,-1422413186965⟩,⟨1410953606707,1410958836607⟩,⟨18019571245644,18019711261797⟩,⟨-7978604019475,-7978436293698⟩,⟨-2886175832917,-2885975911979⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨387197548817,387198139626⟩,⟨-2870828059659,-2870817950217⟩,⟨2847689390101,2847699414613⟩,⟨36758690403231,36758966448043⟩,⟨-16490126658717,-16489800801150⟩,⟨-5441064447869,-5440680744926⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522360526620,522360754100⟩,⟨87471261130,87474691276⟩,⟨-86769956398,-86766555092⟩,⟨-1766741402792,-1766649419401⟩,⟨1143845497970,1143955182484⟩,⟨-470572706492,-470442385078⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360044029283,360044264474⟩,⟨90436117485,90439683591⟩,⟨-89711061421,-89707525291⟩,⟨-1819053927399,-1818957835156⟩,⟨1175104854579,1175219102843⟩,⟨-479072549270,-478937121054⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720088058566,720088528948⟩,⟨180872234970,180879367182⟩,⟨-179422122842,-179415050582⟩,⟨-3638107854798,-3637915670312⟩,⟨2350209709158,2350438205686⟩,⟨-958145098540,-957874242108⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524279996889,1524280082874⟩,⟨-990114784,-989042480⟩,⟨981074464,982137844⟩,⟨34815572926,34848586425⟩,⟨-27684449120,-27649189848⟩,⟨19910588428,19949636838⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨998275776210,998276484626⟩,⟨250099182684,250109787085⟩,⟨-248094791705,-248084276379⟩,⟨-5021123112576,-5020834396362⟩,⟨3240345260708,3240685681235⟩,⟨-1315580946319,-1315179434810⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67657465458,67657468384⟩,⟨15699610100,15699676512⟩,⟨-15573193060,-15573127202⟩,⟨-315973832915,-315971782527⟩,⟨204201471766,204203659620⟩,⟨-83352185975,-83349765419⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50474544467,50474547370⟩,⟨264106889548,264106955848⟩,⟨35629261292,35629313589⟩,⟨-1282004566538,-1282002485065⟩,⟨-201552676432,-201550732800⟩,⟨-169411852737,-169409949917⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136861391658,2136861565641⟩,⟨-355682974456,-355681455442⟩,⟨352815930660,352817437038⟩,⟨7270613649091,7270660648434⟩,⟨-4737555518388,-4737505509918⟩,⟨1998661705233,1998716872220⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2978959612821,2978959976641⟩,⟨-743776781552,-743773574828⟩,⟨737781410834,737784590890⟩,⟨15265646144743,15265745571285⟩,⟨-9968212946494,-9968107447447⟩,⟨4240354242110,4240470290819⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136753105328,136753129895⟩,⟨681413404015,681413820211⟩,⟨130400904755,130401206170⟩,⟨-3129923244752,-3129910946263⟩,⟨-850564443179,-850553293475⟩,⟨-216521554464,-216510728157⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8840205855199,8840207443298⟩,⟨-44049014543017,-44048971812267⟩,⟨-8429598074825,-8429575561622⟩,⟨641302884933259,641304525461703⟩,⟨138988539241649,138989570511228⟩,⟨30072057362026,30072845223619⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8026257421038,8026264558667⟩,⟨-37982469739381,-37982316940280⟩,⟨-9648173506522,-9648062732164⟩,⟨521845491704547,521850592055957⟩,⟨160265465965408,160269750867698⟩,⟨20529740357388,20533876549375⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16052514842076,16052529117334⟩,⟨-75964939478762,-75964633880560⟩,⟨-19296347013044,-19296125464328⟩,⟨1043690983409094,1043701184111914⟩,⟨320530931930816,320539501735396⟩,⟨41059480714776,41067753098750⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10931067056724,10931067056725⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603222,2160817149603840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9831555428948,9831555428949⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603232,2160817149603830⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2408734257088,2408734314944⟩,⟨-12153542525660,-12153542525558⟩,⟨0,0⟩,⟨107314718406763,107314718418708⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7416585106157,7416585106204⟩,⟨-44057354650029,-44057354649423⟩,⟨-19981656744120,-19981656743865⟩,⟨523435104140771,523435104151817⟩,⟨287424804562695,287424804568095⟩,⟨107668583455804,107668583457855⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6317073478381,6317073478428⟩,⟨-44057354650030,-44057354649423⟩,⟨-19981656744120,-19981656743865⟩,⟨523435104140779,523435104151813⟩,⟨287424804562699,287424804568094⟩,⟨107668583455805,107668583457855⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1922375063488,1922375102080⟩,⟨-7668356857459,-7668356857232⟩,⟨-3477886399089,-3477886398989⟩,⟨37624299690734,37624299700431⟩,⟨25771497000824,25771497005403⟩,⟨7739173431784,7739173433721⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99471065088,99471065088⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138837764512,138837764514⟩,⟨681198561606,681198561610⟩,⟨308949003878,308949003880⟩,⟨-1705494687256,-1705494687251⟩,⟨-1547011149008,-1547011149004⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4331109320576,4331109417024⟩,⟨-19821899383119,-19821899382790⟩,⟨-3477886399089,-3477886398989⟩,⟨144939018097497,144939018119139⟩,⟨25771497000824,25771497005403⟩,⟨7739173431784,7739173433721⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨774395097634,774396279252⟩,⟨-5741656119318,-5741635900434⟩,⟨5695378780202,5695398829226⟩,⟨73517380806462,73517932896086⟩,⟨-32980253317434,-32979601602300⟩,⟨-10882128895738,-10881361489852⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5105504418210,5105505696276⟩,⟨-25563555502437,-25563535283224⟩,⟨2217492381113,2217512430237⟩,⟨218456398903959,218456951015225⟩,⟨-7208756316610,-7208104596897⟩,⟨-3142955463954,-3142188056131⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461886849999,461886965624⟩,⟨1765726386266,1765729236423⟩,⟨200613002538,200614816351⟩,⟨-31289383275953,-31289298467841⟩,⟨1119230582917,1119305558767⟩,⟨-284338173082,-284268746918⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨39306635026,39306637231⟩,⟨-790787443626,-790787432575⟩,⟨329378021832,329378040293⟩,⟨9870213265215,9870213293478⟩,⟨-6626565812353,-6626565719884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨501193485025,501193602855⟩,⟨974938942640,974941803848⟩,⟨529991024370,529992856644⟩,⟨-21419170010738,-21419085174363⟩,⟨-5507335229436,-5507260161117⟩,⟨-284338173082,-284268746918⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501892554988,501892567044⟩,⟨2532355881864,2532356003553⟩,⟨0,0⟩,⟨3194096148032,3194099067279⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228779098272,228779157554⟩,⟨1599359954191,1599361597787⟩,⟨241924271305,241925113493⟩,⟨-3830316299172,-3830262270714⟩,⟨-1293269386203,-1293230780796⟩,⟨-129791456490,-129759762507⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-774396279252,-774395097634⟩,⟨5741635900434,5741656119318⟩,⟨-5695398829226,-5695378780202⟩,⟨-73517932896086,-73517380806462⟩,⟨32979601602300,32980253317434⟩,⟨10881361489852,10882128895738⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3556713041324,3556714319390⟩,⟨-14080263482685,-14080243263472⟩,⟨-9173285228315,-9173265179191⟩,⟨71421085201411,71421637312677⟩,⟨58751098603124,58751750322837⟩,⟨18620534921636,18621302329459⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449114020437,449114181829⟩,⟨425603049816,425606394803⟩,⟨-158939167843,-158936277050⟩,⟨-13945213168347,-13945116415844⟩,⟨-7225314760365,-7225212565147⟩,⟨-3938717124538,-3938608547296⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨326006053272,326006053274⟩,⟨1936600753766,1936600753768⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-326006053274,-326006053272⟩,⟨-1936600753768,-1936600753766⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨773505574502,773505574504⟩,⟨-1936600753768,-1936600753766⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1352389361174,1352389388328⟩,⟨-8780616415829,-8780616347677⟩,⟨-3982337673622,-3982337642714⟩,⟨53481650763606,53481650771326⟩,⟨34226376471898,34226376552716⟩,⟨11000969428780,11000969430318⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1352389388328,-1352389361174⟩,⟨8780616347677,8780616415829⟩,⟨3982337642714,3982337673622⟩,⟨-53481650771326,-53481650763606⟩,⟨-34226376552716,-34226376471898⟩,⟨-11000969430318,-11000969428780⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-252877760552,-252877733398⟩,⟨8780616347677,8780616415829⟩,⟨3982337642714,3982337673622⟩,⟨-53481650771326,-53481650763606⟩,⟨-34226376552716,-34226376471898⟩,⟨-11000969430318,-11000969428780⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12053279779,-12053278483⟩,⟨448700664294,448700670794⟩,⟨88813006161,88813018485⟩,⟨-4644859738266,-4644859721566⟩,⟨1653361911736,1653361973689⟩,⟨2656848137289,2656848162064⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437060740658,437060903346⟩,⟨874303714110,874307065597⟩,⟨-70126161682,-70123258565⟩,⟨-18590072906613,-18589976137410⟩,⟨-5571952848629,-5571850591458⟩,⟨-1281868987249,-1281760385232⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99471065088,-99471065088⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4741233767,4741233768⟩,⟨29994207025,29994207028⟩,⟨39730142208,39730142208⟩,⟨-314445712590,-314445712585⟩,⟨251342618624,251342618624⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10386768004,10386768256⟩,⟨13301621721,13301623319⟩,⟨87038055949,87038058040⟩,⟨-889198193158,-889198176377⟩,⟨111463671483,111463684713⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1473815557961,1473815578958⟩,⟨-7369713917257,-7369713541678⟩,⟨-1379583899119,-1379583831910⟩,⟨107674185494686,107674192925274⟩,⟨22754209568532,22754211072477⟩,⟨5078643604980,5078643891029⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13922708859,13922709396⟩,⟨-51789696530,-51789688895⟩,⟨103635668658,103635674076⟩,⟨-353052821173,-353052656313⟩,⟨-235719839067,-235719753214⟩,⟨-170441047945,-170441028189⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13922709396,-13922708859⟩,⟨51789688895,51789696530⟩,⟨-103635674076,-103635668658⟩,⟨353052656313,353052821173⟩,⟨235719753214,235719839067⟩,⟨170441028189,170441047945⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113393774484,-113393773947⟩,⟨-826531123137,-826531115502⟩,⟨-103635674076,-103635668658⟩,⟨2552075911865,2552076076725⟩,⟨235719753214,235719839067⟩,⟨170441028189,170441047945⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨91628953167,91628955009⟩,⟨-594916459313,-594916454686⟩,⟨602052085818,602052101242⟩,⟨3623562720805,3623562721371⟩,⟨-3341803561866,-3341803522923⟩,⟨-2409350013698,-2409350013516⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨122821963247,122821967467⟩,⟨-1411605199672,-1411605138462⟩,⟨692038065388,692038105474⟩,⟨21805375324847,21805376662886⟩,⟨-5872127417756,-5872126787077⟩,⟨-4317143574488,-4317143383576⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-122821967467,-122821963247⟩,⟨1411605138462,1411605199672⟩,⟨-692038105474,-692038065388⟩,⟨-21805376662886,-21805375324847⟩,⟨5872126787077,5872127417756⟩,⟨4317143383576,4317143574488⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨976689660309,976689664529⟩,⟨1411605138462,1411605199672⟩,⟨-692038105474,-692038065388⟩,⟨-21805376662886,-21805375324847⟩,⟨5872126787077,5872127417756⟩,⟨4317143383576,4317143574488⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123328763092,123328763628⟩,⟨783351145887,783351156239⟩,⟨187052386652,187052392904⟩,⟨-2519283957064,-2519283705660⟩,⟨-664820804315,-664820676682⟩,⟨-155398565104,-155398517109⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11694417453,11694417565⟩,⟨170482021478,170482023862⟩,⟨21376107878,21376109098⟩,⟨716252808673,716252868132⟩,⟨107191122058,107191149584⟩,⟨-15618937935,-15618931647⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170734719844,170734873312⟩,⟨1681018563901,1681024070207⟩,⟨106848119254,106850772961⟩,⟨-1999338888680,-1999125023243⟩,⟨505310232732,505443626566⟩,⟨-541620816867,-541523875647⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170734873312,-170734719844⟩,⟨-1681024070207,-1681018563901⟩,⟨-106850772961,-106848119254⟩,⟨1999125023243,1999338888680⟩,⟨-505443626566,-505310232732⟩,⟨541523875647,541620816867⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58044224960,58044437710⟩,⟨-81664116016,-81656966114⟩,⟨135073498344,135076994239⟩,⟨-1831191275929,-1830923382034⟩,⟨-1798713012769,-1798541013528⟩,⟨411732419157,411861054360⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28066055382330,28066080904480⟩,⟨-244771972594623,-244771336059816⟩,⟨-84513603494205,-84513170307567⟩,⟨3433686280869872,3433708903653927⟩,⟨1311531333820657,1311549174904906⟩,⟨306849308650367,306865275526294⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13833399685,13833399806⟩,⟨175732071308,175732074396⟩,⟨41962156462,41962158050⟩,⟨551042543720,551042632078⟩,⟨117390615912,117390657628⟩,⟨28782746900,28782762076⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353110373621,353110697815⟩,⟨1406149283481,1406161476884⟩,⟨7823237904,7829711874⟩,⟨-20976065325039,-20975560428132⟩,⟨-3351744807562,-3351422288689⟩,⟨-1855513870597,-1855278586915⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353110697815,-353110373621⟩,⟨-1406161476884,-1406149283481⟩,⟨-7829711874,-7823237904⟩,⟨20975560428132,20976065325039⟩,⟨3351422288689,3351744807562⟩,⟨1855278586915,1855513870597⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83950042843,83950529725⟩,⟨-531857762774,-531842217884⟩,⟨-77955873556,-77946496469⟩,⟨2385487521519,2386089187629⟩,⟨-2220530559940,-2220105783896⟩,⟨573409599666,573753485365⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238308829600,238308829602⟩,⟨1559519373638,1559519373642⟩,⟨308949003878,308949003880⟩,⟨-3904517942808,-3904517942803⟩,⟨-1547011149008,-1547011149004⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1655513976065,-1655512496002⟩,⟨-4232786885333,-4232744489025⟩,⟨476980688522,477004971128⟩,⟨43830629614100,43832178181128⟩,⟨-7950616604367,-7949532464471⟩,⟨1890578761290,1891476377003⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185693799574,-185693632752⟩,⟨-1654255502754,-1654249675165⟩,⟨-228139845036,-228136859891⟩,⟨2678249065925,2678487045477⟩,⟨-271057001269,-270909764344⟩,⟨608331610638,608440843237⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52615030026,52615196850⟩,⟨-94736129116,-94730301523⟩,⟨80809158842,80812143989⟩,⟨-1226268876883,-1226030897326⟩,⟨-1818068150277,-1817920913348⟩,⟨257517926926,257627159525⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4431799581,4431841529⟩,⟨-34312625377,-34311119762⟩,⟨6197770858,6198607702⟩,⟨65112126888,65174842299⟩,⟨-314111486254,-314069899221⟩,⟨42553419787,42584488444⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2517791822,2517807789⟩,⟨-9066861972,-9066275486⟩,⟨7733936070,7734246290⟩,⟨-101038582803,-101013426165⟩,⟨-187926786242,-187910772044⟩,⟨36524276965,36535686976⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4402081880,4402109886⟩,⟨-33412432762,-33411295677⟩,⟨5557809689,5558402854⟩,⟨35964121455,36016835714⟩,⟨-294818159883,-294785761254⟩,⟨32652066571,32674091923⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4402109886,-4402081880⟩,⟨33411295677,33412432762⟩,⟨-5558402854,-5557809689⟩,⟨-36016835714,-35964121455⟩,⟨294785761254,294818159883⟩,⟨-32674091923,-32652066571⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨29689695,29759649⟩,⟨-901329700,-898687000⟩,⟨639368004,640798013⟩,⟨29095291174,29210720844⟩,⟨-19325725000,-19251739338⟩,⟨9879327864,9932421873⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58044224960,58044437710⟩,⟨-81664116016,-81656966114⟩,⟨135073498344,135076994239⟩,⟨-1831191275929,-1830923382034⟩,⟨-1798713012769,-1798541013528⟩,⟨411732419157,411861054360⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨29689695,29759649⟩,⟨-901329700,-898687000⟩,⟨639368004,640798013⟩,⟨29095291174,29210720844⟩,⟨-19325725000,-19251739338⟩,⟨9879327864,9932421873⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110380659507,110810156237⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨129278515609,133143986176⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110810156237,-110380659507⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438945657651,439375154381⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨51610407403,53205585101⟩,⟨-133143986176,-129278515609⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161991066910,164015741338⟩,⟨966367641600,970233112167⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨51180910673,53635081831⟩,⟨-133143986176,-129278515609⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2105652978176,-2091995668160⟩,⟨6478234649782,6585440844548⟩,⟨2942558138700,2982251431595⟩,⟨-39442994527270,-38169240886096⟩,⟨-25324883560612,-24708108839563⟩,⟨-8088885443836,-7874994843977⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-314103303223,-308213757540⟩,⟨-903635827443,-856308322836⟩,⟨-407911529717,-390297132028⟩,⟨5503753247922,5998799203474⟩,⟨3486711601397,3728614680585⟩,⟨1142818011491,1223248136407⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨308213757540,314103303223⟩,⟨856308322836,903635827443⟩,⟨390297132028,407911529717⟩,⟨-5998799203474,-5503753247922⟩,⟨-3728614680585,-3486711601397⟩,⟨-1223248136407,-1142818011491⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164015741338,-161991066910⟩,⟨-970233112167,-966367641600⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨935495886438,937520560866⟩,⟨-970233112167,-966367641600⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-177620206720,-175243127744⟩,⟨-1140339154824,-1133343099871⟩,⟨-516408568121,-514789621363⟩,⟨-1182682706735,-1168215550957⟩,⟨753908525907,761653952234⟩,⟨-242542054574,-241023694128⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151451418629,-149101856669⟩,⟨-818310687414,-807544713008⟩,⟨-370365742551,-367019008460⟩,⟨983766624400,1018569284342⟩,⟨1368730324205,1385576768588⟩,⟨204219008777,207653569573⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149101856669,151451418629⟩,⟨807544713008,818310687414⟩,⟨367019008460,370365742551⟩,⟨-1018569284342,-983766624400⟩,⟨-1385576768588,-1368730324205⟩,⟨-207653569573,-204219008777⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨457315614209,465554721852⟩,⟨1663853035844,1721946514857⟩,⟨757316140488,778277272268⟩,⟨-7017368487816,-6487519872322⟩,⟨-5114191449173,-4855441925602⟩,⟨-1430901705980,-1347037020268⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨815216791111,825346874690⟩,⟨4065459917168,4137795924335⟩,⟨757316140488,778277272268⟩,⟨-19278242116474,-18533483660922⟩,⟨-5114191449173,-4855441925602⟩,⟨-1430901705980,-1347037020268⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨102361821346,107270163662⟩,⟨-266287972352,-258557031218⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11269916800200,11810319548031⟩,⟨27164275045901,30723818743360⟩,⟨-101388601853132,-92232189691121⟩,⟨130950006437721,159852243512270⟩,⟨-296480695558069,-190901674728216⟩,⟨1509643232693265,1740790931850197⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8355914733280,8865399948316⟩,⟨61811231859616,67508608362288⟩,⟨-68344775876471,-60024400622461⟩,⟨90895798239516,161272068609056⟩,⟨-640332519027934,-510591505768422⟩,⟨960399317146356,1165860801934079⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨94021419008,99688470784⟩,⟨-796399137895,-648212877034⟩,⟨629474421544,806263407114⟩,⟨6971991304232,11715135112704⟩,⟨-7470707867562,-1063971125433⟩,⟨-5384814006539,2912439243679⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1193533046784,1199200098560⟩,⟨-796399137895,-648212877034⟩,⟨629474421544,806263407114⟩,⟨6971991304232,11715135112704⟩,⟨-7470707867562,-1063971125433⟩,⟨-5384814006539,2912439243679⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨90216851968,95425122752⟩,⟨-733662226469,-594327499162⟩,⟨577146755329,742749430828⟩,⟨5902870818249,10471010542805⟩,⟨-6570227928161,-479915720370⟩,⟨-5462368484814,2380058550959⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨97931473829,104076949910⟩,⟨-869298946587,-698336622038⟩,⟨678149195696,880066159197⟩,⟨7680468094037,13499930910688⟩,⟨-8890275427883,-1288764283287⟩,⟨-5764123782700,3937920787110⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-99688470784,-94021419008⟩,⟨648212877034,796399137895⟩,⟨-806263407114,-629474421544⟩,⟨-11715135112704,-6971991304232⟩,⟨1063971125433,7470707867562⟩,⟨-2912439243679,5384814006539⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨999823156992,1005490208768⟩,⟨648212877034,796399137895⟩,⟨-806263407114,-629474421544⟩,⟨-11715135112704,-6971991304232⟩,⟨1063971125433,7470707867562⟩,⟨-2912439243679,5384814006539⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-104500845312,-98286349312⟩,⟨708825992891,875804992456⟩,⟨-886652789519,-688335341149⟩,⟨-13580819291277,-8080889871492⟩,⟨1607212523591,8921837449860⟩,⟨-3917829353350,5490789197105⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-95564770863,-89375105797⟩,⟨568867343512,742968829804⟩,⟨-754564057898,-549296970592⟩,⟨-10960492526795,-4966058093927⟩,⟨-532987562400,7252193153056⟩,⟨-3306447696153,6598419110555⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2366702966,14701844113⟩,⟨-300431603075,44632207766⟩,⟨-76414862202,330769188605⟩,⟨-3280024432758,8533872816761⟩,⟨-9423262990283,5963428869769⟩,⟨-9070571478853,10536339897665⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1183351483,7350922057⟩,⟨-150215801538,22316103883⟩,⟨-38207431101,165384594303⟩,⟨-1640012216379,4266936408381⟩,⟨-4711631495142,2981714434885⟩,⟨-4535285739427,5268169948833⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7350922057,-1183351483⟩,⟨-22316103883,150215801538⟩,⟨-165384594303,38207431101⟩,⟨-4266936408381,1640012216379⟩,⟨-2981714434885,4711631495142⟩,⟨-5268169948833,4535285739427⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754772461559,760940051397⟩,⟨-22316103883,150215801538⟩,⟨-165384594303,38207431101⟩,⟨-4266936408381,1640012216379⟩,⟨-2981714434885,4711631495142⟩,⟨-5268169948833,4535285739427⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8039957931,9038368451⟩,⟨-144412865104,-110859936316⟩,⟨107655211364,146201575452⟩,⟨1956680443412,3278028982556⟩,⟨-2522667137480,-924173038226⟩,⟨-255687748706,1710572716740⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9038368451,-8039957931⟩,⟨110859936316,144412865104⟩,⟨-146201575452,-107655211364⟩,⟨-3278028982556,-1956680443412⟩,⟨924173038226,2522667137480⟩,⟨-1710572716740,255687748706⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090473259325,1091471669845⟩,⟨110859936316,144412865104⟩,⟨-146201575452,-107655211364⟩,⟨-3278028982556,-1956680443412⟩,⟨924173038226,2522667137480⟩,⟨-1710572716740,255687748706⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9075722624,-8069497280⟩,⟨111676548646,145609828600⟩,⟨-147413364642,-108448217169⟩,⟨-3324482176931,-1982436570937⟩,⟨941995649049,2563098373218⟩,⟨-1744514725236,247110430556⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4537861312,-4034748640⟩,⟨55838274323,72804914300⟩,⟨-73706682321,-54224108584⟩,⟨-1662241088466,-991218285468⟩,⟨470997824524,1281549186609⟩,⟨-872257362618,123555215278⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4034748640,4537861312⟩,⟨-72804914300,-55838274323⟩,⟨54224108584,73706682321⟩,⟨991218285468,1662241088466⟩,⟨-1281549186609,-470997824524⟩,⟨-123555215278,872257362618⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766158132256,766661264192⟩,⟨-72804914300,-55838274323⟩,⟨54224108584,73706682321⟩,⟨991218285468,1662241088466⟩,⟨-1281549186609,-470997824524⟩,⟨-123555215278,872257362618⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272618314831,272867917462⟩,⟨27714984079,36103216276⟩,⟨-36550393863,-26913802841⟩,⟨-819507245639,-489170110853⟩,⟨231043259556,630666784370⟩,⟨-427643179185,63921937177⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532316264512,1533322528384⟩,⟨-145609828600,-111676548646⟩,⟨108448217168,147413364642⟩,⟨1982436570936,3324482176932⟩,⟨-2563098373218,-941995649048⟩,⟨-247110430556,1744514725236⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1202324805425,1209139647507⟩,⟨-963128095340,-775106922431⟩,⟨752700229999,975057483975⟩,⟨9336208928551,15702079913348⟩,⟨-10588071383283,-2242745697532⟩,⟨-5569706828478,5094753070273⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1305137983074,1318767667238⟩,⟨-1926256190680,-1550213844862⟩,⟨1505400459998,1950114967950⟩,⟨18672417857111,31404159826688⟩,⟨-21176142766561,-4485491395065⟩,⟨-11134556192401,10189506140544⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨188503201280,199925968000⟩,⟨-1622771773711,-1292477962804⟩,⟨1255115174071,1642871566509⟩,⟨13172921203554,24937079296449⟩,⟨-16364420975613,-1315023352931⟩,⟨-11835041686221,7151395051576⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨64542089479,68991494193⟩,⟨-553188018960,-431353733137⟩,⟨417115208019,561455598316⟩,⟨4181528496239,8288726236506⟩,⟨-5484639045049,-73246259895⟩,⟨-4446868429935,2482845843463⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379930022808,380527603846⟩,⟨2488259436,22658061758⟩,⟨-24082121056,-924119391⟩,⟨-660870110509,137689297618⟩,⟨-308632197361,655613362259⟩,⟨-667495862582,516772650844⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176972727854,3181969697156⟩,⟨-189764592378,-20774136457⟩,⟨7715345937,201691297985⟩,⟨-1152896390964,5557518317448⟩,⟨-5514914836278,2584739044953⟩,⟨-4328009315359,5615944484861⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨186490486224,199660320399⟩,⟨-1612824831622,-1247590127975⟩,⟨1205682205906,1637499448547⟩,⟨12026233845298,24527115058993⟩,⟨-16416884189690,-60362811212⟩,⟨-13134886143773,7743687142189⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨374993687504,399586288399⟩,⟨-3235596605333,-2540068090779⟩,⟨2460797379977,3280371015056⟩,⟨25199155048852,49464194355442⟩,⟨-32781305165303,-1375386164143⟩,⟨-24969927829994,14895082193765⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518122277506,526624500545⟩,⟨-30888654212,207919983484⟩,⟨-228915744974,52884505906⟩,⟨-5912143099220,2311054717676⟩,⟨-4172305697884,6532006358550⟩,⟨-7303388760421,6327232090721⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355671024209,364461515812⟩,⟨-32065710171,215843069217⟩,⟨-237638903964,54899744977⟩,⟨-6143763727424,2441729924557⟩,⟨-4378209188385,6791755380591⟩,⟨-7593626789391,6619989267068⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711342048418,728923031624⟩,⟨-64131420342,431686138434⟩,⟨-475277807928,109799489954⟩,⟨-12287527454848,4883459849114⟩,⟨-8756418376770,13583510761182⟩,⟨-15187253578782,13239978534136⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523277896061,1525282570453⟩,⟨-34749892284,32736316458⟩,⟨-37753358284,39758153278⟩,⟨-1295592411620,1367801733520⟩,⟨-1638925334992,1580671488432⟩,⟨-1957683147296,2000202473942⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨985502646375,1011188574319⟩,⟨-112002939658,620553326278⟩,⟨-684351333740,178675583713⟩,⟨-17931907407631,7707005357312⟩,⟨-13262723950581,19922080318095⟩,⟨-22400532404689,19725656610893⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67594324338,67718156407⟩,⟨13743578628,17919609380⟩,⟨-18141563226,-13346281004⟩,⟨-405360178995,-240203533503⟩,⟨112171687392,311670767492⟩,⟨-210940472131,34157305290⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50116821679,50832539956⟩,⟨260120952854,268295302870⟩,⟨32939342705,38038151323⟩,⟨-1389982422273,-1182598576786⟩,⟨-290617413938,-101205085408⟩,⟨-272153026921,-75556399781⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135487315616,2138292962673⟩,⟨-406119998928,-311272364078⟩,⟨302274142128,411150236670⟩,⟨5548265930931,9310871317732⟩,⟨-7187775396014,-2647623435650⟩,⟨-667821903997,4905149452275⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2976086713149,2981953704832⟩,⟨-849531184372,-650699402517⟩,⟨631889066869,860053551747⟩,⟨11645797643421,19557369997256⟩,⟨-15117228202821,-5580777795814⟩,⟨-1352253713222,10343390204106⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135652960220,137861462325⟩,⟨664803050063,697976417050⟩,⟨117960200303,142924102690⟩,⟨-3653497808739,-2604689340614⟩,⟨-1366972165124,-337942072360⟩,⟨-762755186558,333191649265⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8769135327787,8911901499636⟩,⟨-45854488304058,-42287001849612⟩,⟨-9389588867295,-7503249583347⟩,⟨573517265786521,711892430126553⟩,⟨93861083177536,186429728018091⟩,⟨-9049261677303,69895977224064⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7859858735132,8196014252361⟩,⟨-43078847575280,-32872451002727⟩,⟨-14182220782093,-5277009330129⟩,⟨316945334064486,726516408633712⟩,⟨-36121092915827,362425880786903⟩,⟨-192937685721958,235852601345837⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15719717470264,16392028504722⟩,⟨-86157695150560,-65744902005454⟩,⟨-28364441564186,-10554018660258⟩,⟨633890668128972,1453032817267424⟩,⟨-72242185831654,724851761573806⟩,⟨-385875371443916,471705202691674⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10909882818222,10952333724170⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145760,2173453475298114⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9810371190446,9852822096394⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145775,2173453475298112⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2406362562496,2411110103296⟩,⟨-12227224809080,-12080350374972⟩,⟨0,0⟩,⟨103760055435140,110865974497594⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7370791423753,7462916583458⟩,⟨-44698568388556,-43428114074848⟩,⟨-20241981169316,-19726014481988⟩,⟨511749955647988,535437316937166⟩,⟨281859745201608,293130017840311⟩,⟨105583138898675,109806346373251⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6271279795977,6363404955682⟩,⟨-44698568388556,-43428114074847⟩,⟨-20241981169317,-19726014481988⟩,⟨511749955647987,535437316937164⟩,⟨281859745201606,293130017840310⟩,⟨105583138898674,109806346373251⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1914375461440,1930409850112⟩,⟨-7836772921517,-7503799731461⟩,⟨-3548923726743,-3408392589133⟩,⟨32566950746512,42664577053348⟩,⟨23406644019728,28131855537894⟩,⟨6788402140752,8686061562785⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99256358666,99685855397⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137826624935,139851299364⟩,⟨677482103437,684913690020⟩,⟨307925270526,309972134136⟩,⟨-1712309844053,-1698693120000⟩,⟨-1550957989072,-1543064308938⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4320738023936,4341519953408⟩,⟨-20063997730597,-19584150106433⟩,⟨-3548923726743,-3408392589133⟩,⟨136327006181652,153530551550942⟩,⟨23406644019728,28131855537894⟩,⟨6788402140752,8686061562785⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨749987375008,799172576798⟩,⟨-6471193210666,-5080136181558⟩,⟨4921594759954,6560742030112⟩,⟨50398310097704,98928388710884⟩,⟨-65562610330606,-2750772328286⟩,⟨-49939855659988,29790164387530⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5070725398944,5140692530206⟩,⟨-26535190941263,-24664286287991⟩,⟨1372671033211,3152349440979⟩,⟨186725316279356,252458940261826⟩,⟨-42155966310878,25381083209608⟩,⟨-43151453519236,38476225950315⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457750264917,466074500043⟩,⟨1642877198638,1882015478376⟩,⟨123915313818,285803844722⟩,⟨-35839950145880,-26638356869511⟩,⟨-2726026271344,4820561148553⟩,⟨-3912272910101,3488399212352⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38254637048,40365778393⟩,⟨-812133361614,-769635996262⟩,⟨328085346598,330673870673⟩,⟨9505596667799,10242690763936⟩,⟨-6659570832821,-6593775017748⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨496004901965,506440278436⟩,⟨830743837024,1112379482114⟩,⟨452000660416,616477715395⟩,⟨-26334353478081,-16395666105575⟩,⟨-9385597104165,-1773213869195⟩,⟨-3912272910101,3488399212352⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501398014948,502387228948⟩,⟨2512147284185,2552733193796⟩,⟨0,0⟩,⟨2027158573049,4364694834823⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226187579073,231401943994⟩,⟨1512099223170,1684067824497⟩,⟨206120815971,281680087161⟩,⟨-7322033100201,-301116520375⟩,⟨-3255728997529,622655728177⟩,⟨-1787589959526,1593914215626⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-799172576798,-749987375008⟩,⟨5080136181558,6471193210666⟩,⟨-6560742030112,-4921594759954⟩,⟨-98928388710884,-50398310097704⟩,⟨2750772328286,65562610330606⟩,⟨-29790164387530,49939855659988⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3521565447138,3591532578400⟩,⟨-14983861549039,-13112956895767⟩,⟨-10109665756855,-8329987349087⟩,⟨37398617470768,103132241453238⟩,⟨26157416348014,93694465868500⟩,⟨-23001762246778,58625917222773⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441437332544,456821451551⟩,⟨264012723522,593513722595⟩,⟨-299652037255,-31667717785⟩,⟨-19572867290303,-8482373471607⟩,⟨-12309061051899,-1829846322406⟩,⟨-9772927102663,1668629984108⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨323982133820,328031482676⟩,⟨1932735283200,1940466224334⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-328031482676,-323982133820⟩,⟨-1940466224334,-1932735283200⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨771480145100,775529493956⟩,⟨-1940466224334,-1932735283200⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1343235143183,1361595217700⟩,⟨-8934460903526,-8630207508072⟩,⟨-4046017487520,-3920032032553⟩,⟨49231378293830,57754390742038⟩,⟨32234819187794,36229933440566⟩,⟨10205907505972,11799359135289⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1361595217700,-1343235143183⟩,⟨8630207508072,8934460903526⟩,⟨3920032032553,4046017487520⟩,⟨-57754390742038,-49231378293830⟩,⟨-36229933440566,-32234819187794⟩,⟨-11799359135289,-10205907505972⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-262083589924,-243723515407⟩,⟨8630207508072,8934460903526⟩,⟨3920032032553,4046017487520⟩,⟨-57754390742038,-49231378293830⟩,⟨-36229933440566,-32234819187794⟩,⟨-11799359135289,-10205907505972⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12784653147,-11345029152⟩,⟨430382073182,467567038460⟩,⟨77741598496,100069064755⟩,⟨-4981121448152,-4321107195980⟩,⟨1431790777318,1870976820693⟩,⟨2554318129395,2758580627429⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428652679397,445476422399⟩,⟨694394796704,1061080761055⟩,⟨-221910438759,68401346970⟩,⟨-24553988738455,-12803480667587⟩,⟨-10877270274581,41130498287⟩,⟨-7218608973268,4427210611537⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99685855397,-99256358666⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4620261121,4862758044⟩,⟨28793424313,31195786512⟩,⟨39624999436,39835402372⟩,⟨-320092504066,-308803450959⟩,⟨250784818133,251900503000⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10111783367,10663502553⟩,⟨8939771320,17646109768⟩,⟨86722243560,87354729775⟩,⟨-959749295418,-818225055495⟩,⟨105867709348,117030113883⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1464748770107,1482950097197⟩,⟨-7527009913292,-7214999651899⟩,⟨-1415753906373,-1344014158625⟩,⟨103970201867730,111478485103174⟩,⟨21857566221001,23675042521681⟩,⟨4857058495520,5306139480982⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13470728163,14382241850⟩,⟨-61090550282,-42553632080⟩,⟨101799200092,105458025244⟩,⟨-579876577218,-126186866625⟩,⟨-278681813334,-192546796092⟩,⟨-180291023327,-160552931012⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14382241850,-13470728163⟩,⟨42553632080,61090550282⟩,⟨-105458025244,-101799200092⟩,⟨126186866625,579876577218⟩,⟨192546796092,278681813334⟩,⟨160552931012,180291023327⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114068097247,-112727086829⟩,⟨-836196676682,-816800765020⟩,⟨-105458025244,-101799200092⟩,⟨2325210122177,2778899832770⟩,⟨192546796092,278681813334⟩,⟨160552931012,180291023327⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨89111817475,94166980742⟩,⟨-616044798639,-574381303283⟩,⟨591135159462,612753400919⟩,⟨3280516810691,3979181613064⟩,⟨-3571754948597,-3107985469198⟩,⟨-2520374634579,-2297675228355⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨118713092022,127006326915⟩,⟨-1475527361954,-1349932099054⟩,⟨666247821711,717514168231⟩,⟨20334872189722,23348976112623⟩,⟨-6538531320724,-5198565086067⟩,⟨-4583657338293,-4051655085707⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-127006326915,-118713092022⟩,⟨1349932099054,1475527361954⟩,⟨-717514168231,-666247821711⟩,⟨-23348976112623,-20334872189722⟩,⟨5198565086067,6538531320724⟩,⟨4051655085707,4583657338293⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨972505300861,980798535754⟩,⟨1349932099054,1475527361954⟩,⟨-717514168231,-666247821711⟩,⟨-23348976112623,-20334872189722⟩,⟨5198565086067,6538531320724⟩,⟨4051655085707,4583657338293⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121906053526,124751704461⟩,⟨768442552666,798642543583⟩,⟨181092827111,192988888238⟩,⟨-2833718062945,-2213216326460⟩,⟨-800749798322,-527702222076⟩,⟨-209917730789,-100147403535⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11557309430,11833918334⟩,⟨167484487538,173501328088⟩,⟨20873862500,21881344364⟩,⟨636973115202,795099765595⟩,⟨93425042594,120923524878⟩,⟨-18558015368,-12691578569⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165234850061,176425534532⟩,⟨1467220223722,1895572986272⟩,⟨-6849644750,215280634757⟩,⟨-11421289913198,7463192811572⟩,⟨-5632325457771,6748481579141⟩,⟨-5558763747824,4494728771850⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176425534532,-165234850061⟩,⟨-1895572986272,-1467220223722⟩,⟨-215280634757,6849644750⟩,⟨-7463192811572,11421289913198⟩,⟨-6748481579141,5632325457771⟩,⟨-4494728771850,5558763747824⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49762044541,66167093933⟩,⟨-383473763102,216847600775⟩,⟨-9159818786,288529731911⟩,⟨-14785225911773,11120173392823⟩,⟨-10004210576670,6254981185948⟩,⟨-6282318731376,7152677963450⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27369825498538,28779443972628⟩,⟨-268101092384431,-221751214527128⟩,⟨-102708378361319,-67105541231003⟩,⟨2466659826433890,4415327940352532⟩,⟨483640617814183,2172284379800174⟩,⟨-514993531623457,1140772854052501⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13516078876,14154454917⟩,⟨170398923650,181229586028⟩,⟨40156577368,43793429996⟩,⟨431087389066,669434383714⟩,⟨71421767910,163343504494⟩,⟨12018094489,45540466541⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336451849089,370489344502⟩,⟨790318135918,2017695633985⟩,⟨-322600131707,321367021247⟩,⟨-47327689194638,5629929608343⟩,⟨-19884407493657,13741514301131⟩,⟨-14512283025818,10975954430252⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370489344502,-336451849089⟩,⟨-2017695633985,-790318135918⟩,⟨-321367021247,322600131707⟩,⟨-5629929608343,47327689194638⟩,⟨-13741514301131,19884407493657⟩,⟨-10975954430252,14512283025818⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58163334895,109024573310⟩,⟨-1323300837281,270762625137⟩,⟨-543277460006,391001478677⟩,⟨-30183918346798,34524208527051⟩,⟨-24618784575712,19925537991944⟩,⟨-18194563403520,18939493637355⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237082983601,239537154761⟩,⟨1555373418739,1563663998782⟩,⟨307925270526,309972134136⟩,⟨-3911333099605,-3897716375552⟩,⟨-1550957989072,-1543064308938⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1700580015998,-1611659132502⟩,⟨-5725931698901,-2739427970116⟩,⟨-490169602874,1487226849855⟩,⟨-19819772219384,107488370845408⟩,⟨-58519045564458,41484746424219⟩,⟨-44687009816042,48161310567253⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192949533419,-178689337619⟩,⟨-1884905294545,-1430107941416⟩,⟨-354104977379,-96702773774⟩,⟨-7322837859140,12749420181642⟩,⟨-7227196022789,6574467814857⟩,⟨-5095509311766,6311187456002⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44133450182,60847817142⟩,⟨-329531875806,133556057366⟩,⟨-46179706853,213269360362⟩,⟨-11234170958745,8851703806090⟩,⟨-8778154011861,5031403505919⟩,⟨-5446666173432,5960716782472⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2632374582,6560948517⟩,⟨-117658632190,37796137985⟩,⟨-33601951203,52139750985⟩,⟨-3804456655580,4103313596202⟩,⟨-2957138954289,2079848235079⟩,⟨-2002991008936,2054202942578⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1771478696,3367364890⟩,⟨-36473093718,14782189386⟩,⟨-5111240824,23604980092⟩,⟨-1323470784609,1177246507288⟩,⟨-1099416408634,608694491210⟩,⟨-620760081615,742475867601⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3084346959,5912074224⟩,⟨-88036625461,13863302806⟩,⟨-19842728569,35951771882⟩,⟨-2481864341923,2717477544977⟩,⟨-2108488501855,1308995638774⟩,⟨-1231310683735,1363160367596⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5912074224,-3084346959⟩,⟨-13863302806,88036625461⟩,⟨-35951771882,19842728569⟩,⟨-2717477544977,2481864341923⟩,⟨-1308995638774,2108488501855⟩,⟨-1363160367596,1231310683735⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3279699642,3476601558⟩,⟨-131521934996,125832763446⟩,⟨-69553723085,71982479554⟩,⟨-6521934200557,6585177938125⟩,⟨-4266134593063,4188336736934⟩,⟨-3366151376532,3285513626313⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49762044541,66167093933⟩,⟨-383473763102,216847600775⟩,⟨-9159818786,288529731911⟩,⟨-14785225911773,11120173392823⟩,⟨-10004210576670,6254981185948⟩,⟨-6282318731376,7152677963450⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3279699642,3476601558⟩,⟨-131521934996,125832763446⟩,⟨-69553723085,71982479554⟩,⟨-6521934200557,6585177938125⟩,⟨-4266134593063,4188336736934⟩,⟨-3366151376532,3285513626313⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (103/1024) u, BivariateJet2.affineZ (611/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000019

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000020Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2090960632704,-2090960593920⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2090960632704,-2090960593920⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-177801781504,-177801781440⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-177801781504,-177801781440⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨95366208320,95366208384⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-104430186816,-104430186752⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨95366331520,95366331584⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-104430334656,-104430334592⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-9064003072,-9064003008⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-9063978496,-9063978432⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨199796395072,199796395136⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨199796666112,199796666176⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1913158812480,1913158851072⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1913158812544,1913158851136⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2531719137984,-2531719080128⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-115845112128,-115845112064⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2097769269760,-2097769230976⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2084188872832,-2084188834112⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-178994668736,-178994668672⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-176611073536,-176611073472⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨92766774528,92766774592⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-101320844480,-101320844416⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨97987637184,97987637248⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-107582254656,-107582254592⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9594617408,-9594617344⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8554069888,-8554069824⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨194087618944,194087619008⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨205569891776,205569891840⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2415873968064,2415874025920⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1905194165440,1905194204032⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1921158157504,1921158196096⟩



end LaneCBRB2Cell000020Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000020
open Set LaneCBRB2Cell000020Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨135076721459,135076721460⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110165911143,-110165911142⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439589902745,439589902746⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨54004306411,54004306412⟩,⟨-135076721460,-135076721459⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨164170217553,164170217555⟩,⟨964434906316,964434906317⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨54004306410,54004306413⟩,⟨-135076721460,-135076721459⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2090960632704,-2090960593920⟩,⟨6459194667097,6459194667184⟩,⟨2944104093418,2944104093461⟩,⟨-37945206484954,-37945206483947⟩,⟨-24659299570414,-24659299569842⟩,⟨-7883271712794,-7883271712564⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312205394921,-312205389126⟩,⟨-869647945547,-869647911500⟩,⟨-396385959595,-396385944073⟩,⟨5665672509596,5665672509981⟩,⟨3573865271433,3573865310432⟩,⟨1177066616999,1177066617090⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨312205389126,312205394921⟩,⟨869647911500,869647945547⟩,⟨396385944073,396385959595⟩,⟨-5665672509981,-5665672509596⟩,⟨-3573865310432,-3573865271433⟩,⟨-1177066617090,-1177066616999⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164170217555,-164170217553⟩,⟨-964434906317,-964434906316⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨935341410221,935341410223⟩,⟨-964434906317,-964434906316⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-177801781504,-177801781440⟩,⟨-1133711586103,-1133711586097⟩,⟨-516746296316,-516746296312⟩,⟨-1168975323221,-1168975323208⟩,⟨759677317789,759677317800⟩,⟨-242859400493,-242859400489⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151253852030,-151253851974⟩,⟨-808476351546,-808476351481⟩,⟨-368503917083,-368503917051⟩,⟨994433346309,994433346337⟩,⟨1374973052657,1374973052742⟩,⟨206597591510,206597591520⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151253851974,151253852030⟩,⟨808476351481,808476351546⟩,⟨368503917051,368503917083⟩,⟨-994433346337,-994433346309⟩,⟨-1374973052742,-1374973052657⟩,⟨-206597591520,-206597591510⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨463459241100,463459246951⟩,⟨1678124262981,1678124297093⟩,⟨764889861124,764889876678⟩,⟨-6660105856318,-6660105855905⟩,⟨-4948838363174,-4948838324090⟩,⟨-1383664208610,-1383664208509⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨821363367427,821363379137⟩,⟨4091614206648,4091614298706⟩,⟨764889861124,764889876678⟩,⟨-18855733924531,-18855733923598⟩,⟨-4948838363174,-4948838324090⟩,⟨-1383664208610,-1383664208509⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨108008612820,108008612826⟩,⟨-270153442920,-270153442918⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11192864976075,11192864976698⟩,⟨27995832279357,27995832282683⟩,⟨-91108853231103,-91108853220751⟩,⟨140047543982576,140047544008038⟩,⟨-227883404312387,-227883404206489⟩,⟨1483234748733881,1483234748988330⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8361357020389,8361357140061⟩,⟨62565628854003,62565630094105⟩,⟨-60274184417783,-60274183280951⟩,⟨121032397722858,121032403966323⟩,⟨-540181027609521,-540181016637657⟩,⟨967166708706202,967166727286924⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨99624216576,99624350976⟩,⟨-736659548959,-736657516231⟩,⟨709677677055,709679634654⟩,⟨9404499721287,9404549592460⟩,⟨-4072797391864,-4072735635754⟩,⟨-1336777256907,-1336703266834⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1199135844352,1199135978752⟩,⟨-736659548959,-736657516231⟩,⟨709677677055,709679634654⟩,⟨9404499721287,9404549592460⟩,⟨-4072797391864,-4072735635754⟩,⟨-1336777256907,-1336703266834⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨95366208320,95366331584⟩,⟨-675457867104,-675455927548⟩,⟨650717576422,650719444319⟩,⟨8208221943036,8208271020449⟩,⟨-3334678192535,-3334618853194⟩,⟨-1610830402846,-1610760211558⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨104007120841,104007266932⟩,⟨-800553925171,-800551468415⟩,⟨771231534260,771233900300⟩,⟨10672742065869,10672807069791⟩,⟨-4862029281393,-4861953435845⟩,⟨-1032721010006,-1032632966168⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-99624350976,-99624216576⟩,⟨736657516231,736659548959⟩,⟨-709679634654,-709677677055⟩,⟨-9404549592460,-9404499721287⟩,⟨4072735635754,4072797391864⟩,⟨1336703266834,1336777256907⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨999887276800,999887411200⟩,⟨736657516231,736659548959⟩,⟨-709679634654,-709677677055⟩,⟨-9404549592460,-9404499721287⟩,⟨4072735635754,4072797391864⟩,⟨1336703266834,1336777256907⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-104430334656,-104430186752⟩,⟨810054707871,810057052017⟩,⟨-780388978242,-780386720699⟩,⟨-10938380902779,-10938321218539⟩,⟨5053466895510,5053538733714⟩,⟨915997676438,916082440754⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-94968142521,-94967995252⟩,⟨666690350669,666692873596⟩,⟨-642275465757,-642273035978⟩,⟨-7968601424340,-7968533672826⟩,⟨3163051289886,3163129560637⟩,⟨1713433808843,1713523905237⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨9038978320,9039271680⟩,⟨-133863574502,-133858594819⟩,⟨128956068503,128960864322⟩,⟨2704140641529,2704273396965⟩,⟨-1698977991507,-1698823875208⟩,⟨680712798837,680890939069⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4519489160,4519635840⟩,⟨-66931787251,-66929297409⟩,⟨64478034251,64480432161⟩,⟨1352070320764,1352136698483⟩,⟨-849488995754,-849411937604⟩,⟨340356399418,340445469535⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4519635840,-4519489160⟩,⟨66929297409,66931787251⟩,⟨-64480432161,-64478034251⟩,⟨-1352136698483,-1352070320764⟩,⟨849411937604,849488995754⟩,⟨-340445469535,-340356399418⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757603747776,757603913720⟩,⟨66929297409,66931787251⟩,⟨-64480432161,-64478034251⟩,⟨-1352136698483,-1352070320764⟩,⟨849411937604,849488995754⟩,⟨-340445469535,-340356399418⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨9026720843,9026745200⟩,⟨-133494230714,-133493682258⟩,⟨128604520064,128605048310⟩,⟨2691340729582,2691357513766⟩,⟨-1689008197704,-1688990763680⟩,⟨673875253943,673894043013⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9026745200,-9026720843⟩,⟨133493682258,133494230714⟩,⟨-128605048310,-128604520064⟩,⟨-2691357513766,-2691340729582⟩,⟨1688990763680,1689008197704⟩,⟨-673894043013,-673875253943⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090484882576,1090484906933⟩,⟨133493682258,133494230714⟩,⟨-128605048310,-128604520064⟩,⟨-2691357513766,-2691340729582⟩,⟨1688990763680,1689008197704⟩,⟨-673894043013,-673875253943⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9064003072,-9063978432⟩,⟨134598704616,134599260620⟩,⟨-129669606858,-129669071342⟩,⟨-2730113138853,-2730096018991⟩,⟨1718845417999,1718863165506⟩,⟨-694764791647,-694745705557⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4532001536,-4531989216⟩,⟨67299352308,67299630310⟩,⟨-64834803429,-64834535671⟩,⟨-1365056569427,-1365048009495⟩,⟨859422708999,859431582753⟩,⟨-347382395824,-347372852778⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4531989216,4532001536⟩,⟨-67299630310,-67299352308⟩,⟨64834535671,64834803429⟩,⟨1365048009495,1365056569427⟩,⟨-859431582753,-859422708999⟩,⟨347372852778,347382395824⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766655372832,766655404416⟩,⟨-67299630310,-67299352308⟩,⟨64834535671,64834803429⟩,⟨1365048009495,1365056569427⟩,⟨-859431582753,-859422708999⟩,⟨347372852778,347382395824⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272621220644,272621226734⟩,⟨33373420564,33373557679⟩,⟨-32151262078,-32151130016⟩,⟨-672839378442,-672835182395⟩,⟨422247690920,422252049426⟩,⟨-168473510754,-168468813485⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533310745664,1533310808832⟩,⟨-134599260620,-134598704616⟩,⟨129669071342,129669606858⟩,⟨2730096018990,2730113138854⟩,⟨-1718863165506,-1718845417998⟩,⟨694745705556,694764791648⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1209061946448,1209062108965⟩,⟨-890767558024,-890764860585⟩,⟨858140890623,858143488445⟩,⟨12684428122410,12684499256525⟩,⟨-6189281869938,-6189198383672⟩,⟨-398284921439,-398187806665⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1318612265120,1318612590154⟩,⟨-1781535116049,-1781529721170⟩,⟨1716281781246,1716286976891⟩,⟨25368856244827,25368998513042⟩,⟨-12378563739872,-12378396767346⟩,⟨-796569693975,-796375762233⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨199796395072,199796666176⟩,⟨-1485515209591,-1485510344948⟩,⟨1431104017289,1431108702392⟩,⟨19146529048321,19146666036482⟩,⟨-8388228554611,-8388074120357⟩,⟨-2526922399734,-2526748331897⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨68644730933,68644838577⟩,⟨-501521188700,-501519443112⟩,⟨483151458542,483153139661⟩,⟨6267843321776,6267888867639⟩,⟨-2642945026453,-2642891321636⟩,⟨-1035173445078,-1035110824342⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380180651618,380180675774⟩,⟨13166944719,13167276457⟩,⟨-12685029246,-12684709733⟩,⟨-269550487044,-269540269566⟩,⟨170524197487,170534774673⟩,⟨-70265665076,-70254306208⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179871825819,3179872027863⟩,⟨-110132522291,-110129733603⟩,⟨106096268613,106098954538⟩,⟨2262091968757,2262178101185⟩,⟨-1433720590392,-1433631568745⟩,⟨594694323258,594789762748⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨198525818527,198526142457⟩,⟨-1457313581836,-1457308256415⟩,⟨1403934821094,1403939949879⟩,⟨18368776625208,18368917991700⟩,⟨-7829900120683,-7829735831032⟩,⟨-2863430669396,-2863240673535⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨398322213599,398322808633⟩,⟨-2942828791427,-2942818601363⟩,⟨2835038838383,2835048652271⟩,⟨37515305673529,37515584028182⟩,⟨-16218128675294,-16217809951389⟩,⟨-5390353069130,-5389989005432⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522016706458,522016935142⟩,⟨92233470336,92236921726⟩,⟨-88858774260,-88855450298⟩,⟨-1855195521428,-1855103033671⟩,⟨1162701440564,1162808472720⟩,⟨-461596579458,-461473169063⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359688613765,359688850124⟩,⟨95328354468,95331942552⟩,⟨-91840440948,-91836985334⟩,⟨-1909025195575,-1908928554730⟩,⟨1193601963549,1193713456928⟩,⟨-469269458530,-469141218394⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨719377227530,719377700248⟩,⟨190656708936,190663885104⟩,⟨-183680881896,-183673970668⟩,⟨-3818050391150,-3817857109460⟩,⟨2387203927098,2387426913856⟩,⟨-938538917060,-938282436788⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524284000464,1524284087989⟩,⟨-1105578362,-1104473902⟩,⟨1064023032,1065086794⟩,⟨38738505224,38772409272⟩,⟨-29872401826,-29837220294⟩,⟨20851662543,20889537705⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨997292953090,997293665698⟩,⟨263589429407,263600116201⟩,⟨-253945847002,-253935554702⟩,⟨-5268109314436,-5267818462116⟩,⟨3290272560143,3290605296945⟩,⟨-1287836310629,-1287455511726⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67595765308,67595768329⟩,⟨16549716112,16549784478⟩,⟨-15943654052,-15943588204⟩,⟨-331631802594,-331629697691⟩,⟨207438786514,207440968594⟩,⟨-81664911730,-81662565060⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50495769225,50495772203⟩,⟨263907281076,263907349227⟩,⟨35113573149,35113625569⟩,⟨-1283777176400,-1283775036991⟩,⟨-197100675091,-197098732639⟩,⟨-168253511502,-168251661732⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2138260099644,2138260275825⟩,⟨-375407582706,-375406016500⟩,⟨361656894654,361658403150⟩,⟨7647399568478,7647447903036⟩,⟨-4825787807536,-4825737848626⟩,⟨1968283184206,1968336749220⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2981884961453,2981885329990⟩,⟨-785280241345,-785276932792⟩,⟨756516423483,756519610133⟩,⟨16065817951482,16065920289431⟩,⟨-10161027003168,-10160921531574⟩,⟨4181245645477,4181358393844⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136944959075,136944984078⟩,⟨679654313421,679654740781⟩,⟨129971808246,129972110579⟩,⟨-3120751850823,-3120739189375⟩,⟨-844688075121,-844676914876⟩,⟨-215959037571,-215948499545⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8827821097310,8827822709068⟩,⟨-43812284844356,-43812241297409⟩,⟨-8378335041062,-8378312492526⟩,⟨636048741751658,636050416490242⟩,⟨137612700938989,137613731530859⟩,⟨29823973452700,29824740542007⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8007122024979,8007129208326⟩,⟨-37622879816888,-37622725733919⟩,⟨-9638324063950,-9638215173924⟩,⟨513612709418203,513617856180986⟩,⟨159346264018190,159350471322194⟩,⟨20581456546551,20585398190002⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16014244049958,16014258416652⟩,⟨-75245759633776,-75245451467838⟩,⟨-19276648127900,-19276430347848⟩,⟨1027225418836406,1027235712361972⟩,⟨318692528036380,318700942644388⟩,⟨41162913093102,41170796380004⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10973683302499,10973683302600⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨2186188521914400,2186188521974786⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9874171674723,9874171674824⟩,⟨-109522921071186,-109522921069170⟩,⟨0,0⟩,⟨2186188521914418,2186188521974777⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2413489943680,2413490001536⟩,⟨-12195628068220,-12195628067696⟩,⟨0,0⟩,⟨108164909937337,108164909975027⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7363855866303,7363855866393⟩,⟨-43259732176113,-43259732175010⟩,⟨-19717807117472,-19717807116944⟩,⟨508267533159399,508267533179098⟩,⟨280987189737913,280987189748385⟩,⟨105594657081799,105594657086154⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6264344238527,6264344238617⟩,⟨-43259732176114,-43259732175009⟩,⟨-19717807117472,-19717807116943⟩,⟨508267533159399,508267533179096⟩,⟨280987189737911,280987189748385⟩,⟨105594657081798,105594657086154⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1913158812480,1913158851136⟩,⟨-7592906253417,-7592906253064⟩,⟨-3460850389837,-3460850389671⟩,⟨36776231155948,36776231167081⟩,⟨25418976885276,25418976890824⟩,⟨7640412311051,7640412313445⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99127803248,99127803250⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139657643378,139657643381⟩,⟨676431606690,676431606697⟩,⟨308317857691,308317857696⟩,⟨-1691905142294,-1691905142289⟩,⟨-1542342385340,-1542342385332⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4326648756160,4326648852672⟩,⟨-19788534321637,-19788534320760⟩,⟨-3460850389837,-3460850389671⟩,⟨144941141093285,144941141142108⟩,⟨25418976885276,25418976890824⟩,⟨7640412311051,7640412313445⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨796644427198,796645617266⟩,⟨-5885657582854,-5885637202726⟩,⟨5670077676766,5670097304542⟩,⟨75030611347058,75031168056364⟩,⟨-32436257350588,-32435619902778⟩,⟨-10780706138260,-10779978010864⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5123293183358,5123294469938⟩,⟨-25674191904491,-25674171523486⟩,⟨2209227286929,2209246914871⟩,⟨219971752440343,219972309198472⟩,⟨-7017280465312,-7016643011954⟩,⟨-3140293827209,-3139565697419⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461896705621,461896821624⟩,⟨1781945375752,1781948242045⟩,⟨199175563310,199177332896⟩,⟨-31473418110109,-31473332747564⟩,⟨1133867425859,1133940590945⟩,⟨-283116995571,-283051350141⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨40783383053,40783385329⟩,⟨-818065804571,-818065793139⟩,⟨331972847757,331972866257⟩,⟨10226150772266,10226150802796⟩,⟨-6658977614141,-6658977521421⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨502680088674,502680206953⟩,⟨963879571181,963882448906⟩,⟨531148411067,531150199153⟩,⟨-21247267337843,-21247181944768⟩,⟨-5525110188282,-5525036930476⟩,⟨-283116995571,-283051350141⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500903595558,500903607567⟩,⟨2531120470889,2531120592376⟩,⟨0,0⟩,⟨3131155626176,3131158552760⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229005548892,229005608267⟩,⟨1596303814622,1596305463979⟩,⟨241974838789,241975659188⟩,⟨-3810303173371,-3810248901748⟩,⟨-1294344664697,-1294307055418⟩,⟨-128979376719,-128949467592⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-796645617266,-796644427198⟩,⟨5885637202726,5885657582854⟩,⟨-5670097304542,-5670077676766⟩,⟨-75031168056364,-75030611347058⟩,⟨32435619902778,32436257350588⟩,⟨10779978010864,10780706138260⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3530003138894,3530004425474⟩,⟨-13902897118911,-13902876737906⟩,⟨-9130947694379,-9130928066437⟩,⟨69909973036921,69910529795050⟩,⟨57854596788054,57855234241412⟩,⟨18420390321915,18421118451705⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨448373538797,448373702226⟩,⟨405780017050,405783397383⟩,⟨-169933292825,-169930438907⟩,⟨-13658508240589,-13658410464964⟩,⟨-7119171527748,-7119070964275⟩,⟨-3909660744211,-3909556839376⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨328340435106,328340435110⟩,⟨1928869812632,1928869812634⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-328340435110,-328340435106⟩,⟨-1928869812634,-1928869812632⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨771171192666,771171192670⟩,⟨-1928869812634,-1928869812632⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1341843893150,1341843920271⟩,⟨-8681731675106,-8681731607011⟩,⟨-3957137550424,-3957137519380⟩,⟨52434393515479,52434393524690⟩,⟨33797298898679,33797298980571⟩,⟨10893459529338,10893459531325⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1341843920271,-1341843893150⟩,⟨8681731607011,8681731675106⟩,⟨3957137519380,3957137550424⟩,⟨-52434393524690,-52434393515479⟩,⟨-33797298980571,-33797298898679⟩,⟨-10893459531325,-10893459529338⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-242332292495,-242332265374⟩,⟨8681731607011,8681731675106⟩,⟨3957137519380,3957137550424⟩,⟨-52434393524690,-52434393515479⟩,⟨-33797298980571,-33797298898679⟩,⟨-10893459531325,-10893459529338⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11902545683,-11902544349⟩,⟨456188301345,456188308047⟩,⟨97475675113,97475687494⟩,⟨-4708529338155,-4708529320810⟩,⟨1567179278564,1567179340852⟩,⟨2629114231384,2629114256343⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨436470993114,436471157877⟩,⟨861968318395,861971705430⟩,⟨-72457617712,-72454751413⟩,⟨-18367037578744,-18366939785774⟩,⟨-5551992249184,-5551891623423⟩,⟨-1280546512827,-1280442583033⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99127803250,-99127803248⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4868823689,4868823691⟩,⟨31004344178,31004344183⟩,⟨39631760400,39631760401⟩,⟨-324025838474,-324025838465⟩,⟨252372404139,252372404144⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10687342192,10687342454⟩,⟨14051975102,14051976771⟩,⟨86993946002,86993948090⟩,⟨-920074076826,-920074059250⟩,⟨114381737068,114381750391⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1471852593288,1471852614272⟩,⟨-7332020687761,-7332020313730⟩,⟨-1370654218663,-1370654151707⟩,⟨106837558212227,106837565588844⟩,⟨22523936408705,22523937900627⟩,⟨5032302128409,5032302412304⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14306526573,14306527129⟩,⟨-52457271501,-52457263613⟩,⟨103130891149,103130896584⟩,⟨-380589572622,-380589402552⟩,⟨-225579930076,-225579843732⟩,⟨-167979405011,-167979385250⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14306527129,-14306526573⟩,⟨52457263613,52457271501⟩,⟨-103130896584,-103130891149⟩,⟨380589402552,380589572622⟩,⟨225579843732,225579930076⟩,⟨167979385250,167979405011⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113434330379,-113434329821⟩,⟨-826722541879,-826722533989⟩,⟨-103130896584,-103130891149⟩,⟨2579612658104,2579612828174⟩,⟨225579843732,225579930076⟩,⟨167979385250,167979405011⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨93967914581,93967916486⟩,⟨-607972525467,-607972520676⟩,⟨594904551154,594904566629⟩,⟨3671925353018,3671925353767⟩,⟨-3275172988350,-3275172949178⟩,⟨-2392057108436,-2392057108157⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨125789409832,125789414176⟩,⟨-1440476497625,-1440476434937⟩,⟨679223635619,679223675787⟩,⟨22154535273238,22154536637394⟩,⟨-5668495871574,-5668495241533⟩,⟨-4255250569165,-4255250379117⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-125789414176,-125789409832⟩,⟨1440476434937,1440476497625⟩,⟨-679223675787,-679223635619⟩,⟨-22154536637394,-22154535273238⟩,⟨5668495241533,5668495871574⟩,⟨4255250379117,4255250569165⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨973722213600,973722217944⟩,⟨1440476434937,1440476497625⟩,⟨-679223675787,-679223635619⟩,⟨-22154536637394,-22154535273238⟩,⟨5668495241533,5668495871574⟩,⟨4255250379117,4255250569165⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123680137818,123680138373⟩,⟨782010852762,782010863409⟩,⟨186771257171,186771263499⟩,⟨-2539971707044,-2539971449868⟩,⟨-659827596971,-659827468523⟩,⟨-151720904660,-151720856580⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11702784087,11702784203⟩,⟨170582491756,170582494226⟩,⟨21279599460,21279600688⟩,⟨710958364659,710958426102⟩,⟨108542960056,108542987758⟩,⟨-15313436264,-15313429974⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170449530226,170449684830⟩,⟨1683624547191,1683630100011⟩,⟨104761280307,104763896245⟩,⟨-2059424032443,-2059208220904⟩,⟨526019777265,526151073259⟩,⟨-531064316228,-530971640714⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170449684830,-170449530226⟩,⟨-1683630100011,-1683624547191⟩,⟨-104763896245,-104761280307⟩,⟨2059208220904,2059424032443⟩,⟨-526151073259,-526019777265⟩,⟨530971640714,531064316228⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58555864062,58556078041⟩,⟨-87326285389,-87319083212⟩,⟨137210942544,137214378881⟩,⟨-1751094952467,-1750824869305⟩,⟨-1820495737956,-1820326832683⟩,⟨401992263995,402114848636⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27864909615693,27864935176874⟩,⟨-241518004194808,-241517366120887⟩,⟨-83948400488542,-83947975648448⟩,⟨3362267508554296,3362290192436639⟩,⟨1294713453156641,1294730911994926⟩,⟨304255354680682,304270543962401⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13912337172,13912337298⟩,⟨175931218190,175931221376⟩,⟨42018463912,42018465528⟩,⟨540961849122,540961939835⟩,⟨117233105984,117233148170⟩,⟨29319635399,29319650672⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352580189283,352580515908⟩,⟨1402647790696,1402660062799⟩,⟨2657758043,2664161041⟩,⟨-21036851332414,-21036343454198⟩,⟨-3308905943880,-3308588130245⟩,⟨-1823422165268,-1823196150965⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352580515908,-352580189283⟩,⟨-1402660062799,-1402647790696⟩,⟨-2664161041,-2657758043⟩,⟨21036343454198,21036851332414⟩,⟨3308588130245,3308905943880⟩,⟨1823196150965,1823422165268⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83890477206,83890968594⟩,⟨-540691744404,-540676085266⟩,⟨-75121778753,-75112509456⟩,⟨2669305875454,2669911546640⟩,⟨-2243404118939,-2242985679543⟩,⟨542649638138,542979582235⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238785446626,238785446631⟩,⟨1555611412180,1555611412189⟩,⟨308317857691,308317857696⟩,⟨-3890928397846,-3890928397841⟩,⟨-1542342385340,-1542342385332⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1652157770886,-1652156280576⟩,⟨-4278200381296,-4278157633036⟩,⟨486619800732,486643705145⟩,⟨44748023451881,44749586617936⟩,⟨-8042432038134,-8041366389568⟩,⟨1815235038619,1816091889356⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185845330377,-185845161903⟩,⟨-1656311487791,-1656305601072⟩,⟨-225909743995,-225906792161⟩,⟨2764566618648,2764807196349⟩,⟨-293815843626,-293670588679⟩,⟨597490970663,597595760321⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52940116249,52940284728⟩,⟨-100700075611,-100694188883⟩,⟨82408113696,82411065535⟩,⟨-1126361779198,-1126121201492⟩,⟨-1836158228966,-1836012974011⟩,⟨245990763271,246095552932⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4467692069,4467734565⟩,⟨-35458174032,-35456646318⟩,⟨6468194176,6469025955⟩,⟨94428415177,94492150545⟩,⟨-319887498206,-319846204172⟩,⟨40820909707,40850902672⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2549000699,2549016924⟩,⟨-9697197448,-9696599708⟩,⟨7935696192,7936005704⟩,⟨-90022865377,-89997196643⟩,⟨-191913459236,-191897485718⟩,⟨36041231952,36052283333⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4435281107,4435309429⟩,⟨-34475966160,-34474813700⟩,⟨5784823668,5785413572⟩,⟨62541714518,62595179841⟩,⟨-299284520043,-299252325273⟩,⟨30465671418,30486963387⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4435309429,-4435281107⟩,⟨34474813700,34475966160⟩,⟨-5785413572,-5784823668⟩,⟨-62595179841,-62541714518⟩,⟨299252325273,299284520043⟩,⟨-30486963387,-30465671418⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨32382640,32453458⟩,⟨-983360332,-980680158⟩,⟨682780604,684202287⟩,⟨31833235336,31950436027⟩,⟨-20635172933,-20561684129⟩,⟨10333946320,10385231254⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58555864062,58556078041⟩,⟨-87326285389,-87319083212⟩,⟨137210942544,137214378881⟩,⟨-1751094952467,-1750824869305⟩,⟨-1820495737956,-1820326832683⟩,⟨401992263995,402114848636⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨32382640,32453458⟩,⟨-983360332,-980680158⟩,⟨682780604,684202287⟩,⟨31833235336,31950436027⟩,⟨-20635172933,-20561684129⟩,⟨10333946320,10385231254⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨133143986176,137009456743⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110380659508,-109951162777⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439375154380,439804651111⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨53205585100,54803782698⟩,⟨-137009456743,-133143986176⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163156747877,165184442206⟩,⟨962502171033,966367641600⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52776088369,55233279429⟩,⟨-137009456743,-133143986176⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2097769269760,-2084188834112⟩,⟨6406670717152,6512341490447⟩,⟨2924598011441,2963838971657⟩,⟨-38572208439463,-37330600824154⟩,⟨-24964238070048,-24359786559119⟩,⟨-7989312007256,-7779156957008⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-315157055141,-309273193247⟩,⟨-893055387596,-846101812495⟩,⟨-405126030642,-387590901866⟩,⟨5421807339169,5907980037657⟩,⟨3454033492479,3692888917407⟩,⟨1137124270848,1216720538130⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309273193247,315157055141⟩,⟨846101812495,893055387596⟩,⟨387590901866,405126030642⟩,⟨-5907980037657,-5421807339169⟩,⟨-3692888917407,-3454033492479⟩,⟨-1216720538130,-1137124270848⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-165184442206,-163156747877⟩,⟨-966367641600,-962502171033⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨934327185570,936354879899⟩,⟨-966367641600,-962502171033⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-178994668736,-176611073472⟩,⟨-1137216678543,-1130214998104⟩,⟨-517559946147,-515934825104⟩,⟨-1176214731420,-1161775746311⟩,⟨755789507234,763557791078⟩,⟨-243624797673,-242097252116⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152433614446,-150078019230⟩,⟨-813861192739,-803098321177⟩,⟨-370183682702,-366825811617⟩,⟨977083232322,1011776599581⟩,⟨1366538292258,1383415568830⟩,⟨204871520231,208322034165⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150078019230,152433614446⟩,⟨803098321177,813861192739⟩,⟨366825811617,370183682702⟩,⟨-1011776599581,-977083232322⟩,⟨-1383415568830,-1366538292258⟩,⟨-208322034165,-204871520231⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨459351212477,467590669587⟩,⟨1649200133672,1706916580335⟩,⟨754416713483,775309713344⟩,⟨-6919756637238,-6398890571491⟩,⟨-5076304486237,-4820571784737⟩,⟨-1425042572295,-1341995791079⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨816309809303,826441727050⟩,⟨4055537993146,4127546287437⟩,⟨754416713483,775309713344⟩,⟨-19223542329011,-18486110478548⟩,⟨-5076304486237,-4820571784737⟩,⟨-1425042572295,-1341995791079⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨105552176738,110466558858⟩,⟨-274018913486,-266287972352⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10943817134456,11453348068941⟩,⟨26380896668206,29733484335606⟩,⟨-95445416801154,-87056959004921⟩,⟨127186282531605,154379328282726⟩,⟨-277707336584050,-181101190350976⟩,⟨1385058616764142,1590771106144895⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8125012098457,8608844617448⟩,⟨59952118051381,65344662694965⟩,⟨-64232041535996,-56557435160034⟩,⟨88791190218656,155277641030088⟩,⟨-601815190250906,-482578143283611⟩,⟨878859199702179,1062870627696807⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨96792602624,102486577920⟩,⟨-814495229269,-666098679949⟩,⟨628382017615,800626849074⟩,⟨7163810586702,11898642368817⟩,⟨-7304072903101,-1082666713896⟩,⟨-5150262818585,2685528306513⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1196304230400,1201998205696⟩,⟨-814495229269,-666098679949⟩,⟨628382017615,800626849074⟩,⟨7163810586702,11898642368817⟩,⟨-7304072903101,-1082666713896⟩,⟨-5150262818585,2685528306513⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨92766774528,97987637248⟩,⟨-748594673991,-609304772984⟩,⟨574803965412,735848380117⟩,⟨6043323638335,10598274915600⟩,⟨-6394569583103,-489357619462⟩,⟨-5226023336070,2167746363354⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨100933252550,107121162867⟩,⟨-890959125170,-719142648067⟩,⟨678422464641,875788797043⟩,⟨7917998523786,13755635214192⟩,⟨-8731749404700,-1320230161997⟩,⟨-5515121126014,3680775764782⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-102486577920,-96792602624⟩,⟨666098679949,814495229269⟩,⟨-800626849074,-628382017615⟩,⟨-11898642368817,-7163810586702⟩,⟨1082666713896,7304072903101⟩,⟨-2685528306513,5150262818585⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨997025049856,1002719025152⟩,⟨666098679949,814495229269⟩,⟨-800626849074,-628382017615⟩,⟨-11898642368817,-7163810586702⟩,⟨1082666713896,7304072903101⟩,⟨-2685528306513,5150262818585⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-107582254656,-101320844416⟩,⟨730397275287,898219132488⟩,⟨-882925188484,-689039818455⟩,⟨-13855510289853,-8340531585009⟩,⟨1644900628259,8776160079604⟩,⟨-3670583012822,5247864452403⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-98111534965,-91876627225⟩,⟨582621529825,757765276089⟩,⟨-747293313579,-546476001351⟩,⟨-11090657709366,-5068109885074⟩,⟨-531197845553,7068946567340⟩,⟨-3063796469884,6334481387285⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2821717585,15244535642⟩,⟨-308337595345,38622628022⟩,⟨-68870848938,329312795692⟩,⟨-3172659185580,8687525329118⟩,⟨-9262947250253,5748716405343⟩,⟨-8578917595898,10015257152067⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1410858792,7622267821⟩,⟨-154168797673,19311314011⟩,⟨-34435424469,164656397846⟩,⟨-1586329592790,4343762664559⟩,⟨-4631473625127,2874358202672⟩,⟨-4289458797949,5007628576034⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7622267821,-1410858792⟩,⟨-19311314011,154168797673⟩,⟨-164656397846,34435424469⟩,⟨-4343762664559,1586329592790⟩,⟨-2874358202672,4631473625127⟩,⟨-5007628576034,4289458797949⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754501115795,760712544088⟩,⟨-19311314011,154168797673⟩,⟨-164656397846,34435424469⟩,⟨-4343762664559,1586329592790⟩,⟨-2874358202672,4631473625127⟩,⟨-5007628576034,4289458797949⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8520881167,9552876376⟩,⟨-151839829014,-117276476588⟩,⟨110635903050,149254457852⟩,⟨2068357067077,3424890777346⟩,⟨-2547815139612,-951983677530⟩,⟨-241868932070,1666619859862⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9552876376,-8520881167⟩,⟨117276476588,151839829014⟩,⟨-149254457852,-110635903050⟩,⟨-3424890777346,-2068357067077⟩,⟨951983677530,2547815139612⟩,⟨-1666619859862,241868932070⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1089958751400,1090990746609⟩,⟨117276476588,151839829014⟩,⟨-149254457852,-110635903050⟩,⟨-3424890777346,-2068357067077⟩,⟨951983677530,2547815139612⟩,⟨-1666619859862,241868932070⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9594617408,-8554069824⟩,⟨118192432038,153170619848⟩,⟨-150562589360,-111499994139⟩,⟨-3476245894092,-2097216538952⟩,⟨971404617906,2591119861761⟩,⟨-1701844267287,232681713119⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4797308704,-4277034912⟩,⟨59096216019,76585309924⟩,⟨-75281294680,-55749997069⟩,⟨-1738122947046,-1048608269476⟩,⟨485702308953,1295559930881⟩,⟨-850922133644,116340856560⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4277034912,4797308704⟩,⟨-76585309924,-59096216019⟩,⟨55749997069,75281294680⟩,⟨1048608269476,1738122947046⟩,⟨-1295559930881,-485702308953⟩,⟨-116340856560,850922133644⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766400418528,766920711584⟩,⟨-76585309924,-59096216019⟩,⟨55749997069,75281294680⟩,⟨1048608269476,1738122947046⟩,⟨-1295559930881,-485702308953⟩,⟨-116340856560,850922133644⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272489687850,272747686653⟩,⟨29319119147,37959957254⟩,⟨-37313614463,-27658975762⟩,⟨-856222694337,-517089266769⟩,⟨237995919382,636953784903⟩,⟨-416654964966,60467233018⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532800837056,1533841423168⟩,⟨-153170619848,-118192432038⟩,⟨111499994138,150562589360⟩,⟨2097216538952,3476245894092⟩,⟨-2591119861762,-971404617906⟩,⟨-232681713120,1701844267288⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1205647633375,1212533044972⟩,⟨-990549214992,-800902622699⟩,⟨755552924986,973683170082⟩,⟨9677677789972,16088956124779⟩,⟨-10473709114042,-2305591212773⟩,⟨-5316520561617,4829773928421⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1311783638974,1325554462168⟩,⟨-1981098429984,-1601805245397⟩,⟨1511105849971,1947366340164⟩,⟨19355355579945,32177912249551⟩,⟨-20947418228080,-4611182425546⟩,⟨-10628137070491,9659547856839⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨194087618944,205569891840⟩,⟨-1660518316299,-1328654191895⟩,⟨1253421492863,1632244732238⟩,⟨13546975820831,25365351565631⟩,⟨-16043080580473,-1359782066517⟩,⟨-11331395132137,6667570147994⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨66420513285,70906776659⟩,⟨-565319977335,-442716522916⟩,⟨415857232553,557134677400⟩,⟨4282616109601,8408716844553⟩,⟨-5360917986463,-77003125516⟩,⟨-4269841987186,2307994577112⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379870854545,380488654502⟩,⟨2877130230,23663538693⟩,⟨-24420450168,-1209721863⟩,⟨-685275750897,135162344051⟩,⟨-305029462168,658218648581⟩,⟨-649181049302,500907192350⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177297943868,3182465317227⟩,⟨-198247352416,-24025683435⟩,⟨10101869641,204588572040⟩,⟨-1131993785334,5765772107945⟩,⟨-5539884342967,2555309621845⟩,⟨-4196413982571,5464984847413⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨191937724858,205235080534⟩,⟨-1649066963861,-1280785087331⟩,⟨1202327713417,1625784083477⟩,⟨12321974702860,24914178004881⟩,⟨-16079738437734,-70882945280⟩,⟨-12621764064702,7240108907531⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨386025343802,410804972374⟩,⟨-3309585280160,-2609439279226⟩,⟨2455749206280,3258028815715⟩,⟨25868950523691,50279529570512⟩,⟨-32122819018207,-1430665011797⟩,⟨-23953159196839,13907679055525⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517749807600,526309645223⟩,⟨-26721607012,213327690830⟩,⟨-227839677438,47649262988⟩,⟨-6016001770213,2238282538146⟩,⟨-4023504916152,6418356774222⟩,⟨-6939509852373,5984760435787⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355287563740,364134711341⟩,⟨-27731578011,221390633328⟩,⟨-236451115601,49450216564⟩,⟨-6249003013021,2367748599119⟩,⟨-4223497530872,6670967022960⟩,⟨-7212499372865,6262140592444⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨710575127480,728269422682⟩,⟨-55463156022,442781266656⟩,⟨-472902231202,98900433128⟩,⟨-12498006026042,4735497198238⟩,⟨-8446995061744,13341934045920⟩,⟨-14424998745730,12524281184888⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523247960680,1525320542001⟩,⟨-35894143260,33647396976⟩,⟨-37754463714,39926686310⟩,⟨-1327674238394,1407888827015⟩,⟨-1639136184232,1576410521706⟩,⟨-1899301572982,1943713199358⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨984420797834,1010307014920⟩,⟨-100717168785,636544184104⟩,⟨-681050468396,163647425372⟩,⟨-18246424938404,7529043078119⟩,⟨-12833640309344,19584541278156⟩,⟨-21303742872385,18694480418090⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67530554574,67658493731⟩,⟨14532193062,18832889558⟩,⟨-18512222644,-13709333272⟩,⟨-423229991418,-253677234535⟩,⟨115387612044,314533707810⟩,⟨-205321446425,32531904705⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50136672258,50855126037⟩,⟨259874924740,268144367861⟩,⟨32420671948,37530502734⟩,⟨-1393836210837,-1182333344992⟩,⟨-286226897691,-96942590087⟩,⟨-268126183793,-76784178236⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136838162259,2139740455665⟩,⟨-427352354628,-329538049774⟩,⟨310878539214,420075841868⟩,⟨5872761389372,9741545342442⟩,⟨-7271280522224,-2732391780092⟩,⟨-626577459670,4789450624708⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2978911037429,2984982116439⟩,⟨-894248037844,-689100759521⟩,⟨650081645012,879021709528⟩,⟨12333733789560,20473785657887⟩,⟨-15303159500323,-5763862507101⟩,⟨-1263854780266,10108358950050⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135835476948,138062788892⟩,⟨662718944099,696542814474⟩,⟨117480547381,142545686058⟩,⟨-3657786640823,-2582081758435⟩,⟨-1361739064908,-331420438751⟩,⟨-748035008848,319513570259⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8756347958176,8899926932030⟩,⟨-45637415888211,-42031583742269⟩,⟨-9339579165155,-7450961692434⟩,⟨567277110326577,707700699495990⟩,⟨92550785880575,185004773849996⟩,⟨-8254135512526,68613079365825⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7839781613347,8177865867497⟩,⟨-42750049813248,-32479482319337⟩,⟨-14094568316711,-5346402327150⟩,⟨307361072824038,719588440066040⟩,⟨-33217514063558,357644827659408⟩,⟨-182806399718411,225937796751100⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15679563226694,16355731734994⟩,⟨-85500099626496,-64958964638674⟩,⟨-28189136633422,-10692804654300⟩,⟨614722145648076,1439176880132080⟩,⟨-66435028127116,715289655318816⟩,⟨-365612799436822,451875593502200⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10952333724070,10995116277821⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨2173453475238562,2199023255588622⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9852822096294,9895604650045⟩,⟨-109951162778820,-109097176394608⟩,⟨0,0⟩,⟨2173453475238575,2199023255588602⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2411110045440,2415874025920⟩,⟨-12269843176037,-12121908488212⟩,⟨0,0⟩,⟨104571265817406,111755106875729⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7318642140081,7409597429130⟩,⟨-43886601602233,-42644506073135⟩,⟨-19973280018111,-19466903040056⟩,⟨496964836759082,519875423358658⟩,⟨275575619612328,286534281609648⟩,⟨103560279821731,107679781121031⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6219130512305,6310085801354⟩,⟨-43886601602234,-42644506073134⟩,⟨-19973280018112,-19466903040056⟩,⟨496964836759081,519875423358659⟩,⟨275575619612327,286534281609650⟩,⟨103560279821730,107679781121032⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1905194165440,1921158196096⟩,⟨-7758934897707,-7430664457513⟩,⟨-3531177482339,-3392043614470⟩,⟨31841927947675,41693868327213⟩,⟨23099646234476,27733909597981⟩,⟨6704352569667,8572645123142⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨98913096826,99342593558⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138644995832,140672690162⟩,⟨672719620272,680142268666⟩,⟨307292125787,309342985915⟩,⟨-1698693120000,-1685130754127⟩,⟨-1546292245304,-1538392525366⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4316304210880,4337032222016⟩,⟨-20028778073744,-19552572945725⟩,⟨-3531177482339,-3392043614470⟩,⟨136413193765081,153448975202942⟩,⟨23099646234476,27733909597981⟩,⟨6704352569667,8572645123142⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨772050687604,821609944748⟩,⟨-6619170560320,-5218878558452⟩,⟨4911498412560,6516057631430⟩,⟨51737901047382,100559059141024⟩,⟨-64245638036414,-2861330023594⟩,⟨-47906318393678,27815358111050⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5088354898484,5158642166764⟩,⟨-26647948634064,-24771451504177⟩,⟨1380320930221,3124014016960⟩,⟨188151094812463,254008034343966⟩,⟨-41145991801938,24872579574387⟩,⟨-41201965824011,36388003234192⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457753176996,466091380153⟩,⟨1659024844970,1898450732886⟩,⟨124174964932,282259547709⟩,⟨-36027753267260,-26822304019720⟩,⟨-2614426281527,4746487641558⟩,⟨-3722661990328,3287712948515⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨39719297440,41854657993⟩,⟨-839637151430,-796691276886⟩,⟨330673852191,333275037186⟩,⟨9853172814857,10607092164104⟩,⟨-6692236630045,-6625935308195⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497472474436,507946038146⟩,⟨819387693540,1101759456000⟩,⟨454848817123,615534584895⟩,⟨-26174580452403,-16215211855616⟩,⟨-9306662911572,-1879447666637⟩,⟨-3722661990328,3287712948515⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500409295618,501398026980⟩,⟨2510857612204,2551553037358⟩,⟨0,0⟩,⟨1957166706152,4308831445771⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226409475109,231632967679⟩,⟨1508953362518,1681174829984⟩,⟨207010613111,280695372935⟩,⟨-7308258115090,-275752889371⟩,⟨-3205315630799,573050835261⟩,⟨-1697604036112,1499259074683⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-821609944748,-772050687604⟩,⟨5218878558452,6619170560320⟩,⟨-6516057631430,-4911498412560⟩,⟨-100559059141024,-51737901047382⟩,⟨2861330023594,64245638036414⟩,⟨-27815358111050,47906318393678⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3494694266132,3564981534412⟩,⟨-14809899515292,-12933402385405⟩,⟨-10047235113769,-8303542027030⟩,⟨35854134624057,101711074155560⟩,⟨25960976258070,91979547634395⟩,⟨-21111005541383,56478963516820⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨440670075442,456107539161⟩,⟨243381686080,574385111350⟩,⟨-308754863117,-44058212679⟩,⟨-19309018689468,-8169220970074⟩,⟨-12121774195731,-1816706102405⟩,⟨-9495253589258,1468502616635⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨326313495754,330368884412⟩,⟨1925004342066,1932735283200⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-330368884412,-326313495754⟩,⟨-1932735283200,-1925004342066⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨769142743364,773198132022⟩,⟨-1932735283200,-1925004342066⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1332742856036,1350996106831⟩,⟨-8833271021641,-8533560218728⟩,⟨-4020119789411,-3895507409080⟩,⟨48293359674034,56597451094671⟩,⟨31846765454547,35759641167127⟩,⟨10111873848471,11678336084721⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1350996106831,-1332742856036⟩,⟨8533560218728,8833271021641⟩,⟨3895507409080,4020119789411⟩,⟨-56597451094671,-48293359674034⟩,⟨-35759641167127,-31846765454547⟩,⟨-11678336084721,-10111873848471⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-251484479055,-233231228260⟩,⟨8533560218728,8833271021641⟩,⟨3895507409080,4020119789411⟩,⟨-56597451094671,-48293359674034⟩,⟨-35759641167127,-31846765454547⟩,⟨-11678336084721,-10111873848471⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12633165629,-11194999308⟩,⟨437850088598,475071172756⟩,⟨86388899664,108746819701⟩,⟨-5044554344895,-4384782246580⟩,⟨1346014055063,1784440152051⟩,⟨2526708647812,2730730207087⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428036909813,444912539853⟩,⟨681231774678,1049456284106⟩,⟨-222365963453,64688607022⟩,⟨-24353573034363,-12554003216654⟩,⟨-10775760140668,-32265950354⟩,⟨-6968544941446,4199232823722⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99342593558,-98913096826⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4747786387,4990413099⟩,⟨29800620881,32208865726⟩,⟨39526600801,39737037424⟩,⟨-329681689648,-318374517140⟩,⟨251814268106,252930624064⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10411381891,10965058559⟩,⟨9659734367,18426662799⟩,⟨86677559241,87311197222⟩,⟨-991697435162,-848024361110⟩,⟨108761645553,119972071186⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1462808302201,1480964464518⟩,⟨-7488271374040,-7178333876530⟩,⟨-1406581326567,-1335323466471⟩,⟨103172001872713,110602317234236⟩,⟨21637923093165,23433854894421⟩,⟨4813241074999,5257207118279⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13851473220,14769159023⟩,⟨-61826535325,-43152924740⟩,⟨101289885294,104957705738⟩,⟨-609791870546,-151356096061⟩,⟨-268619642039,-182327643843⟩,⟨-177813588617,-158106171359⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14769159023,-13851473220⟩,⟨43152924740,61826535325⟩,⟨-104957705738,-101289885294⟩,⟨151356096061,609791870546⟩,⟨182327643843,268619642039⟩,⟨158106171359,177813588617⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114111752581,-112764570046⟩,⟨-836456377482,-816923773435⟩,⟨-104957705738,-101289885294⟩,⟨2350379351613,2808815126098⟩,⟨182327643843,268619642039⟩,⟨158106171359,177813588617⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨91448505950,96508181262⟩,⟨-629159567363,-587375825194⟩,⟨583946955855,605646634190⟩,⟨3328012985388,4028137473390⟩,⟨-3505203723770,-3041343911022⟩,⟨-2503135926954,-2280343387620⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨121664592122,129989700313⟩,⟨-1504706608905,-1378490325646⟩,⟨653431788528,704701785546⟩,⟨20678207893504,23703425624171⟩,⟨-6333026292522,-4996897153884⟩,⟨-4520801799019,-3990733501661⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-129989700313,-121664592122⟩,⟨1378490325646,1504706608905⟩,⟨-704701785546,-653431788528⟩,⟨-23703425624171,-20678207893504⟩,⟨4996897153884,6333026292522⟩,⟨3990733501661,4520801799019⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨969521927463,977847035654⟩,⟨1378490325646,1504706608905⟩,⟨-704701785546,-653431788528⟩,⟨-23703425624171,-20678207893504⟩,⟨4996897153884,6333026292522⟩,⟨3990733501661,4520801799019⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122253699002,125106792505⟩,⟨767010722794,797396049001⟩,⟨180802233582,192717447300⟩,⟨-2856551603739,-2231783701663⟩,⟨-795753978185,-522711516421⟩,⟨-206221756183,-96488123118⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11564996618,11842978054⟩,⟨167565409486,173621634882⟩,⟨20776333922,21785868284⟩,⟨630908534527,790568727829⟩,⟨94757446592,122295103148⟩,⟨-18246245177,-12392146237⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164922399279,176169643960⟩,⟨1468630788759,1899442101755⟩,⟨-7348248948,211604463042⟩,⟨-11539399899127,7462148658983⟩,⟨-5509692620789,6666625503181⟩,⟨-5326569122872,4286389172583⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176169643960,-164922399279⟩,⟨-1899442101755,-1468630788759⟩,⟨-211604463042,7348248948⟩,⟨-7462148658983,11539399899127⟩,⟨-6666625503181,5509692620789⟩,⟨-4286389172583,5326569122872⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50239831149,66710568400⟩,⟨-390488739237,212544041225⟩,⟨-4593849931,288043621883⟩,⟨-14770406774073,11263647009756⟩,⟨-9871941133980,6082743456050⟩,⟨-5983993208695,6825828197555⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27168982684220,28578095294353⟩,⟨-264810546378291,-218523394869905⟩,⟨-101782263749518,-66900275997202⟩,⟨2397254417924844,4341563542539521⟩,⟨485996178717400,2135881615454941⟩,⟨-477246236849829,1098140340235612⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13593277726,14235146893⟩,⟨170566450898,181461768166⟩,⟨40206472190,43856310534⟩,⟨420061842508,660287052711⟩,⟨71164366142,163288340734⟩,⟨12532300764,46100439310⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨335890515234,369994617757⟩,⟨786258100966,2014878652367⟩,⟨-324249894087,312807778868⟩,⟨-47390842102219,5572493396415⟩,⟨-19593661490987,13527879549995⟩,⟨-13988728419413,10522856998548⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-369994617757,-335890515234⟩,⟨-2014878652367,-786258100966⟩,⟨-312807778868,324249894087⟩,⟨-5572493396415,47390842102219⟩,⟨-13527879549995,19593661490987⟩,⟨-10522856998548,13988728419413⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58042292056,109022024619⟩,⟨-1333646877689,263198183140⟩,⟨-535173742321,388938501109⟩,⟨-29926066430778,34836838885565⟩,⟨-24303639690663,19561395540633⟩,⟨-17491401939994,18187961243135⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237558092658,240015283720⟩,⟨1551469929032,1559751570888⟩,⟨307292125787,309342985915⟩,⟨-3897716375552,-3884154009679⟩,⟨-1546292245304,-1538392525366⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1697463824735,-1608076859854⟩,⟨-5780554056408,-2776179592486⟩,⟨-464652256727,1481139974471⟩,⟨-19318603693577,108826093728340⟩,⟨-57706753021211,40497403193695⟩,⟨-42672704056671,45971612853098⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-193144164320,-178800605132⟩,⟨-1888781775111,-1430462742846⟩,⟨-350393792048,-95900046812⟩,⟨-7318513551736,12919424540414⟩,⟨-7151786101378,6454119559038⟩,⟨-4877236285763,6068419708095⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44413928338,61214678588⟩,⟨-337311846079,129288828042⟩,⟨-43101666261,213442939103⟩,⟨-11216229927288,9035270530735⟩,⟨-8698078346682,4915727033672⟩,⟨-5229080006653,5717262846431⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2652118339,6614683326⟩,⟨-119635127884,37043793869⟩,⟨-32926050484,52158982106⟩,⟨-3795868857590,4177781284513⟩,⟨-2940935891458,2048997612190⟩,⟨-1935000169941,1984114852771⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1794066547,3408092084⟩,⟨-37559286724,14396162540⟩,⟨-4799321046,23766626172⟩,⟨-1328241638900,1213030305736⟩,⟨-1099482510012,597557005392⟩,⟨-598986295237,719479968759⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3108693925,5954902045⟩,⟨-89676628828,13029602207⟩,⟨-19331157991,35992249368⟩,⟨-2472037112144,2778833529708⟩,⟨-2097364488890,1284558842041⟩,⟨-1188316424414,1314534267030⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5954902045,-3108693925⟩,⟨-13029602207,89676628828⟩,⟨-35992249368,19331157991⟩,⟨-2778833529708,2472037112144⟩,⟨-1284558842041,2097364488890⟩,⟨-1314534267030,1188316424414⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3302783706,3505989401⟩,⟨-132664730091,126720422697⟩,⟨-68918299852,71490140097⟩,⟨-6574702387298,6649818396657⟩,⟨-4225494733499,4146362101080⟩,⟨-3249534436971,3172431277185⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50239831149,66710568400⟩,⟨-390488739237,212544041225⟩,⟨-4593849931,288043621883⟩,⟨-14770406774073,11263647009756⟩,⟨-9871941133980,6082743456050⟩,⟨-5983993208695,6825828197555⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3302783706,3505989401⟩,⟨-132664730091,126720422697⟩,⟨-68918299852,71490140097⟩,⟨-6574702387298,6649818396657⟩,⟨-4225494733499,4146362101080⟩,⟨-3249534436971,3172431277185⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (513/5120) u, BivariateJet2.affineZ (629/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000020

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000021Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2080658680256,-2080658641536⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2080658680192,-2080658641536⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-179619970176,-179619970112⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-179619970176,-179619970112⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨97643996416,97643996480⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-107168109312,-107168109248⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨97644118400,97644118464⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-107168256320,-107168256256⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-9524137856,-9524137792⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-9524112896,-9524112832⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨204812105664,204812105728⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨204812374720,204812374784⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1901038671360,1901038709952⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1901038671424,1901038710016⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2531719137984,-2531719080128⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-115845112128,-115845112064⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2087408666112,-2087408627392⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2073944901568,-2073944862912⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-180815722624,-180815722560⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-178426404672,-178426404608⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨95045948416,95045948480⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-104046231488,-104046231424⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨100263775168,100263775232⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-110332611200,-110332611136⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-10068836032,-10068835968⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-9000283008,-9000282944⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨199092179904,199092179968⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨210596386368,210596386432⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2415873968064,2415874025920⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1893129140288,1893129178880⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1908982222720,1908982261312⟩



end LaneCBRB2Cell000021Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000021
open Set LaneCBRB2Cell000021Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨138942192025,138942192026⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110165911143,-110165911142⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439589902745,439589902746⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨55549739663,55549739664⟩,⟨-138942192026,-138942192025⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨165715650805,165715650807⟩,⟨960569435750,960569435751⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨55549739662,55549739665⟩,⟨-138942192026,-138942192025⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2080658680256,-2080658641536⟩,⟨6373310298393,6373310298478⟩,⟨2916647927744,2916647927787⟩,⟨-36942841835013,-36942841834032⟩,⟨-24201508152131,-24201508151572⟩,⟨-7736921483830,-7736921483604⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313591687979,-313591682138⟩,⟨-857162258948,-857162225093⟩,⟨-392267190716,-392267175220⟩,⟨5567933000769,5567933001147⟩,⟨3529226345861,3529226384792⟩,⟨1166089513263,1166089513352⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨313591682138,313591687979⟩,⟨857162225093,857162258948⟩,⟨392267175220,392267190716⟩,⟨-5567933001147,-5567933000769⟩,⟨-3529226384792,-3529226345861⟩,⟨-1166089513352,-1166089513263⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-165715650807,-165715650805⟩,⟨-960569435751,-960569435750⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨933795976969,933795976971⟩,⟨-960569435751,-960569435750⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-179619970176,-179619970112⟩,⟨-1131036425455,-1131036425450⟩,⟨-517601511940,-517601511937⟩,⟨-1163465090672,-1163465090662⟩,⟨762193931970,762193931979⟩,⟨-243663930781,-243663930777⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152548096170,-152548096115⟩,⟨-803647536084,-803647536020⟩,⟨-367776996729,-367776996697⟩,⟨988110533396,988110533420⟩,⟨1372085322220,1372085322302⟩,⟨206939510725,206939510734⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨152548096115,152548096170⟩,⟨803647536020,803647536084⟩,⟨367776996697,367776996729⟩,⟨-988110533420,-988110533396⟩,⟨-1372085322302,-1372085322220⟩,⟨-206939510734,-206939510725⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨466139778253,466139784149⟩,⟨1660809761113,1660809795032⟩,⟨760044171917,760044187445⟩,⟨-6556043534567,-6556043534165⟩,⟨-4901311707094,-4901311668081⟩,⟨-1373029024086,-1373029023988⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨824043904580,824043916335⟩,⟨4074299704780,4074299796645⟩,⟨760044171917,760044187445⟩,⟨-18751671602780,-18751671601858⟩,⟨-4901311707094,-4901311668081⟩,⟨-1373029024086,-1373029023988⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨111099479324,111099479330⟩,⟨-277884384052,-277884384050⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10881471514585,10881471515173⟩,⟨27216968320854,27216968323993⟩,⟨-86109944604486,-86109944594982⟩,⟨136151321737232,136151321761266⟩,⟨-215380027575559,-215380027478360⟩,⟨1362852909776464,1362852910003621⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8155266436419,8155266553196⟩,⟨60720006354487,60720007559155⟩,⟨-57014382928837,-57014381847021⟩,⟨118169790184648,118169796248683⟩,⟨-510197166288970,-510197155908437⟩,⟨888772166190040,888772183377741⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨102110964736,102111098112⟩,⟨-750839983285,-750837975666⟩,⟨705015786723,705017671211⟩,⟨9511952485653,9512001559141⟩,⟨-3994681010505,-3994621780530⟩,⟨-1315493527201,-1315424382292⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1201622592512,1201622725888⟩,⟨-750839983285,-750837975666⟩,⟨705015786723,705017671211⟩,⟨9511952485653,9512001559141⟩,⟨-3994681010505,-3994621780530⟩,⟨-1315493527201,-1315424382292⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨97643996416,97644118464⟩,⟨-687035428067,-687033514791⟩,⟨645105188647,645106984602⟩,⟨8274351358399,8274399618864⟩,⟨-3252126603218,-3252069755978⟩,⟨-1582204150651,-1582138640458⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨106712133962,106712279190⟩,⟨-817519769164,-817517333225⟩,⟨767625832100,767628118715⟩,⟨10825837573040,10825901855087⟩,⟨-4789972603958,-4789899570731⟩,⟨-1018674071057,-1018591483987⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-102111098112,-102110964736⟩,⟨750837975666,750839983285⟩,⟨-705017671211,-705015786723⟩,⟨-9512001559141,-9511952485653⟩,⟨3994621780530,3994681010505⟩,⟨1315424382292,1315493527201⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨997400529664,997400663040⟩,⟨750837975666,750839983285⟩,⟨-705017671211,-705015786723⟩,⟨-9512001559141,-9511952485653⟩,⟨3994621780530,3994681010505⟩,⟨1315424382292,1315493527201⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-107168256320,-107168109248⟩,⟨827706573107,827708896946⟩,⟨-777195423734,-777193242387⟩,⟨-11108910535452,-11108851537002⟩,⟨4988646470221,4988715637588⟩,⟨900729121295,900808622772⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-97215606648,-97215460234⟩,⟨677654281970,677656786516⟩,⟨-636300703347,-636298352318⟩,⟨-8019660267541,-8019593148730⟩,⟨3074525771191,3074601244989⟩,⟨1685544307825,1685628912266⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨9496527314,9496818956⟩,⟨-139865487194,-139860546709⟩,⟨131325128753,131329766397⟩,⟨2806177305499,2806308706357⟩,⟨-1715446832767,-1715298325742⟩,⟨666870236768,667037428279⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4748263657,4748409478⟩,⟨-69932743597,-69930273354⟩,⟨65662564376,65664883199⟩,⟨1403088652749,1403154353179⟩,⟨-857723416384,-857649162871⟩,⟨333435118384,333518714140⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4748409478,-4748263657⟩,⟨69930273354,69932743597⟩,⟨-65664883199,-65662564376⟩,⟨-1403154353179,-1403088652749⟩,⟨857649162871,857723416384⟩,⟨-333518714140,-333435118384⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757374974138,757375139223⟩,⟨69930273354,69932743597⟩,⟨-65664883199,-65662564376⟩,⟨-1403154353179,-1403088652749⟩,⟨857649162871,857723416384⟩,⟨-333518714140,-333435118384⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨9482982131,9483006905⟩,⟨-139460271748,-139459716692⟩,⟨130948760008,130949281076⟩,⟨2792207506964,2792224413401⟩,⟨-1704860044006,-1704842925172⟩,⟨659785238724,659803234171⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9483006905,-9482982131⟩,⟨139459716692,139460271748⟩,⟨-130949281076,-130948760008⟩,⟨-2792224413401,-2792207506964⟩,⟨1704842925172,1704860044006⟩,⟨-659803234171,-659785238724⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090028620871,1090028645645⟩,⟨139459716692,139460271748⟩,⟨-130949281076,-130948760008⟩,⟨-2792224413401,-2792207506964⟩,⟨1704842925172,1704860044006⟩,⟨-659803234171,-659785238724⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9524137856,-9524112832⟩,⟨140672982055,140673545138⟩,⟨-132088510738,-132087982134⟩,⟨-2834514178407,-2834496916787⟩,⟨1736574153244,1736591595371⟩,⟨-681411670588,-681393376450⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4762068928,-4762056416⟩,⟨70336491027,70336772569⟩,⟨-66044255369,-66043991067⟩,⟨-1417257089204,-1417248458393⟩,⟨868287076622,868295797686⟩,⟨-340705835294,-340696688225⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4762056416,4762068928⟩,⟨-70336772569,-70336491027⟩,⟨66043991067,66044255369⟩,⟨1417248458393,1417257089204⟩,⟨-868295797686,-868287076622⟩,⟨340696688225,340705835294⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766885440032,766885471808⟩,⟨-70336772569,-70336491027⟩,⟨66043991067,66044255369⟩,⟨1417248458393,1417257089204⟩,⟨-868295797686,-868287076622⟩,⟨340696688225,340705835294⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272507155217,272507161412⟩,⟨34864929173,34865067937⟩,⟨-32737320269,-32737190002⟩,⟨-698056103351,-698051876741⟩,⟨426210731293,426215011002⟩,⟨-164950808543,-164946309681⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533770880064,1533770943616⟩,⟨-140673545138,-140672982054⟩,⟨132087982134,132088510738⟩,⟨2834496916786,2834514178408⟩,⟨-1736591595372,-1736574153244⟩,⟨681393376450,681411670588⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1212076414637,1212076576721⟩,⟨-912447436651,-912444752887⟩,⟨856760015005,856762534243⟩,⟨12933026902155,12933097527121⟩,⟨-6144414641685,-6144333950497⟩,⟨-387427486934,-387336071085⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1324641201498,1324641525666⟩,⟨-1824894873302,-1824889505774⟩,⟨1713520030011,1713525068486⟩,⟨25866053804321,25866195054233⟩,⟨-12288829283365,-12288667900997⟩,⟨-774854826942,-774672289097⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨204812105664,204812374784⟩,⟨-1514744619446,-1514739793466⟩,⟨1422298154571,1422302684800⟩,⟨19383188627394,19383324422361⟩,⟨-8240853700840,-8240704766196⟩,⟨-2483021963777,-2482858571436⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨70336945351,70337052556⟩,⟨-510705730630,-510703997095⟩,⟨479536720290,479538347548⟩,⟨6326281923912,6326327056229⟩,⟨-2582321766987,-2582269960802⟩,⟨-1021333320314,-1021274491083⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380135624510,380135648903⟩,⟨13769990463,13770326399⟩,⟨-12929949982,-12929634615⟩,⟨-280166807430,-280156505769⟩,⟨172518810835,172529205054⟩,⟨-69085794559,-69074908600⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3180248479992,3180248684067⟩,⟨-115203784087,-115200958830⟩,⟨108170467436,108173119708⟩,⟨2352160173402,2352247067662⟩,⟨-1451231876464,-1451144348417⟩,⟨585245248539,585336755995⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨203443927184,203444250322⟩,⟨-1484544848062,-1484539547192⟩,⟨1393940971009,1393945946944⟩,⟨18555746841576,18555887333261⟩,⟨-7662483802462,-7662324932022⟩,⟨-2822331373397,-2822152480442⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨408256032848,408256625106⟩,⟨-2999289467508,-2999279340658⟩,⟨2816239125580,2816248631744⟩,⟨37938935468970,37939211755622⟩,⟨-15903337503302,-15903029698218⟩,⟨-5305353337174,-5305011051878⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨521701487241,521701714673⟩,⟨96339934266,96343358416⟩,⟨-90463709158,-90460494894⟩,⟨-1924170611274,-1924079048806⟩,⟨1173193390256,1173296533714⟩,⟨-451631804382,-451515984017⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359362866590,359363101583⟩,⟨99542542406,99546102084⟩,⟨-93470995560,-93467654070⟩,⟨-1978944838568,-1978849146266⟩,⟨1203562903035,1203670352284⟩,⟨-458541989816,-458421642255⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨718725733180,718726203166⟩,⟨199085084812,199092204168⟩,⟨-186941991120,-186935308140⟩,⟨-3957889677136,-3957698292532⟩,⟨2407125806070,2407340704568⟩,⟨-917083979632,-916843284510⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524287873159,1524287961485⟩,⟨-1213828446,-1212710306⟩,⟨1138701058,1139750730⟩,⟨42272503385,42306671444⟩,⟨-31748670200,-31714109238⟩,⟨21590142279,21626431864⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨996392299579,996393008873⟩,⟨275204520399,275215137604⟩,⟨-258419288737,-258409322257⟩,⟨-5459755429291,-5459467015190⟩,⟨3316733883313,3317054997519⟩,⟨-1257657289468,-1257299430808⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67539212654,67539215726⟩,⟨17282114032,17282183210⟩,⟨-16227484992,-16227420050⟩,⟨-343806685023,-343804564476⟩,⟨209191212000,209193354730⟩,⟨-79814622950,-79812375544⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50618179109,50618182134⟩,⟨263222514061,263222583121⟩,⟨34524987011,34525038935⟩,⟨-1281441633724,-1281439472752⟩,⟨-192474976159,-192473061864⟩,⟨-166593298876,-166591519587⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2139543642017,2139543819322⟩,⟨-392466965548,-392465378328⟩,⟨368513975632,368515465664⟩,⟨7943995512463,7944044286728⟩,⟨-4878738925960,-4878689792636⟩,⟨1932764559916,1932815931757⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2984570287255,2984570658254⟩,⟨-821211544580,-821208189399⟩,⟨771091442476,771094592222⟩,⟨16697610949673,16697714301483⟩,⟨-10279166030777,-10279062230469⟩,⟨4110589908280,4110698102337⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137400559982,137400585274⟩,⟨676698490559,676698923560⟩,⟨129215091096,129215390820⟩,⟨-3102898778382,-3102885966580⟩,⟨-836873002405,-836861987651⟩,⟨-214545299419,-214535150540⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8798549272580,8798550892173⟩,⟨-43332937787166,-43332894106604⟩,⟨-8274407268288,-8274385029014⟩,⟨625525014756970,625526690259882⟩,⟨135091849241818,135092860520172⟩,⟨29300813495612,29301549237453⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7973364283921,7973371427556⟩,⟨-37066670968028,-37066518063317⟩,⟨-9566317037900,-9566211411795⟩,⟨501475925396051,501481022022766⟩,⟨157076380200474,157080446822057⟩,⟨20378047090173,20381758712555⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15946728567842,15946742855112⟩,⟨-74133341936056,-74133036126634⟩,⟨-19132634075800,-19132422823590⟩,⟨1002951850792102,1002962044045532⟩,⟨314152760400948,314160893644114⟩,⟨40756094180346,40763517425110⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10973683302499,10973683302600⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨2186188521914400,2186188521974786⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9874171674723,9874171674824⟩,⟨-109522921071186,-109522921069170⟩,⟨0,0⟩,⟨2186188521914418,2186188521974777⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2413489943680,2413490001536⟩,⟨-12195628068220,-12195628067696⟩,⟨0,0⟩,⟨108164909937337,108164909975027⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7295181919917,7295181920006⟩,⟨-42286463267415,-42286463266337⟩,⟨-19351752807607,-19351752807089⟩,⟨490226287762181,490226287781159⟩,⟨272747574999323,272747575009467⟩,⟨102667854158449,102667854162678⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6195670292141,6195670292230⟩,⟨-42286463267415,-42286463266337⟩,⟨-19351752807608,-19351752807089⟩,⟨490226287762187,490226287781159⟩,⟨272747574999325,272747575009469⟩,⟨102667854158449,102667854162679⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1901038671360,1901038710016⟩,⟨-7504346724042,-7504346723734⟩,⟨-3434249439777,-3434249439631⟩,⟨35779376738529,35779376748848⟩,⟨24963702081174,24963702086321⟩,⟨7493257551780,7493257554034⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99127803248,99127803250⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨140739401142,140739401145⟩,⟨671020175570,671020175576⟩,⟨307082114775,307082114779⟩,⟨-1678369955515,-1678369955510⟩,⟨-1536160652332,-1536160652324⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4314528615040,4314528711552⟩,⟨-19699974792262,-19699974791430⟩,⟨-3434249439777,-3434249439631⟩,⟨143944286675866,143944286723875⟩,⟨24963702081174,24963702086321⟩,⟨7493257551780,7493257554034⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨816512065696,816513250212⟩,⟨-5998578935016,-5998558681316⟩,⟨5632478251160,5632497263488⟩,⟨75877870937940,75878423511244⟩,⟨-31806675006604,-31806059396436⟩,⟨-10610706674348,-10610022103756⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5131040680736,5131041961764⟩,⟨-25698553727278,-25698533472746⟩,⟨2198228811383,2198247823857⟩,⟨219822157613806,219822710235119⟩,⟨-6842972925430,-6842357310115⟩,⟨-3117449122568,-3116764549722⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨462595190635,462595306138⟩,⟨1785943977632,1785946828083⟩,⟨198183982419,198185696516⟩,⟨-31541359880420,-31541275104197⟩,⟨1140787849195,1140858553312⟩,⟨-281057403540,-280995685038⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨41950475096,41950477437⟩,⟨-841476272747,-841476260990⟩,⟨331972847757,331972866257⟩,⟨10518791016956,10518791048348⟩,⟨-6658977614141,-6658977521421⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨504545665731,504545783575⟩,⟨944467704885,944470567093⟩,⟨530156830176,530158562773⟩,⟨-21022568863464,-21022484055849⟩,⟨-5518189764946,-5518118968109⟩,⟨-281057403540,-280995685038⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500903595558,500903607567⟩,⟨2531120470889,2531120592376⟩,⟨0,0⟩,⟨3131155626176,3131158552760⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229855448276,229855507474⟩,⟨1591755001113,1591756642394⟩,⟨241523105109,241523900219⟩,⟨-3791998551845,-3791944621398⟩,⟨-1293474592659,-1293438232444⟩,⟨-128041090072,-128012969955⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-816513250212,-816512065696⟩,⟨5998558681316,5998578935016⟩,⟨-5632497263488,-5632478251160⟩,⟨-75878423511244,-75877870937940⟩,⟨31806059396436,31806675006604⟩,⟨10610022103756,10610706674348⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3498015364828,3498016645856⟩,⟨-13701416110946,-13701395856414⟩,⟨-9066746703265,-9066727690791⟩,⟨68065863164622,68066415785935⟩,⟨56769761477610,56770377092925⟩,⟨18103279655536,18103964228382⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨447752052088,447752216072⟩,⟨380996230850,380999605322⟩,⟨-183600191671,-183597400225⟩,⟨-13350718755745,-13350621341205⟩,⟨-6980556553371,-6980458703505⟩,⟨-3865516503231,-3865417847089⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨331431301610,331431301614⟩,⟨1921138871500,1921138871502⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-331431301614,-331431301610⟩,⟨-1921138871502,-1921138871500⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨768080326162,768080326166⟩,⟨-1921138871502,-1921138871500⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1327999055087,1327999082099⟩,⟨-8563893462913,-8563893395123⟩,⟨-3919134790654,-3919134759623⟩,⟨51218393989583,51218393998028⟩,⟨33241937554109,33241937635631⟩,⟨10726643461625,10726643463475⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1327999082099,-1327999055087⟩,⟨8563893395123,8563893462913⟩,⟨3919134759623,3919134790654⟩,⟨-51218393998028,-51218393989583⟩,⟨-33241937635631,-33241937554109⟩,⟨-10726643463475,-10726643461625⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-228487454323,-228487427311⟩,⟨8563893395123,8563893462913⟩,⟨3919134759623,3919134790654⟩,⟨-51218393998028,-51218393989583⟩,⟨-33241937635631,-33241937554109⟩,⟨-10726643463475,-10726643461625⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11543687474,-11543686108⟩,⟨461539996279,461540003142⟩,⟨106652931001,106652943381⟩,⟨-4752055895260,-4752055877543⟩,⟨1477666489818,1477666552078⟩,⟨2591843334610,2591843359555⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨436208364614,436208529964⟩,⟨842536227129,842539608464⟩,⟨-76947260670,-76944456844⟩,⟨-18102774651005,-18102677218748⟩,⟨-5502890063553,-5502792151427⟩,⟨-1273673168621,-1273574487534⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99127803250,-99127803248⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨5008154097,5008154098⟩,⟨31891590912,31891590916⟩,⟨39631760400,39631760401⟩,⟨-333298437985,-333298437976⟩,⟨252372404139,252372404144⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10993180284,10993180551⟩,⟨14454098405,14454100108⟩,⟨86993946002,86993948090⟩,⟨-946403700603,-946403682653⟩,⟨114381737068,114381750391⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1467064795516,1467064816445⟩,⟨-7253572109557,-7253571739044⟩,⟨-1353124609196,-1353124542942⟩,⟨105111348967061,105111356225616⟩,⟨22106360220197,22106361686357⟩,⟨4940502938121,4940503216863⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14668064782,14668065349⟩,⟨-53237025822,-53237017807⟩,⟨102546084658,102546090093⟩,⟨-402556249396,-402556077119⟩,⟨-218051765025,-218051678982⟩,⟨-164723555401,-164723535789⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14668065349,-14668064782⟩,⟨53237017807,53237025822⟩,⟨-102546090093,-102546084658⟩,⟨402556077119,402556249396⟩,⟨218051678982,218051765025⟩,⟨164723535789,164723555401⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113795868599,-113795868030⟩,⟨-825942787685,-825942779668⟩,⟨-102546090093,-102546084658⟩,⟨2601579332671,2601579504948⟩,⟨218051678982,218051765025⟩,⟨164723535789,164723555401⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨96044644380,96044646339⟩,⟨-619364975477,-619364970552⟩,⟨586538355794,586538371270⟩,⟨3704258988469,3704258989181⟩,⟨-3206114266867,-3206114227728⟩,⟨-2367482237108,-2367482236849⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨128151183678,128151188121⟩,⟨-1460025789146,-1460025725494⟩,⟨664412617390,664412657405⟩,⟨22296250408906,22296251784104⟩,⟨-5454058155808,-5454057531963⟩,⟨-4170997321741,-4170997134399⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-128151188121,-128151183678⟩,⟨1460025725494,1460025789146⟩,⟨-664412657405,-664412617390⟩,⟨-22296251784104,-22296250408906⟩,⟨5454057531963,5454058155808⟩,⟨4170997134399,4170997321741⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨971360439655,971360444098⟩,⟨1460025725494,1460025789146⟩,⟨-664412657405,-664412617390⟩,⟨-22296251784104,-22296250408906⟩,⟨5454057531963,5454058155808⟩,⟨4170997134399,4170997321741⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124335826121,124335826694⟩,⟨779696710211,779696721081⟩,⟨186244850284,186244856654⟩,⟨-2554634076576,-2554633815990⟩,⟨-656701934742,-656701806447⟩,⟨-147764009433,-147763961658⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11777501259,11777501378⟩,⟨170964768686,170964771202⟩,⟨21226370730,21226371962⟩,⟨702370881827,702370944272⟩,⟨108928012568,108928040270⟩,⟨-14968755910,-14968749649⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170814578982,170814733748⟩,⟨1685496703513,1685502245279⟩,⟨102915281166,102917839771⟩,⟨-2124211453707,-2123996686100⟩,⟨538777097075,538904946646⟩,⟨-519258506620,-519170502810⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170814733748,-170814578982⟩,⟨-1685502245279,-1685496703513⟩,⟨-102917839771,-102915281166⟩,⟨2123996686100,2124211453707⟩,⟨-538904946646,-538777097075⟩,⟨519170502810,519258506620⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨59040714528,59040928492⟩,⟨-93747244166,-93740061119⟩,⟨138605265338,138608619053⟩,⟨-1668001865745,-1667733167691⟩,⟨-1832379539305,-1832215329519⟩,⟨391129412738,391245536665⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27571648105685,27571673368802⟩,⟨-237014537767387,-237013908903845⟩,⟨-82888592004659,-82888181452757⟩,⟨3264953444703198,3264975743457068⟩,⟨1267356855972125,1267373650748221⟩,⟨298662489621155,298676742800491⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14060240261,14060240392⟩,⟨176340535450,176340538722⟩,⟨42122169034,42122170672⟩,⟨528042474073,528042566507⟩,⟨115620276322,115620318744⟩,⟨29676419195,29676434474⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352578351119,352578677462⟩,⟨1391088346997,1391100550733⟩,⟨-3688826189,-3682557389⟩,⟨-21032530090627,-21032026975073⟩,⟨-3267816569468,-3267507395229⟩,⟨-1787521514655,-1787306445116⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352578677462,-352578351119⟩,⟨-1391100550733,-1391088346997⟩,⟨3682557389,3688826189⟩,⟨21032026975073,21032530090627⟩,⟨3267507395229,3267816569468⟩,⟨1787306445116,1787521514655⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83629687152,83630178845⟩,⟨-548564323604,-548548738533⟩,⟨-73264703281,-73255630655⟩,⟨2929252324068,2929852871879⟩,⟨-2235382668324,-2234975581959⟩,⟨513633276495,513947027121⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239867204390,239867204395⟩,⟨1550199981060,1550199981068⟩,⟨307082114775,307082114779⟩,⟨-3877393211067,-3877393211062⟩,⟨-1536160652332,-1536160652324⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1650435892337,-1650434405397⟩,⟨-4306515668321,-4306473130940⟩,⟨492868396774,492891681923⟩,⟨45304690810681,45306243125649⟩,⟨-8066000870065,-8064967144033⟩,⟨1738946359711,1739756681403⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186635871687,-186635702678⟩,⟨-1657366410111,-1657360526868⟩,⟨-223830281269,-223827386429⟩,⟨2850083010756,2850322834624⟩,⟨-306343423875,-306201695008⟩,⟨585420329976,585520130049⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨53231332703,53231501717⟩,⟨-107166429051,-107160545800⟩,⟨83251833506,83254728350⟩,⟨-1027310200311,-1027070376438⟩,⟨-1842504076207,-1842362347332⟩,⟨233920122584,234019922660⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4490681463,4490724140⟩,⟨-36587012619,-36585480721⟩,⟨6608296525,6609115030⟩,⟨123956706786,124020532899⟩,⟨-322315875494,-322275381714⟩,⟨38858222412,38886911746⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2577121250,2577137616⟩,⟨-10376661434,-10376058828⟩,⟨8061044440,8061350338⟩,⟨-78583765784,-78557934833⟩,⟨-194634359716,-194618614816⟩,⟨35257012591,35267624678⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4455802952,4455831340⟩,⟨-35530473992,-35529320026⟩,⟨5887908444,5888488740⟩,⟨89628972556,89682395006⟩,⟨-300619066178,-300587495044⟩,⟨28163960337,28184332161⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4455831340,-4455802952⟩,⟨35529320026,35530473992⟩,⟨-5888488740,-5887908444⟩,⟨-89682395006,-89628972556⟩,⟨300587495044,300619066178⟩,⟨-28184332161,-28163960337⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨34850123,34921188⟩,⟨-1057692593,-1055006729⟩,⟨719807785,721206586⟩,⟨34274311780,34391560343⟩,⟨-21728380450,-21656315536⟩,⟨10673890251,10722951409⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨59040714528,59040928492⟩,⟨-93747244166,-93740061119⟩,⟨138605265338,138608619053⟩,⟨-1668001865745,-1667733167691⟩,⟨-1832379539305,-1832215329519⟩,⟨391129412738,391245536665⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨34850123,34921188⟩,⟨-1057692593,-1055006729⟩,⟨719807785,721206586⟩,⟨34274311780,34391560343⟩,⟨-21728380450,-21656315536⟩,⟨10673890251,10722951409⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨137009456742,140874927309⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110380659508,-109951162777⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439375154380,439804651111⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨54750263377,56349970924⟩,⟨-140874927309,-137009456742⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨164701426154,166730630432⟩,⟨958636700467,962502171034⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨54320766646,56779467655⟩,⟨-140874927309,-137009456742⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2087408666112,-2073944862912⟩,⟨6321767009727,6425459411761⟩,⟨2897476546120,2936042140853⟩,⟨-37549879063761,-36347717582688⟩,⟨-24498104531651,-23910142756244⟩,⟨-7840156697839,-7635544839394⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-316535954763,-310666725168⟩,⟨-880328416909,-833859996231⟩,⟨-400935751470,-383544545182⟩,⟨5329494093262,5804864798948⟩,⟨3411511707683,3646154580973⟩,⟨1126831321572,1205066704915⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨310666725168,316535954763⟩,⟨833859996231,880328416909⟩,⟨383544545182,400935751470⟩,⟨-5804864798948,-5329494093262⟩,⟨-3646154580973,-3411511707683⟩,⟨-1205066704915,-1126831321572⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-166730630432,-164701426154⟩,⟨-962502171034,-958636700467⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨932780997344,934810201622⟩,⟨-962502171034,-958636700467⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-180815722624,-178426404608⟩,⟨-1134545334677,-1127536046512⟩,⟨-518417859309,-516787354650⟩,⟨-1170695319558,-1156274753324⟩,⟨758295115401,766085386330⟩,⟨-244433137460,-242897995055⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-153730417990,-151369713096⟩,⟨-809030510273,-798271387269⟩,⟨-369460553444,-366095108148⟩,⟨970810054110,1005404172173⟩,⟨1363638997212,1380539431977⟩,⟨205207886164,208669496175⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151369713096,153730417990⟩,⟨798271387269,809030510273⟩,⟨366095108148,369460553444⟩,⟨-1005404172173,-970810054110⟩,⟨-1380539431977,-1363638997212⟩,⟨-208669496175,-205207886164⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨462036438264,470266372753⟩,⟨1632131383500,1689358927182⟩,⟨749639653330,770396304914⟩,⟨-6810268971121,-6300304147372⟩,⟨-5026694012950,-4775150704895⟩,⟨-1413736201090,-1332039207736⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨818995035090,829117430216⟩,⟨4038469242974,4109988634284⟩,⟨749639653330,770396304914⟩,⟨-19114054662894,-18387524054429⟩,⟨-5026694012950,-4775150704895⟩,⟨-1413736201090,-1332039207736⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨108641533292,113558935310⟩,⟨-281749854618,-274018913484⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10645800934241,11127657931386⟩,⟨25688430392590,28858355634400⟩,⟨-90094378565924,-82380138845294⟩,⟨123972909151905,149681935777787⟩,⟨-261148034839366,-172332348452390⟩,⟨1274960393884884,1458886874350374⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨7929755256281,8391121035305⟩,⟨58236252326007,63356777252967⟩,⟨-60679945010382,-53565798363373⟩,⟨87604719003213,150584136015675⟩,⟨-567058600534951,-456959176531408⟩,⟨809120962908983,974884710144168⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨99274989568,104977454336⟩,⟨-828329604894,-680438025724⟩,⟨625867988219,793332569217⟩,⟨7285937910460,11983340439423⟩,⟨-7118222900851,-1098719725964⟩,⟨-4915905339459,2477204516381⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1198786617344,1204489082112⟩,⟨-828329604894,-680438025724⟩,⟨625867988219,793332569217⟩,⟨7285937910460,11983340439423⟩,⟨-7118222900851,-1098719725964⟩,⟨-4915905339459,2477204516381⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨95045948416,100263775232⟩,⟨-759733232784,-621134331871⟩,⟨571320355426,727634402928⟩,⟨6125975314408,10640075129925⟩,⟨-6205992887457,-500184637210⟩,⟨-4990338618701,1975194650021⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨103627654419,109836603405⟩,⟨-907804712851,-736036237970⟩,⟨677007313082,869449843323⟩,⟨8077698058392,13893412266287⟩,⟨-8543968590456,-1347452504967⟩,⟨-5264658618515,3439696600693⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-104977454336,-99274989568⟩,⟨680438025724,828329604894⟩,⟨-793332569217,-625867988219⟩,⟨-11983340439423,-7285937910460⟩,⟨1098719725964,7118222900851⟩,⟨-2477204516381,4915905339459⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨994534173440,1000236638208⟩,⟨680438025724,828329604894⟩,⟨-793332569217,-625867988219⟩,⟨-11983340439423,-7285937910460⟩,⟨1098719725964,7118222900851⟩,⟨-2477204516381,4915905339459⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-110332611200,-104046231424⟩,⟨747972522387,915763436326⟩,⟨-877072309673,-687986326648⟩,⟨-14010957582221,-8517906736046⟩,⟨1675790616104,8600080355953⟩,⟨-3438318451277,5004314011558⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-100370671236,-94112267805⟩,⟨593438440833,768689577537⟩,⟨-738655810847,-542691358349⟩,⟨-11130669768397,-5122354343999⟩,⟨-520004508854,6868079891341⟩,⟨-2837932265672,6066725039884⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨3256983183,15724335600⟩,⟨-314366272018,32653339567⟩,⟨-61648497765,326758484974⟩,⟨-3052971710005,8771057922288⟩,⟨-9063973099310,5520627386374⟩,⟨-8102590884187,9506421640577⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1628491591,7862167800⟩,⟨-157183136009,16326669784⟩,⟨-30824248883,163379242487⟩,⟨-1526485855003,4385528961144⟩,⟨-4531986549655,2760313693187⟩,⟨-4051295442094,4753210820289⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7862167800,-1628491591⟩,⟨-16326669784,157183136009⟩,⟨-163379242487,30824248883⟩,⟨-4385528961144,1526485855003⟩,⟨-2760313693187,4531986549655⟩,⟨-4753210820289,4051295442094⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754261215816,760494911289⟩,⟨-16326669784,157183136009⟩,⟨-163379242487,30824248883⟩,⟨-4385528961144,1526485855003⟩,⟨-2760313693187,4531986549655⟩,⟨-4753210820289,4051295442094⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8963546455,10022873466⟩,⟨-158171921200,-122873603514⟩,⟨113019337734,151489136550⟩,⟨2157880438799,3536316413588⟩,⟨-2554577391742,-973049768800⟩,⟨-226188584959,1617858632710⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-10022873466,-8963546455⟩,⟨122873603514,158171921200⟩,⟨-151489136550,-113019337734⟩,⟨-3536316413588,-2157880438799⟩,⟨973049768800,2554577391742⟩,⟨-1617858632710,226188584959⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1089488754310,1090548081321⟩,⟨122873603514,158171921200⟩,⟨-151489136550,-113019337734⟩,⟨-3536316413588,-2157880438799⟩,⟨973049768800,2554577391742⟩,⟨-1617858632710,226188584959⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-10068836032,-9000282944⟩,⟨123883539042,159627041454⟩,⟨-152882777780,-113948278054⟩,⟨-3592023797013,-2189574849166⟩,⟨993886275444,2600274025545⟩,⟨-1654000054277,216460361841⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-5034418016,-4500141472⟩,⟨61941769521,79813520727⟩,⟨-76441388890,-56974139027⟩,⟨-1796011898507,-1094787424583⟩,⟨496943137722,1300137012773⟩,⟨-827000027139,108230180921⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4500141472,5034418016⟩,⟨-79813520727,-61941769521⟩,⟨56974139027,76441388890⟩,⟨1094787424583,1796011898507⟩,⟨-1300137012773,-496943137722⟩,⟨-108230180921,827000027139⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766623525088,767157820896⟩,⟨-79813520727,-61941769521⟩,⟨56974139027,76441388890⟩,⟨1094787424583,1796011898507⟩,⟨-1300137012773,-496943137722⟩,⟨-108230180921,827000027139⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272372188577,272637020331⟩,⟨30718400878,39542980300⟩,⟨-37872284138,-28254834433⟩,⟨-884079103397,-539470109699⟩,⟨243262442200,638644347936⟩,⟨-404464658178,56547146240⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533247050176,1534315641792⟩,⟨-159627041454,-123883539042⟩,⟨113948278054,152882777780⟩,⟨2189574849166,3592023797014⟩,⟨-2600274025546,-993886275444⟩,⟨-216460361842,1654000054278⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1208639809256,1215569913936⟩,⟨-1012426293056,-822209919339⟩,⟨756270003521,969651147885⟩,⟨9922652316174,16333107381384⟩,⟨-10315461627541,-2356588477360⟩,⟨-5062041463040,4574731643296⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1317767990736,1331628200096⟩,⟨-2024852586112,-1644419838678⟩,⟨1512540007042,1939302295769⟩,⟨19845304632350,32666214762757⟩,⟨-20630923255076,-4713176954719⟩,⟨-10119174416583,9149463286589⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨199092179904,210596386432⟩,⟨-1689484779275,-1357780447605⟩,⟨1248888635054,1618103823255⟩,⟨13790038491925,25579132079184⟩,⟨-15671665080641,-1405279593481⟩,⟨-10824471753790,6215516568847⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨68102303277,72609345646⟩,⟨-574486313439,-451770872210⟩,⟨413744430958,551664227742⟩,⟨4342582388337,8458813455425⟩,⟨-5221980350129,-84523799862⟩,⟨-4089751305649,2144682978112⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379817588223,380451860861⟩,⟨3254769203,24491766946⟩,⟨-24621564140,-1491695505⟩,⟨-702767793987,131482649698⟩,⟨-299177302331,655987527247⟩,⟨-628616907915,483181463952⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177605221535,3182911632057⟩,⟨-205243601980,-27184442181⟩,⟨12458920334,206331316218⟩,⟨-1101373409119,5915738008771⟩,⟨-5523854695082,2506924319859⟩,⟨-4049014163193,5294627026600⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨196816685721,210192530042⟩,⟨-1676600525699,-1307308417015⟩,⟨1196499347646,1610606040528⟩,⟨12499735701462,25092061047890⟩,⟨-15692372056983,-94071876630⟩,⟨-12097192351635,6765209959114⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨395908865625,420788916474⟩,⟨-3366085304974,-2665088864620⟩,⟨2445387982700,3228709863783⟩,⟨26289774193387,50671193127074⟩,⟨-31364037137624,-1499351470111⟩,⟨-22921664105425,12980726527961⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517420614127,526008543690⟩,⟨-22585207788,217436490994⟩,⟨-226007764508,42640175562⟩,⟨-6071311391530,2156577944572⟩,⟨-3865143260416,6278055954950⟩,⟨-6584430018023,5652841254626⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨354948771473,363822274059⟩,⟨-23432133630,225590172153⟩,⟨-234482861043,44239145425⟩,⟨-6303823418282,2284073937767⟩,⟨-4058546969834,6522621228728⟩,⟨-6840844492257,5915192540438⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨709897542946,727644548118⟩,⟨-46864267260,451180344306⟩,⟨-468965722086,88478290850⟩,⟨-12607646836564,4568147875534⟩,⟨-8117093939668,13045242457456⟩,⟨-13681688984514,11830385080876⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523224176710,1525352095337⟩,⟨-36753437940,34288382158⟩,⟨-37540858496,39863440046⟩,⟨-1346741564422,1434143358215⟩,⟨-1627224256746,1560691116298⟩,⟨-1834318994552,1880188639237⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨983466725667,1009461026236⟩,⟨-89337797366,648614002697⟩,⟨-675440103662,149127082441⟩,⟨-18412005860289,7314630254511⟩,⟨-12367749951652,19162542232061⟩,⟨-20228539460792,17688600961408⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67472327928,67603600524⟩,⟨15219189802,19610307072⟩,⟨-18781768996,-13998635208⟩,⟨-436719478486,-264431959584⟩,⟨117798373674,315140184726⟩,⟨-199131506754,30652073049⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50258223908,50978381787⟩,⟨259159934989,267490829352⟩,⟨31839263530,36940720120⟩,⟨-1392751244309,-1178724447927⟩,⟨-281152351605,-93066468045⟩,⟨-263404100597,-77715851410⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2138082451777,2141063749739⟩,⟨-445503731600,-345506252054⟩,⟨317797205204,426681139850⟩,⟨6134553241042,10071342494141⟩,⟨-7301505931260,-2797586632344⟩,⟨-580501926255,4658670693144⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2981513364120,2987751578347⟩,⟨-932518574525,-722702373121⟩,⟨664742802791,893119541065⟩,⟨12890161358298,21178129052584⟩,⟨-15376269321181,-5905478193377⟩,⟨-1165702752526,9840419141714⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136283748578,138525811641⟩,⟨659520557472,693830233926⟩,⟨116722714976,141789754517⟩,⟨-3649109609293,-2555086162646⟩,⟨-1351549068471,-325950884975⟩,⟨-731308150276,305519963486⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8727079850993,8870652827126⟩,⟨-45161122953698,-41549574770554⟩,⟨-9229036476378,-7353492045656⟩,⟨556604126588338,697355997838839⟩,⟨90554659804646,181943128939375⟩,⟨-7493971312383,66804343427380⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7806004437671,8144141526149⟩,⟨-42183162902425,-31931444587566⟩,⟨-13922496962294,-5374258916074⟩,⟨296032205897391,706594107468210⟩,⟨-30352885094246,350134443980491⟩,⟨-172583733087790,215380297875576⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15612008875342,16288283052298⟩,⟨-84366325804850,-63862889175132⟩,⟨-27844993924588,-10748517832148⟩,⟨592064411794782,1413188214936420⟩,⟨-60705770188492,700268887960982⟩,⟨-345167466175580,430760595751152⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10952333724070,10995116277821⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨2173453475238562,2199023255588622⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9852822096294,9895604650045⟩,⟨-109951162778820,-109097176394608⟩,⟨0,0⟩,⟨2173453475238575,2199023255588602⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2411110045440,2415874025920⟩,⟨-12269843176037,-12121908488212⟩,⟨0,0⟩,⟨104571265817406,111755106875729⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7250772197539,7340105352120⟩,⟨-42894997948767,-41689138446103⟩,⟨-19600391744569,-19107521787766⟩,⟨479392874863260,501349983619302⟩,⟨267537233605005,278087272635185⟩,⟨100705794892825,104678431197066⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6151260569763,6240593724344⟩,⟨-42894997948767,-41689138446102⟩,⟨-19600391744570,-19107521787765⟩,⟨479392874863266,501349983619294⟩,⟨267537233605008,278087272635182⟩,⟨100705794892825,104678431197065⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1893129140288,1908982261312⟩,⟨-7667298187619,-7345085179097⟩,⟨-3503486543565,-3366497373747⟩,⟨30995918532040,40546683810444⟩,⟨22705490910090,27217649118576⟩,⟨6579536061524,8403243279038⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨98913096826,99342593558⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139725998953,141755203232⟩,⟨667314001278,674725030728⟩,⟨306055779186,308107846684⟩,⟨-1685130754132,-1671622746438⟩,⟨-1540110512298,-1532210792360⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4304239185728,4324856287232⟩,⟨-19937141363656,-19466993667309⟩,⟨-3503486543565,-3366497373747⟩,⟨135567184349446,152301790686173⟩,⟨22705490910090,27217649118576⟩,⟨6579536061524,8403243279038⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨791817731250,841577832948⟩,⟨-6732170609948,-5330177729240⟩,⟨4890775965400,6457419727566⟩,⟨52579548386774,101342386254148⟩,⟨-62728074275248,-2998702940222⟩,⟨-45843328210850,25961453055922⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5096056916978,5166434120180⟩,⟨-26669311973604,-24797171396549⟩,⟨1387289421835,3090922353819⟩,⟨188146732736220,253644176940321⟩,⟨-40022583365158,24218946178354⟩,⟨-39263792149326,34364696334960⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458446057800,466795395319⟩,⟨1663250231456,1902370509989⟩,⟨124801856970,279269664238⟩,⟨-36077910933824,-26911694782119⟩,⟨-2507355224779,4660957512411⟩,⟨-3547544970422,3104904008750⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨40881822701,43026328045⟩,⟨-863164545825,-819985580701⟩,⟨330673852191,333275037186⟩,⟨10140730360464,10904825623478⟩,⟨-6692236630045,-6625935308195⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨499327880501,509821723364⟩,⟨800085685631,1082384929288⟩,⟨455475709161,612544701424⟩,⟨-25937180573360,-16006869158641⟩,⟨-9199591854824,-1964977795784⟩,⟨-3547544970422,3104904008750⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500409295618,501398026980⟩,⟨2510857612204,2551553037358⟩,⟨0,0⟩,⟨1957166706152,4308831445771⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227253906781,232488315493⟩,⟨1504405667330,1676692440687⟩,⟨207295923967,279331929716⟩,⟨-7284853193937,-263503479369⟩,⟨-3155057632748,527186001585⟩,⟨-1617747374251,1415894752381⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-841577832948,-791817731250⟩,⟨5330177729240,6732170609948⟩,⟨-6457419727566,-4890775965400⟩,⟨-101342386254148,-52579548386774⟩,⟨2998702940222,62728074275248⟩,⟨-25961453055922,45843328210850⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3462661352780,3533038555982⟩,⟨-14606963634416,-12734823057361⟩,⟨-9960906271131,-8257273339147⟩,⟨34224798095298,99722242299399⟩,⟨25704193850312,89945723393824⟩,⟨-19381916994398,54246571489888⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨440035197746,455499137870⟩,⟨218341759859,549738319996⟩,⟨-320362937107,-59298021555⟩,⟨-18992892180485,-7865645071947⟩,⟨-11888113075899,-1785350014583⟩,⟨-9211936938838,1290958626681⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨329402852308,333461260864⟩,⟨1917273400934,1925004342068⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-333461260864,-329402852308⟩,⟨-1925004342068,-1917273400934⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨766050366912,770108775468⟩,⟨-1925004342068,-1917273400934⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1318978568205,1337069981355⟩,⟨-8712461531444,-8418602502982⟩,⟨-3981062297281,-3858526147193⟩,⟨47211422176767,55246820579435⟩,⟨31346259116477,35149151188640⟩,⟨9965221786187,11491292843347⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1337069981355,-1318978568205⟩,⟨8418602502982,8712461531444⟩,⟨3858526147193,3981062297281⟩,⟨-55246820579435,-47211422176767⟩,⟨-35149151188640,-31346259116477⟩,⟨-11491292843347,-9965221786187⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-237558353579,-219466940429⟩,⟨8418602502982,8712461531444⟩,⟨3858526147193,3981062297281⟩,⟨-55246820579435,-47211422176767⟩,⟨-35149151188640,-31346259116477⟩,⟨-11491292843347,-9965221786187⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12267661854,-10842643366⟩,⟨443264060167,480354122841⟩,⟨95605018600,117883498306⟩,⟨-5085548611516,-4430527913436⟩,⟨1258421682511,1693089760237⟩,⟨2490388899687,2692523541729⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨427767535892,444656494504⟩,⟨661605820026,1030092442837⟩,⟨-224757918507,58585476751⟩,⟨-24078440792001,-12296172985383⟩,⟨-10629691393388,-92260254346⟩,⟨-6721548039151,3983482168410⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99342593558,-98913096826⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4886747093,5130113621⟩,⟨30685905417,33098074951⟩,⟨39526600801,39737037424⟩,⟨-338958819005,-327642586802⟩,⟨251814268106,252930624064⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10716107686,11272011986⟩,⟨10042099528,18848439610⟩,⟨86677559241,87311197222⟩,⟨-1018711241707,-873669169811⟩,⟨108761645553,119972071186⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1458087570658,1476108850260⟩,⟨-7407603633242,-7102060085898⟩,⟨-1388517335477,-1318317793303⟩,⟨101521834722797,108797678757998⟩,⟨21240127116453,22995900643819⟩,⟨4726419029094,5160282524817⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14210876018,15132824640⟩,⟨-62624473173,-43914125990⟩,⟨100710247111,104367787125⟩,⟨-632147299118,-172946426420⟩,⟨-260790906324,-175101384747⟩,⟨-174456914978,-154950949566⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-15132824640,-14210876018⟩,⟨43914125990,62624473173⟩,⟨-104367787125,-100710247111⟩,⟨172946426420,632147299118⟩,⟨175101384747,260790906324⟩,⟨154950949566,174456914978⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114475418198,-113123972844⟩,⟨-835695176232,-816125835587⟩,⟨-104367787125,-100710247111⟩,⟨2371969681972,2831170554670⟩,⟨175101384747,260790906324⟩,⟨154950949566,174456914978⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨93529002934,98581037092⟩,⟨-640532422715,-598781528479⟩,⟨575589917748,597272955165⟩,⟨3361869237578,4058601254300⟩,⟨-3434652124535,-2973873413067⟩,⟨-2477730878030,-2256619087948⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨124030954497,132346341452⟩,⟨-1524081041299,-1398188490225⟩,⟨638810002703,689705253884⟩,⟨20829520976176,23834168896194⟩,⟨-6110285045562,-4790937904342⟩,⟨-4432868920868,-3910157012148⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-132346341452,-124030954497⟩,⟨1398188490225,1524081041299⟩,⟨-689705253884,-638810002703⟩,⟨-23834168896194,-20829520976176⟩,⟨4790937904342,6110285045562⟩,⟨3910157012148,4432868920868⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨967165286324,975480673279⟩,⟨1398188490225,1524081041299⟩,⟨-689705253884,-638810002703⟩,⟨-23834168896194,-20829520976176⟩,⟨4790937904342,6110285045562⟩,⟨3910157012148,4432868920868⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122907418503,125764437225⟩,⟨764672423096,795105411275⟩,⟨180295698439,192171577472⟩,⟨-2870700360696,-2246897441587⟩,⟨-791594343948,-520632895508⟩,⟨-201792642111,-93011729527⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11638833922,11918583707⟩,⟨167935280590,174016449430⟩,⟨20723279264,21732459714⟩,⟨622025156692,782274207610⟩,⟨95202424766,122620789556⟩,⟨-17877890836,-12070871927⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165260260918,176563175958⟩,⟨1469998073750,1901880407953⟩,⟨-7585978088,208169004772⟩,⟨-11605384596862,7399140782312⟩,⟨-5380752970286,6561996671650⟩,⟨-5107165545513,4092832191475⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176563175958,-165260260918⟩,⟨-1901880407953,-1469998073750⟩,⟨-208169004772,7585978088⟩,⟨-7399140782312,11605384596862⟩,⟨-6561996671650,5380752970286⟩,⟨-4092832191475,5107165545513⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50690730823,67228054575⟩,⟨-397474740623,206694366937⟩,⟨-873080805,286917907804⟩,⟨-14683993976249,11341881117493⟩,⟨-9717054304398,5907938971871⟩,⟨-5710579565726,6523060297894⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26880615169234,28279867741791⟩,⟨-260061772259941,-214251696421915⟩,⟨-100245761095615,-66307729139859⟩,⟨2312771964777232,4230888090045972⟩,⟨484337865484443,2082016923638785⟩,⟨-440039985383782,1049827791838032⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13739039352,14385199093⟩,⟨170955742802,181891636356⟩,⟨40308221036,43961973082⟩,⟨406893194556,647618891622⟩,⟨69690452476,161539021006⟩,⟨12966121728,46380743919⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨335888971327,369992929145⟩,⟨777031493992,2001123840376⟩,⟨-326095190544,302165321440⟩,⟨-47196697965672,5385689565516⟩,⟨-19225840267294,13230181398647⟩,⟨-13456454664229,10066405500422⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-369992929145,-335888971327⟩,⟨-2001123840376,-777031493992⟩,⟨-302165321440,326095190544⟩,⟨-5385689565516,47196697965672⟩,⟨-13230181398647,19225840267294⟩,⟨-10066405500422,13456454664229⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57774606747,108767523177⟩,⟨-1339518020350,253060948845⟩,⟨-526923239947,384680667295⟩,⟨-29464130357517,34900524980289⟩,⟨-23859872792035,19133580012948⟩,⟨-16787953539573,17439936832639⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238639095779,241097796790⟩,⟨1546064310038,1554334332950⟩,⟨306055779186,308107846684⟩,⟨-3884154009684,-3870646001990⟩,⟨-1540110512298,-1532210792360⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1695851109743,-1606251742536⟩,⟨-5809502759003,-2804420874091⟩,⟨-440247294025,1469086830642⟩,⟨-18648090725251,109273325456422⟩,⟨-56594307334759,39355844243018⟩,⟨-40679362398862,43807662629865⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-193974993121,-179552676073⟩,⟨-1890847887915,-1430581089240⟩,⟨-346755619913,-95352699007⟩,⟨-7252781747897,13025830468736⟩,⟨-7046535785566,6325031443208⟩,⟨-4671003716866,5835581560156⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44664102658,61545120717⟩,⟨-344783577877,123753243710⟩,⟨-40699840727,212755147677⟩,⟨-11136935757581,9155184466746⟩,⟨-8586646297864,4792820650848⟩,⟨-5022847437756,5484424698492⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2663579870,6650433520⟩,⟨-121222486669,35919974496⟩,⟨-32304330643,51903664901⟩,⟨-3757758783885,4224395407425⟩,⟨-2908732600012,2010848808364⟩,⟨-1866387246254,1912388763025⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1814334669,3444985745⟩,⟨-38598494798,13854166034⟩,⟨-4556344014,23817922278⟩,⟨-1324391890665,1241155857800⟩,⟨-1094705410624,584448326068⟩,⟨-578058193286,696317025351⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3123904964,5981216125⟩,⟨-91038213980,11933402237⟩,⟨-18887877651,35797746235⟩,⟨-2441494599191,2820269948842⟩,⟨-2073406765247,1254766226041⟩,⟨-1144559880232,1264317764105⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5981216125,-3123904964⟩,⟨-11933402237,91038213980⟩,⟨-35797746235,18887877651⟩,⟨-2820269948842,2441494599191⟩,⟨-1254766226041,2073406765247⟩,⟨-1264317764105,1144559880232⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3317636255,3526528556⟩,⟨-133155888906,126958188476⟩,⟨-68102076878,70791542552⟩,⟨-6578028732727,6665890006616⟩,⟨-4163498826053,4084255573611⟩,⟨-3130705010359,3056948643257⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50690730823,67228054575⟩,⟨-397474740623,206694366937⟩,⟨-873080805,286917907804⟩,⟨-14683993976249,11341881117493⟩,⟨-9717054304398,5907938971871⟩,⟨-5710579565726,6523060297894⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3317636255,3526528556⟩,⟨-133155888906,126958188476⟩,⟨-68102076878,70791542552⟩,⟨-6578028732727,6665890006616⟩,⟨-4163498826053,4084255573611⟩,⟨-3130705010359,3056948643257⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (513/5120) u, BivariateJet2.affineZ (647/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000021

end


