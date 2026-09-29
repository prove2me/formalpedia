-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000038_000041_data
-- name    : GeneralCK_RB2_cells000038_000041_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T03:20:55.574223+00:00
-- url     : https://prove2.me/theorems/c6e115fb-3b22-4739-9d0a-172b5bd252fa
-- title:
--   Exact certificate data for RB2 cells 000038–000041
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000038 through 000041. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000038Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2119922333696,-2119922294720⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2119922333696,-2119922294720⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-172796227904,-172796227840⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-172796227904,-172796227840⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨84844253056,84844253120⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-91942877760,-91942877696⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨84844376960,84844377024⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-91943023360,-91943023296⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7098646336,-7098646272⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7098624704,-7098624640⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨176787130752,176787130816⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨176787400256,176787400320⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1947126066880,1947126105536⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1947126066944,1947126105536⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2506246686912,-2506246629056⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2126866256768,-2126866217792⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2113016830784,-2113016791872⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-173975734208,-173975734144⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-171618868032,-171618867968⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨82278724416,82278724480⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-88937455616,-88937455552⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨87432239424,87432239488⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-94990097408,-94990097344⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7557857984,-7557857920⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6658731136,-6658731072⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨171216179968,171216180032⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨182422336832,182422336896⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1939041057728,1939041096320⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1955247349824,1955247388416⟩



end LaneCBRB2Cell000038Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000038
open Set LaneCBRB2Cell000038Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112313394790,112313394791⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨119614839193,119614839194⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112313394791,-112313394790⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437442419097,437442419098⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨47588950671,47588950672⟩,⟨-119614839194,-119614839193⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159902345461,159902345463⟩,⟨979896788582,979896788583⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47588950670,47588950673⟩,⟨-119614839194,-119614839193⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2119922333696,-2119922294720⟩,⟨6737911879569,6737911879662⟩,⟨3007917269048,3007917269094⟩,⟨-41290565148384,-41290565147248⟩,⟨-25993204039258,-25993204038631⟩,⟨-8228713611710,-8228713611462⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308301017283,-308301011610⟩,⟨-909401181873,-909401147107⟩,⟨-405971993750,-405971978227⟩,⟨6004900762815,6004900763235⟩,⟨3701099436121,3701099475326⟩,⟨1196704585323,1196704585418⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨308301011610,308301017283⟩,⟨909401147107,909401181873⟩,⟨405971978227,405971993750⟩,⟨-6004900763235,-6004900762815⟩,⟨-3701099475326,-3701099436121⟩,⟨-1196704585418,-1196704585323⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159902345463,-159902345461⟩,⟨-979896788583,-979896788582⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939609282313,939609282315⟩,⟨-979896788583,-979896788582⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-172796227904,-172796227840⟩,⟨-1146655246334,-1146655246328⟩,⟨-511886201355,-511886201351⟩,⟨-1195820235757,-1195820235745⟩,⟨752791812616,752791812626⟩,⟨-238312607633,-238312607629⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147666414421,-147666414365⟩,⟨-825898900377,-825898900311⟩,⟨-368695169860,-368695169828⟩,⟨1021911697059,1021911697086⟩,⟨1382913981263,1382913981348⟩,⟨203654725025,203654725035⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147666414365,147666414421⟩,⟨825898900311,825898900377⟩,⟨368695169828,368695169860⟩,⟨-1021911697086,-1021911697059⟩,⟨-1382913981348,-1382913981263⟩,⟨-203654725035,-203654725025⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨455967425975,455967431704⟩,⟨1735300047418,1735300082250⟩,⟨774667148055,774667163610⟩,⟨-7026812460321,-7026812459874⟩,⟨-5084013456674,-5084013417384⟩,⟨-1400359310453,-1400359310348⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨818562271573,818562283274⟩,⟨4125174033774,4125174126550⟩,⟨774667148055,774667163610⟩,⟨-19015276803284,-19015276802340⟩,⟨-5084013456674,-5084013417384⟩,⟨-1400359310453,-1400359310348⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95177901340,95177901346⟩,⟨-239229678388,-239229678386⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12701749066937,12701749067739⟩,⟨31925849396242,31925849400542⟩,⟨-116755754450172,-116755754435159⟩,⟨160491260581545,160491260614632⟩,⟨-293465617525360,-293465617370864⟩,⟨2146461266379069,2146461266795493⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9456173365090,9456173500860⟩,⟨71422820145131,71422821562863⟩,⟨-77973008249608,-77973006815656⟩,⟨139374775509572,139374782686957⟩,⟨-692763623929123,-692763609870664⟩,⟨1417294242141489,1417294268621068⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨88203623936,88203757824⟩,⟨-660036864497,-660034821500⟩,⟨720566613455,720568842763⟩,⟨8544249531282,8544300120323⟩,⟨-4332025453156,-4331954818277⟩,⟨-1379209476330,-1379113491604⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1187715251712,1187715385600⟩,⟨-660036864497,-660034821500⟩,⟨720566613455,720568842763⟩,⟨8544249531282,8544300120323⟩,⟨-4332025453156,-4331954818277⟩,⟨-1379209476330,-1379113491604⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨84844253056,84844377024⟩,⟨-611020365555,-611018405398⟩,⟨667054901945,667057040894⟩,⟨7570168583806,7570218486180⟩,⟨-3639620639571,-3639552420351⟩,⟨-1681478261309,-1681386665471⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨91650520857,91650665102⟩,⟨-710969021081,-710966597205⟩,⟨776169342192,776171987228⟩,⟨9570359909687,9570424228200⟩,⟨-5066745786843,-5066660665902⟩,⟨-1048484397824,-1048372178639⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-88203757824,-88203623936⟩,⟨660034821500,660036864497⟩,⟨-720568842763,-720566613455⟩,⟨-8544300120323,-8544249531282⟩,⟨4331954818277,4332025453156⟩,⟨1379113491604,1379209476330⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1011307869952,1011308003840⟩,⟨660034821500,660036864497⟩,⟨-720568842763,-720566613455⟩,⟨-8544300120323,-8544249531282⟩,⟨4331954818277,4332025453156⟩,⟨1379113491604,1379209476330⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-91943023360,-91942877696⟩,⟨717601322465,717603638653⟩,⟨-783415065552,-783412538091⟩,⟨-9757861559588,-9757802305104⟩,⟨5221074319973,5221155038856⟩,⟨941203623923,941311780393⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-84567287033,-84567141857⟩,⟨604841334321,604843810367⟩,⟨-660314033767,-660311331782⟩,⟨-7399045793457,-7398979294350⟩,⟨3499415820463,3499503126083⟩,⟨1777188828800,1777303122171⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7083233824,7083523245⟩,⟨-106127686760,-106122786838⟩,⟨115855308425,115860655446⟩,⟨2171314116230,2171444933850⟩,⟨-1567329966380,-1567157539819⟩,⟨728704430976,728930943532⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3541616912,3541761623⟩,⟨-53063843380,-53061393419⟩,⟨57927654212,57930327723⟩,⟨1085657058115,1085722466925⟩,⟨-783664983190,-783578769909⟩,⟨364352215488,364465471766⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3541761623,-3541616912⟩,⟨53061393419,53063843380⟩,⟨-57930327723,-57927654212⟩,⟨-1085722466925,-1085657058115⟩,⟨783578769909,783664983190⟩,⟨-364465471766,-364352215488⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758581621993,758581785968⟩,⟨53061393419,53063843380⟩,⟨-57930327723,-57927654212⟩,⟨-1085722466925,-1085657058115⟩,⟨783578769909,783664983190⟩,⟨-364465471766,-364352215488⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7075758981,7075780463⟩,⟨-105897437154,-105896948626⟩,⟨115608757540,115609290702⟩,⟨2163287241390,2163302344496⟩,⟨-1560152529400,-1560134787338⟩,⟨723166132569,723187712325⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7075780463,-7075758981⟩,⟨105896948626,105897437154⟩,⟨-115609290702,-115608757540⟩,⟨-2163302344496,-2163287241390⟩,⟨1560134787338,1560152529400⟩,⟨-723187712325,-723166132569⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092435847313,1092435868795⟩,⟨105896948626,105897437154⟩,⟨-115609290702,-115608757540⟩,⟨-2163302344496,-2163287241390⟩,⟨1560134787338,1560152529400⟩,⟨-723187712325,-723166132569⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7098646336,-7098624640⟩,⟨106582848189,106583341978⟩,⟨-116358099855,-116357560950⟩,⟨-2187646067095,-2187630727614⟩,⟨1581519153279,1581537145633⟩,⟨-740185685181,-740163837275⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3549323168,-3549312320⟩,⟨53291424094,53291670989⟩,⟨-58179049928,-58178780475⟩,⟨-1093823033548,-1093815363807⟩,⟨790759576639,790768572817⟩,⟨-370092842591,-370081918637⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3549312320,3549323168⟩,⟨-53291670989,-53291424094⟩,⟨58178780475,58179049928⟩,⟨1093815363807,1093823033548⟩,⟨-790768572817,-790759576639⟩,⟨370081918637,370092842591⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765672695936,765672726048⟩,⟨-53291670989,-53291424094⟩,⟨58178780475,58179049928⟩,⟨1093815363807,1093823033548⟩,⟨-790768572817,-790759576639⟩,⟨370081918637,370092842591⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273108961828,273108967199⟩,⟨26474237156,26474359289⟩,⟨-28902322676,-28902189385⟩,⟨-540825586124,-540821810347⟩,⟨390033696834,390038132350⟩,⟨-180796928082,-180791533142⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531345391872,1531345452096⟩,⟨-106583341978,-106582848188⟩,⟨116357560950,116358099856⟩,⟨2187630727614,2187646067096⟩,⟨-1581537145634,-1581519153278⟩,⟨740163837274,740185685182⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1195408139779,1195408298041⟩,⟨-780191243712,-780188622222⟩,⟨851739718963,851742579627⟩,⟨11118045848845,11118115030332⟩,⟨-6232426706577,-6232334534807⟩,⟨-416538047501,-416416165567⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1291304651782,1291304968306⟩,⟨-1560382487424,-1560377244443⟩,⟨1703479437926,1703485159254⟩,⟨22236091697697,22236230060661⟩,⟨-12464853413154,-12464669069617⟩,⟨-833075947204,-832832478934⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨176787130752,176787400320⟩,⟨-1328624261002,-1328619471070⟩,⟨1450467159692,1450472386791⟩,⟨17327958452632,17328092482063⟩,⟨-8860787309548,-8860615109227⟩,⟨-2622800801428,-2622579529714⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨60853970454,60854075982⟩,⟨-451120046168,-451118335216⟩,⟨492490396747,492492263793⟩,⟨5744093578878,5744138273783⟩,⟨-2856370502288,-2856310686155⟩,⟨-1056720057389,-1056640760370⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380372648736,380372671177⟩,⟨10397647768,10397942495⟩,⟨-11351537718,-11351216064⟩,⟨-214979714827,-214970558150⟩,⟨155983146409,155993874014⟩,⟨-74072172618,-74059161921⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178266766310,3178266953821⟩,⟨-86881738552,-86879265659⟩,⟨94846963273,94849662099⟩,⟨1800971816898,1801048809099⟩,⟨-1308618427471,-1308528342553⟩,⟨624474489939,624583597830⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨175905508414,175905823834⟩,⟨-1308823850980,-1308818683132⟩,⟨1428850441705,1428856081085⟩,⟨16774941895559,16775078804706⟩,⟨-8406932382565,-8406751368367⟩,⟨-2935043311059,-2934805075054⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨352692639166,352693224154⟩,⟨-2637448111982,-2637438154202⟩,⟨2879317601397,2879328467876⟩,⟨34102900348191,34103171286769⟩,⟨-17267719692113,-17267366477594⟩,⟨-5557844112487,-5557384604768⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523365158392,523365384654⟩,⟨73216866230,73220262642⟩,⟨-79935291918,-79931585588⟩,⟨-1493015182050,-1492924130795⟩,⟨1075631095588,1075750807104⟩,⟨-496804669408,-496647720376⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361083212508,361083446665⟩,⟨75771325748,75774857039⟩,⟨-82724168131,-82720314607⟩,⟨-1539805181820,-1539710128537⟩,⟨1107372063925,1107496729000⟩,⟨-507820993081,-507657871762⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722166425016,722166893330⟩,⟨151542651496,151549714078⟩,⟨-165448336262,-165440629214⟩,⟨-3079610363640,-3079420257074⟩,⟨2214744127850,2214993458000⟩,⟨-1015641986162,-1015315743524⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524269611409,1524269693115⟩,⟨-686393352,-685411034⟩,⟨748270248,749342316⟩,⟨24328383118,24358825706⟩,⟨-21402358296,-21366623878⟩,⟨16976124949,17019552613⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001150245457,1001150948354⟩,⟨209635043531,209645491245⟩,⟨-228872076233,-228860675078⟩,⟨-4253520863013,-4253236801686⟩,⟨3056482352091,3056851951760⟩,⟨-1397075417096,-1396594202563⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67837850138,67837852807⟩,⟨13151932624,13151993558⟩,⟨-14358162836,-14358096336⟩,⟨-267397685145,-267395792357⟩,⟨192370002960,192372223100⟩,⟨-88297248569,-88294552673⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50503790323,50503793033⟩,⟨264306994486,264307055730⟩,⟨37106204527,37106257030⟩,⟨-1273591975998,-1273590058348⟩,⟨-215062101814,-215060138327⟩,⟨-172367218269,-172365112773⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132782091582,2132782259337⟩,⟨-296888021708,-296886634578⟩,⟨324114107152,324115621024⟩,⟨6114311213198,6114354372461⟩,⟨-4427932345494,-4427881845518⟩,⟨2086354585897,2086415752479⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2970433368146,2970433718608⟩,⟨-620236444536,-620233522253⟩,⟨677115137151,677118326450⟩,⟨12816733929735,12816824998915⟩,⟨-9297636168691,-9297529865623⟩,⟨4410106986918,4410235421623⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136440707131,136440730551⟩,⟨685560756054,685561141516⟩,⟨131347759636,131348061470⟩,⟨-3150210107619,-3150198832247⟩,⟨-866240950649,-866229739208⟩,⟨-217394638663,-217382705342⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8860446691633,8860448212526⟩,⟨-44520283708958,-44520243393312⟩,⟨-8529732225393,-8529709696073⟩,⟨651966842326239,651968378264019⟩,⟨141969709521897,141970746213805⟩,⟨30539446493636,30540310223405⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8067798608123,8067805657276⟩,⟨-38848215015886,-38848065362665⟩,⟨-9611047685589,-9610929525697⟩,⟨542387815039592,542392786814232⟩,⟨161540375788693,161544948537917⟩,⟨20099914954313,20104787026695⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16135597216246,16135611314552⟩,⟨-77696430031772,-77696130725330⟩,⟨-19222095371178,-19221859051394⟩,⟨1084775630079184,1084785573628464⟩,⟨323080751577386,323089897075834⟩,⟨40199829908626,40209574053390⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10763861442032,10763861442129⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311394,2063168215367208⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9664349814256,9664349814353⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311405,2063168215367197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2389873986368,2389874044224⟩,⟨-11988464342936,-11988464342527⟩,⟨0,0⟩,⟨104010778944236,104010778977589⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7560400794085,7560400794181⟩,⟨-46330855480954,-46330855479728⟩,⟨-20682873682826,-20682873682252⟩,⟨567839782029263,567839782052065⟩,⟨305479644104493,305479644116315⟩,⟨113163647115292,113163647120124⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6460889166309,6460889166405⟩,⟨-46330855480954,-46330855479728⟩,⟨-20682873682826,-20682873682251⟩,⟨567839782029268,567839782052058⟩,⟨305479644104496,305479644116313⟩,⟨113163647115292,113163647120123⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1947126066880,1947126105536⟩,⟨-7884567126124,-7884567125745⟩,⟨-3519803470506,-3519803470332⟩,⟨40094744905546,40094744918087⟩,⟨26745995848390,26745995854492⟩,⟨7990401002605,7990401005208⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100840757001,100840757003⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136647693633,136647693636⟩,⟨694883350164,694883350171⟩,⟨310207623117,310207623121⟩,⟨-1746589471214,-1746589471210⟩,⟨-1559413873708,-1559413873700⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4337000053248,4337000149760⟩,⟨-19873031469060,-19873031468272⟩,⟨-3519803470506,-3519803470332⟩,⟨144105523849782,144105523895676⟩,⟨26745995848390,26745995854492⟩,⟨7990401002605,7990401005208⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨705385278332,705386448308⟩,⟨-5274896223964,-5274876308404⟩,⟨5758635202794,5758656935752⟩,⟨68205800696382,68206342573538⟩,⟨-34535439384226,-34534732955188⟩,⟨-11115688224974,-11114769209536⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5042385331580,5042386598068⟩,⟨-25147927693024,-25147907776676⟩,⟨2238831732288,2238853465420⟩,⟨212311324546164,212311866469214⟩,⟨-7789443535836,-7788737100696⟩,⟨-3125287222369,-3124368204328⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨462458005065,462458121230⟩,⟨1705821350068,1705824184484⟩,⟨205332513980,205334507220⟩,⟨-30633393186571,-30633309256110⟩,⟨1067043335806,1067125419035⟩,⟨-286633011780,-286548724829⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34717214595,34717216591⟩,⟨-707015524005,-707015513932⟩,⟨319124126993,319124145312⟩,⟨8773120154895,8773120181760⟩,⟨-6498957778804,-6498957686573⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497175219660,497175337821⟩,⟨998805826063,998808670552⟩,⟨524456640973,524458652532⟩,⟨-21860273031676,-21860189074350⟩,⟨-5431914442998,-5431832267538⟩,⟨-286633011780,-286548724829⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505853361827,505853374074⟩,⟨2537541677330,2537541800300⟩,⟨0,0⟩,⟨3442964323895,3442967248197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228735876846,228735936747⟩,⟨1606942647185,1606944295285⟩,⟨241287266334,241288197636⟩,⟨-3890193970483,-3890140055453⟩,⟨-1288682746464,-1288640178322⟩,⟨-131871525928,-131832744757⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-705386448308,-705385278332⟩,⟨5274876308404,5274896223964⟩,⟨-5758656935752,-5758635202794⟩,⟨-68206342573538,-68205800696382⟩,⟨34534732955188,34535439384226⟩,⟨11114769209536,11115688224974⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3631613604940,3631614871428⟩,⟨-14598155160656,-14598135244308⟩,⟨-9278460406258,-9278438673126⟩,⟨75899181276244,75899723199294⟩,⟨61280728803578,61281435238718⟩,⟨19105170212141,19106089230182⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451338222120,451338379531⟩,⟨480889497573,480892773260⟩,⟨-128535239620,-128532181261⟩,⟨-14787949254802,-14787854718196⟩,⟨-7517180188352,-7517071241577⟩,⟨-4010774005624,-4010647125438⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨319804690922,319804690926⟩,⟨1959793577164,1959793577166⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-319804690926,-319804690922⟩,⟨-1959793577166,-1959793577164⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨779706936850,779706936854⟩,⟨-1959793577166,-1959793577164⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1380783670599,1380783698020⟩,⟨-9061856797319,-9061856728115⟩,⟨-4045365394728,-4045365363828⟩,⟨56540010298333,56540010308753⟩,⟨35408439058832,35408439141203⟩,⟨11267744838893,11267744841060⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1380783698020,-1380783670599⟩,⟨9061856728115,9061856797319⟩,⟨4045365363828,4045365394728⟩,⟨-56540010308753,-56540010298333⟩,⟨-35408439141203,-35408439058832⟩,⟨-11267744841060,-11267744838893⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-281272070244,-281272042823⟩,⟨9061856728115,9061856797319⟩,⟨4045365363828,4045365394728⟩,⟨-56540010308753,-56540010298333⟩,⟨-35408439141203,-35408439058832⟩,⟨-11267744841060,-11267744838893⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12173989196,-12173988007⟩,⟨422813684949,422813690954⟩,⟨63186560426,63186572687⟩,⟨-4418820798360,-4418820782680⟩,⟨1913909923531,1913909985522⟩,⟨2731220473225,2731220497945⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439164232924,439164391524⟩,⟨903703182522,903706464214⟩,⟨-65348679194,-65345608574⟩,⟨-19206770053162,-19206675500876⟩,⟨-5603270264821,-5603161256055⟩,⟨-1279553532399,-1279426627493⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100840757003,-100840757001⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4364579408,4364579410⟩,⟨26896305346,26896305352⟩,⟨40119652736,40119652738⟩,⟨-285533704033,-285533704024⟩,⟨247233542879,247233542884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9486752595,9486752830⟩,⟨10872259596,10872261050⟩,⟨87203183662,87203185778⟩,⟨-794277256654,-794277241135⟩,⟨99938903425,99938916483⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1476889229221,1476889250334⟩,⟨-7442836708750,-7442836328554⟩,⟨-1397691594464,-1397691526436⟩,⟨109325154174443,109325161748680⟩,⟨23260253532986,23260255070023⟩,⟨5172076806231,5172077098363⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12742823608,12742824106⟩,⟨-49614053856,-49614046821⟩,⟨105073821045,105073826449⟩,⟨-270810941743,-270810789721⟩,⟨-269185129128,-269185044433⟩,⟨-177078715281,-177078695483⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12742824106,-12742823608⟩,⟨49614046821,49614053856⟩,⟨-105073826449,-105073821045⟩,⟨270810789721,270810941743⟩,⟨269185044433,269185129128⟩,⟨177078695483,177078715281⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113583581109,-113583580609⟩,⟨-825270791375,-825270784338⟩,⟨-105073826449,-105073821045⟩,⟨2469834045273,2469834197295⟩,⟨269185044433,269185129128⟩,⟨177078695483,177078715281⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨84275312788,84275314467⟩,⟨-553085057662,-553085053415⟩,⟨622323371540,622323386940⟩,⟨3450886010923,3450886011675⟩,⟨-3543479859066,-3543479819890⟩,⟨-2454878895724,-2454878895443⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨113200532492,113200536366⟩,⟨-1313394732587,-1313394675753⟩,⟨728788823715,728788863701⟩,⟨20502767257424,20502768512191⟩,⟨-6486399094762,-6486398461707⟩,⟨-4483206971862,-4483206777892⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-113200536366,-113200532492⟩,⟨1313394675753,1313394732587⟩,⟨-728788863701,-728788823715⟩,⟨-20502768512191,-20502767257424⟩,⟨6486398461707,6486399094762⟩,⟨4483206777892,4483206971862⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨986311091410,986311095284⟩,⟨1313394675753,1313394732587⟩,⟨-728788863701,-728788823715⟩,⟨-20502768512191,-20502767257424⟩,⟨6486398461707,6486399094762⟩,⟨4483206777892,4483206971862⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122579090971,122579091457⟩,⟨786570589092,786570598616⟩,⟨187695970405,187695976475⟩,⟨-2454748409909,-2454748175896⟩,⟨-682770426100,-682770300586⟩,⟨-166293284577,-166293236659⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11733600134,11733600239⟩,⟨170506992902,170506995108⟩,⟨21709021570,21709022784⟩,⟨728576659834,728576714618⟩,⟨102116871418,102116898624⟩,⟨-16503193823,-16503187502⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172193400120,172193552114⟩,⟨1673082178994,1673087599179⟩,⟨113453684362,113456504297⟩,⟨-1829199962211,-1828990456754⟩,⟨431465891751,431607910043⟩,⟨-572241519071,-572127850424⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172193552114,-172193400120⟩,⟨-1673087599179,-1673082178994⟩,⟨-113456504297,-113453684362⟩,⟨1828990456754,1829199962211⟩,⟨-431607910043,-431465891751⟩,⟨572127850424,572241519071⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56542324732,56542536627⟩,⟨-66144951994,-66137883709⟩,⟨127830762037,127834513274⟩,⟨-2061203513729,-2060940093242⟩,⟨-1720290656507,-1720106070073⟩,⟨440256324496,440408774314⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28574542688537,28574568222527⟩,⟨-253300693432218,-253300059554459⟩,⟨-85694431985776,-85693967676419⟩,⟨3623743647546163,3623766101706311⟩,⟨1351211465399708,1351230668379292⟩,⟨311518634829742,311537507691375⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13665734098,13665734207⟩,⟨175381697400,175381700220⟩,⟨41850583204,41850584724⟩,⟨578061120507,578061202112⟩,⟨116311187422,116311227952⟩,⟨27004166561,27004181541⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355150498174,355150818368⟩,⟨1409636614199,1409648663904⟩,⟨22540867361,22547658119⟩,⟨-20745267894110,-20744769391570⟩,⟨-3493534428091,-3493193109000⟩,⟨-1949921745174,-1949650545872⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355150818368,-355150498174⟩,⟨-1409648663904,-1409636614199⟩,⟨-22547658119,-22540867361⟩,⟨20744769391570,20745267894110⟩,⟨3493193109000,3493534428091⟩,⟨1949650545872,1949921745174⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84013414556,84013893350⟩,⟨-505945481382,-505930149985⟩,⟨-87896337313,-87886475935⟩,⟨1537999338408,1538592393234⟩,⟨-2110077155821,-2109626827964⟩,⟨670097013473,670495117681⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237488450634,237488450639⟩,⟨1569768188358,1569768188367⟩,⟨310207623117,310207623121⟩,⟨-3945612726766,-3945612726762⟩,⟨-1559413873708,-1559413873700⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1666867789472,-1666866325727⟩,⟨-4084762614759,-4084720974805⟩,⟨443703496880,443729344920⟩,⟨40817313351759,40818825251182⟩,⟨-7573524312561,-7572368223022⟩,⟨2118714697895,2119769239467⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185830812564,-185830648640⟩,⟨-1647836766200,-1647831060586⟩,⟨-235082194279,-235079053335⟩,⟨2427603148031,2427834990623⟩,⟨-189136966431,-188981351262⟩,⟨639794447957,639921138384⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51657638070,51657801999⟩,⟨-78068577842,-78062872219⟩,⟨75125428838,75128569786⟩,⟨-1518009578735,-1517777736139⟩,⟨-1748550840139,-1748395224962⟩,⟨291720148072,291846838502⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4320385203,4320426017⟩,⟨-31072464350,-31071009537⟩,⟨5247436030,5248302390⟩,⟨-17539946655,-17479777419⟩,⟨-293495849699,-293452764809⟩,⟨47661077624,47696412516⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2426997135,2427012539⟩,⟨-7335713484,-7335154076⟩,⟨7059138102,7059455644⟩,⟨-131555182147,-131531324072⟩,⟨-174971271344,-174954901896⟩,⟨37677462177,37690312085⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4297971268,4297998634⟩,⟨-30394860467,-30393759088⟩,⟨4731577655,4732189553⟩,⟨-39268042278,-39217202612⟩,⟨-277960794832,-277927357399⟩,⟨39162529108,39187431359⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4297998634,-4297971268⟩,⟨30393759088,30394860467⟩,⟨-4732189553,-4731577655⟩,⟨39217202612,39268042278⟩,⟨277927357399,277960794832⟩,⟨-39187431359,-39162529108⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨22386569,22454749⟩,⟨-678705262,-676149070⟩,⟨515246477,516724735⟩,⟨21677255957,21788264859⟩,⟨-15568492300,-15491969977⟩,⟨8473646265,8533883408⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56542324732,56542536627⟩,⟨-66144951994,-66137883709⟩,⟨127830762037,127834513274⟩,⟨-2061203513729,-2060940093242⟩,⟨-1720290656507,-1720106070073⟩,⟨440256324496,440408774314⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨22386569,22454749⟩,⟨-678705262,-676149070⟩,⟨515246477,516724735⟩,⟨21677255957,21788264859⟩,⟨-15568492300,-15491969977⟩,⟨8473646265,8533883408⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112098646425,112528143156⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨117682103910,121547574477⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112528143156,-112098646425⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437227670732,437657167463⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46797024132,48381632185⟩,⟨-121547574477,-117682103910⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158895670557,160909775341⟩,⟨977964053299,981829523866⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46367527401,48811128916⟩,⟨-121547574477,-117682103910⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2126866256768,-2113016791872⟩,⟨6682520349496,6793973518601⟩,⟨2987617793489,3028459761794⟩,⟨-41980525721956,-40614466544347⟩,⟨-26321403288856,-25670961368815⟩,⟨-8341492983894,-8118022451504⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311259620100,-305362136753⟩,⟨-933502208015,-885154544372⟩,⟨-414837567265,-397049580194⟩,⟨5743870507899,6264221768992⟩,⟨3575661191040,3825673021711⟩,⟨1155340738224,1237763736951⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305362136753,311259620100⟩,⟨885154544372,933502208015⟩,⟨397049580194,414837567265⟩,⟨-6264221768992,-5743870507899⟩,⟨-3825673021711,-3575661191040⟩,⟨-1237763736951,-1155340738224⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160909775341,-158895670557⟩,⟨-981829523866,-977964053299⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938601852435,940615957219⟩,⟨-981829523866,-977964053299⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173975734208,-171618867968⟩,⟨-1150150061162,-1143168835161⟩,⟨-512687188244,-511087340444⟩,⟨-1203120667188,-1188559495570⟩,⟨748949912562,756626493841⟩,⟨-239059002515,-237569356215⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148833670906,-146503032181⟩,⟨-831289450603,-820515082564⟩,⟨-370351001429,-367040954602⟩,⟨1004338225593,1039478256262⟩,⟨1374544378176,1391291197013⟩,⟨201962704816,205345174780⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146503032181,148833670906⟩,⟨820515082564,831289450603⟩,⟨367040954602,370351001429⟩,⟨-1039478256262,-1004338225593⟩,⟨-1391291197013,-1374544378176⟩,⟨-205345174780,-201962704816⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨451865168934,460093291006⟩,⟨1705669626936,1764791658618⟩,⟨764090534796,785188568694⟩,⟨-7303700025254,-6748208733492⟩,⟨-5216964218724,-4950205569216⟩,⟨-1443108911731,-1357303443040⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨813518152362,823631376722⟩,⟨4088513152875,4161684260107⟩,⟨764090534796,785188568694⟩,⟨-19396283759209,-18632317224392⟩,⟨-5216964218724,-4950205569216⟩,⟨-1443108911731,-1357303443040⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92735054802,97622257832⟩,⟨-243095148954,-235364207820⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12383710912475,13036341243297⟩,⟨29856739369851,34173391314871⟩,⟨-123048359540084,-110927593717358⟩,⟨143967328065004,179163870009883⟩,⟨-366163072286272,-225755588039527⟩,⟨1987276856653337,2322875491356231⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9162589431891,9765371656281⟩,⟨68139310674060,74941830005210⟩,⟨-83568205334370,-72764692017768⟩,⟨98591775915574,183049891600454⟩,⟨-781136523363636,-610866257657157⟩,⟨1277513188885650,1570576602376743⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨85435517440,91002513152⟩,⟨-737416502597,-590610856041⟩,⟨630702257141,822298757606⟩,⟨6315591174569,11053315613517⟩,⟨-7983763521408,-981484144116⟩,⟨-6198111460870,3733934486683⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1184947145216,1190514140928⟩,⟨-737416502597,-590610856041⟩,⟨630702257141,822298757606⟩,⟨6315591174569,11053315613517⟩,⟨-7983763521408,-981484144116⟩,⟨-6198111460870,3733934486683⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨82278724416,87432239488⟩,⟨-684248257312,-545464754581⟩,⟨582491582040,763010442402⟩,⟨5407007954127,9985760237263⟩,⟨-7119156087300,-431623031631⟩,⟨-6280717406140,3156126882829⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨88672040518,94668682763⟩,⟨-799519696096,-632045713808⟩,⟨674949764701,891550501603⟩,⟨6885759136334,12609013376157⟩,⟨-9366710675192,-1164387364370⟩,⟨-6625159714247,4855542116730⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-91002513152,-85435517440⟩,⟨590610856041,737416502597⟩,⟨-822298757606,-630702257141⟩,⟨-11053315613517,-6315591174569⟩,⟨981484144116,7983763521408⟩,⟨-3733934486683,6198111460870⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1008509114624,1014076110336⟩,⟨590610856041,737416502597⟩,⟨-822298757606,-630702257141⟩,⟨-11053315613517,-6315591174569⟩,⟨981484144116,7983763521408⟩,⟨-3733934486683,6198111460870⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-94990097408,-88937455552⟩,⟨640369590692,803957056375⟩,⟨-896498635842,-683838676724⟩,⟨-12638557310457,-7220636686162⟩,⟨1462450165297,9359691030011⟩,⟨-4801834737723,6332084302713⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-87609067578,-81576431107⟩,⟨523660949992,693713643932⟩,⟨-775821532076,-556199028619⟩,⟨-10457686552393,-4589692237524⟩,⟨-550853592767,7818365046398⟩,⟨-4179662856460,7503587448372⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1062972940,13092251656⟩,⟨-275858746104,61667930124⟩,⟨-100871767375,335351472984⟩,⟨-3571927416059,8019321138633⟩,⟨-9917564267959,6653977682028⟩,⟨-10804822570707,12359129565102⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨531486470,6546125828⟩,⟨-137929373052,30833965062⟩,⟨-50435883688,167675736492⟩,⟨-1785963708030,4009660569317⟩,⟨-4958782133980,3326988841014⟩,⟨-5402411285354,6179564782551⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6546125828,-531486470⟩,⟨-30833965062,137929373052⟩,⟨-167675736492,50435883688⟩,⟨-4009660569317,1785963708030⟩,⟨-3326988841014,4958782133980⟩,⟨-6179564782551,5402411285354⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755577257788,761591916410⟩,⟨-30833965062,137929373052⟩,⟨-167675736492,50435883688⟩,⟨-4009660569317,1785963708030⟩,⟨-3326988841014,4958782133980⟩,⟨-6179564782551,5402411285354⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6638608865,7531941629⟩,⟨-122066476208,-91784648414⟩,⟨98015104756,136117257178⟩,⟨1615984698604,2818819844462⟩,⟨-2424565934752,-830101645456⟩,⟨-302422236152,1848043519194⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7531941629,-6638608865⟩,⟨91784648414,122066476208⟩,⟨-136117257178,-98015104756⟩,⟨-2818819844462,-1615984698604⟩,⟨830101645456,2424565934752⟩,⟨-1848043519194,302422236152⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091979686147,1092873018911⟩,⟨91784648414,122066476208⟩,⟨-136117257178,-98015104756⟩,⟨-2818819844462,-1615984698604⟩,⟨830101645456,2424565934752⟩,⟨-1848043519194,302422236152⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7557857984,-6658731072⟩,⟨92342190205,122908431041⟩,⟨-137056127424,-98610493179⟩,⟨-2852001950382,-1633556260418⟩,⟨843425837138,2456610164201⟩,⟨-1877874715208,295664243592⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3778928992,-3329365536⟩,⟨46171095102,61454215521⟩,⟨-68528063712,-49305246589⟩,⟨-1426000975191,-816778130209⟩,⟨421712918569,1228305082101⟩,⟨-938937357604,147832121796⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3329365536,3778928992⟩,⟨-61454215521,-46171095102⟩,⟨49305246589,68528063712⟩,⟨816778130209,1426000975191⟩,⟨-1228305082101,-421712918569⟩,⟨-147832121796,938937357604⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765452749152,765902331872⟩,⟨-61454215521,-46171095102⟩,⟨49305246589,68528063712⟩,⟨816778130209,1426000975191⟩,⟨-1228305082101,-421712918569⟩,⟨-147832121796,938937357604⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272994921536,273218254728⟩,⟨22946162103,30516619052⟩,⟨-34029314295,-24503776189⟩,⟨-704704961116,-403996174651⟩,⟨207525411364,606141483688⟩,⟨-462010879799,75605559038⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530905498304,1531804663744⟩,⟨-122908431042,-92342190204⟩,⟨98610493178,137056127424⟩,⟨1633556260418,2852001950382⟩,⟨-2456610164202,-843425837138⟩,⟨-295664243592,1877874715208⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1192145054293,1198725725018⟩,⟨-876501876779,-694320479363⟩,⟨741451818968,977393917516⟩,⟨8233353615132,14419887196637⟩,⟨-10918925138630,-2017492015092⟩,⟨-6444859312263,6032055481344⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1284778480810,1297939822260⟩,⟨-1753003753559,-1388640958726⟩,⟨1482903637936,1954787835033⟩,⟨16466707230274,28839774393271⟩,⟨-21837850277258,-4034984030185⟩,⟨-12885048936957,12064110962686⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨171216179968,182422336896⟩,⟨-1500218161623,-1176346433585⟩,⟨1256198295805,1672904696458⟩,⟨11902329383341,23422488087351⟩,⟨-17344819239323,-1135539430774⟩,⟨-13572327946732,8889235590157⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨58710733342,63034147743⟩,⟨-513333739689,-394448044464⟩,⟨419536598669,573750984437⟩,⟨3823156549090,7845408577821⟩,⟨-5862312800959,-48439191719⟩,⟨-5055468691900,3108938521566⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380104599015,380638991203⟩,⟨1407514634,19587378499⟩,⟨-22924813033,-60690365⟩,⟨-583003641079,142337041841⟩,⟨-317380439441,642652922245⟩,⟨-725612281776,567570115271⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176043042237,3180508267323⟩,⟨-163896515362,-11744269934⟩,⟨506399018,191822349867⟩,⟨-1190911989611,4895148628340⟩,⟨-5397139449192,2655662916519⟩,⟨-4749117446100,6094666705102⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨169591490826,182336068993⟩,⟨-1494293683338,-1140027490549⟩,⟨1211898075983,1670660920108⟩,⟨10983700707070,23127736846124⟩,⟨-17442146677936,7663030959⟩,⟨-14895605667957,9542685180459⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨340807670794,364758405889⟩,⟨-2994511844961,-2316373924134⟩,⟨2468096371788,3343565616566⟩,⟨22886030090411,46550224933475⟩,⟨-34786965917259,-1127876399815⟩,⟨-28467933614689,18431920770616⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519227789924,527527160686⟩,⟨-42715143614,191077370896⟩,⟨-232285829936,69870223004⟩,⟨-5562429553920,2508750249014⟩,⟨-4651038064392,6882191843570⟩,⟨-8576104772632,7535250764080⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356809968869,365398974523⟩,⟨-44380851366,198528570423⟩,⟨-241343982966,72594862611⟩,⟨-5787378163651,2642535617152⟩,⟨-4876117643541,7163715278653⟩,⟨-8926518981152,7882228739154⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713619937738,730797949046⟩,⟨-88761702732,397057140846⟩,⟨-482687965932,145189725222⟩,⟨-11574756327302,5285071234304⟩,⟨-9752235287082,14327430557306⟩,⟨-17853037962304,15764457478308⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523373556675,1525166054879⟩,⟨-31123782628,29724286004⟩,⟨-37506764000,39041022668⟩,⟨-1185263584044,1236017251778⟩,⟨-1626508518746,1581140097614⟩,⟨-2143707762786,2180296951360⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988720551200,1013712085169⟩,⟨-143810696038,570526499647⟩,⟨-694480301669,227345971982⟩,⟨-16865969410430,8174078717997⟩,⟨-14635286054077,20952692714034⟩,⟨-26223600777131,23349439367951⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67781208767,67892155782⟩,⟨11394487450,15166183218⟩,⟨-16911926398,-12167959462⟩,⟨-349267308084,-198920388286⟩,⟨101162957016,300218108664⟩,⟨-228518494982,39680913907⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50150669013,50857224538⟩,⟨260473812830,268334643322⟩,⟨34435094524,39480518103⟩,⟨-1374564825488,-1180990328407⟩,⟨-303378986663,-114689475211⟩,⟨-284443449564,-70860612673⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131556943584,2134061585701⟩,⟨-342464241628,-257145378252⟩,⟨274600727054,381884483764⟩,⟨4564476223011,7974115525984⟩,⟨-6875583967690,-2365252222084⟩,⟨-806132152998,5266559362550⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2967874247479,2973106793155⟩,⟨-715665449877,-537054720684⟩,⟨573510664552,798043993075⟩,⟨9565420142434,16721349895165⟩,⟨-14432300864078,-4974483359863⟩,⟨-1647682138199,11077208639892⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135369990910,137519200285⟩,⟨669985422757,701087535491⟩,⟨119108311774,143669330207⟩,⟨-3629876543727,-2668827362496⟩,⟨-1377734611242,-358530349566⟩,⟨-809431644257,378408986010⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8790960223075,8930530404028⟩,⟨-46251636049461,-42829039067199⟩,⟨-9478048368882,-7614038104299⟩,⟨587926767388244,718546357604381⟩,⟨97109458828411,189065418463425⟩,⟨-11774760378328,73517502393060⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7905148811310,8233643345678⟩,⟨-43810494585678,-33879447857984⟩,⟨-14379192747953,-5000252564351⟩,⟨343695916733480,740966192934190⟩,⟨-46028935986059,374948698483579⟩,⟨-227770645484792,269404240153282⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15810297622620,16467286691356⟩,⟨-87620989171356,-67758895715968⟩,⟨-28758385495906,-10000505128702⟩,⟨687391833466960,1481932385868380⟩,⟨-92057871972118,749897396967158⟩,⟨-455541290969584,538808480306564⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10743319721704,10784481866367⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239228,2075048233589864⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9643808093928,9684970238591⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239235,2075048233589852⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2387534470720,2392217527616⟩,⟨-12060075023605,-11917323006543⟩,⟨0,0⟩,⟨100606314842521,107411991083576⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7513066356923,7608299303416⟩,⟨-47012312269537,-45662290010343⟩,⟨-20956056956564,-20414673355491⟩,⟨555044939026108,580985951469092⟩,⟨299486697564410,311625636026920⟩,⟨110942421752307,115441389896307⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6413554729147,6508787675640⟩,⟨-47012312269538,-45662290010343⟩,⟨-20956056956565,-20414673355490⟩,⟨555044939026115,580985951469093⟩,⟨299486697564413,311625636026923⟩,⟨110942421752308,115441389896308⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1939041057728,1955247388416⟩,⟨-8059584142020,-7713605254772⟩,⟨-3592614278533,-3448594707661⟩,⟨34684264049745,45487010027762⟩,⟨24257067143387,29230171158393⟩,⟨7002462069002,8974320832637⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100626050579,101055547311⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135641831301,137655936086⟩,⟨691154949828,698610404824⟩,⟨309191259649,311223385853⟩,⟨-1753486165281,-1739706366688⟩,⟨-1563348634180,-1555479113230⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4326575528448,4347464916032⟩,⟨-20119659165625,-19630928261315⟩,⟨-3592614278533,-3448594707661⟩,⟨135290578892266,152899001111338⟩,⟨24257067143387,29230171158393⟩,⟨7002462069002,8974320832637⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨681615341588,729516811778⟩,⟨-5989023689922,-4632747848268⟩,⟨4936192743576,6687131233132⟩,⟨45772060180822,93100449866950⟩,⟨-69573931834518,-2255752799630⟩,⟨-56935867229378,36863841541232⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5008190870036,5076981727810⟩,⟨-26108682855547,-24263676109583⟩,⟨1343578465043,3238536525471⟩,⟨181062639073088,245999450978288⟩,⟨-45316864691131,26974418358763⟩,⟨-49933405160376,45838162373869⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458343918396,466622775268⟩,⟨1583441209584,1821169448772⟩,⟨122962769255,297652223770⟩,⟨-35153235648182,-26001108735535⟩,⟨-3096484941442,5057383582942⟩,⟨-4589353545802,4212961890901⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33708324860,35733088443⟩,⟨-727598223557,-686618979605⟩,⟨317856335867,320395012775⟩,⟨8435558648415,9118158477382⟩,⟨-6530975501168,-6467144718132⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨492052243256,502355863711⟩,⟨855842986027,1134550469167⟩,⟨440819105122,618047236545⟩,⟨-26717676999767,-16882950258153⟩,⟨-9627460442610,-1409761135190⟩,⟨-4589353545802,4212961890901⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505357813684,506349053570⟩,⟨2517543755956,2557704464203⟩,⟨0,0⟩,⟨2303354216540,4586136051397⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226157177048,231345817288⟩,⟨1520011203763,1691074786799⟩,⟨202609389084,284624214407⟩,⟨-7354042756614,-385961260776⟩,⟨-3424314943726,789758242630⟩,⟨-2113497270707,1940160715262⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-729516811778,-681615341588⟩,⟨4632747848268,5989023689922⟩,⟨-6687131233132,-4936192743576⟩,⟨-93100449866950,-45772060180822⟩,⟨2255752799630,69573931834518⟩,⟨-36863841541232,56935867229378⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3597058716670,3665849574444⟩,⟨-15486911317357,-13641904571393⟩,⟨-10279745511665,-8384787451237⟩,⟨42190129025316,107126940930516⟩,⟨26512819943017,98804102992911⟩,⟨-29861379472230,65910188062015⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443753043897,458954632196⟩,⟨322197285983,646275781701⟩,⟨-275475827490,3247070373⟩,⟨-20321663140527,-9430101596189⟩,⟨-12856780472502,-1825650019630⟩,⟨-10719697178873,2398435711112⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨317791341114,321819550682⟩,⟨1955928106598,1963659047732⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-321819550682,-317791341114⟩,⟨-1963659047732,-1955928106598⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨777692077094,781720286662⟩,⟨-1963659047732,-1955928106598⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1371496971619,1390123133177⟩,⟨-9222075869452,-8905257888840⟩,⟨-4110802848198,-3981358160221⟩,⟨51975977833847,61127747504698⟩,⟨33304724587943,37524652107740⟩,⟨10438310161163,12100592548092⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1390123133177,-1371496971619⟩,⟨8905257888840,9222075869452⟩,⟨3981358160221,4110802848198⟩,⟨-61127747504698,-51975977833847⟩,⟨-37524652107740,-33304724587943⟩,⟨-12100592548092,-10438310161163⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-290611505401,-271985343843⟩,⟨8905257888840,9222075869452⟩,⟨3981358160221,4110802848198⟩,⟨-61127747504698,-51975977833847⟩,⟨-37524652107740,-33304724587943⟩,⟨-12100592548092,-10438310161163⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12901251153,-11469899512⟩,⟨404654744370,441526078916⟩,⟨52220935049,74336102817⟩,⟨-4752615742243,-4098161793848⟩,⟨1692931132523,2130806022143⟩,⟨2629236702578,2832390263089⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430851792744,447484732684⟩,⟨726852030353,1087801860617⟩,⟨-223254892441,77583173190⟩,⟨-25074278882770,-13528263390037⟩,⟨-11163849339979,305156002513⟩,⟨-8090460476295,5230825974201⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101055547311,-100626050579⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4243503242,4486205715⟩,⟨25705299179,28088102686⟩,⟨40014577925,40224844809⟩,⟨-291148786570,-279923151333⟩,⟨246677084567,247790085082⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9214554908,9760678899⟩,⟨6610489777,15117305111⟩,⟨86889653291,87517563587⟩,⟨-861343558887,-726805038805⟩,⟨94437742819,105411467849⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1467799617379,1486046520419⟩,⟨-7602112375568,-7286169773323⟩,⟨-1434297116781,-1361691439049⟩,⟨105542008784755,113210704095579⟩,⟨22340694002072,24204542870588⟩,⟨4945368364121,5404814096054⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12301025133,13192059592⟩,⟨-58661410992,-40630577847⟩,⟨103261196502,106872712706⟩,⟨-488690482655,-52860858758⟩,⟨-311525423985,-226641620331⟩,⟨-186885708818,-167237102828⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13192059592,-12301025133⟩,⟨40630577847,58661410992⟩,⟨-106872712706,-103261196502⟩,⟨52860858758,488690482655⟩,⟨226641620331,311525423985⟩,⟨167237102828,186885708818⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114247606903,-112927075712⟩,⟨-834683757079,-815793930472⟩,⟨-106872712706,-103261196502⟩,⟨2251884114310,2687713738207⟩,⟨226641620331,311525423985⟩,⟨167237102828,186885708818⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨81771340206,86800202861⟩,⟨-573939340148,-532828593579⟩,⟨611583206071,632849354680⟩,⟨3113864435304,3801249584268⟩,⟨-3771286991742,-3311623589943⟩,⟨-2564756801804,-2344309297370⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨109161139213,117314938901⟩,⟨-1375852167012,-1253179537449⟩,⟨703207038137,754058644410⟩,⟨19067919964859,22011453002605⟩,⟨-7151286989598,-5814163283558⟩,⟨-4749696501353,-4217702154782⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-117314938901,-109161139213⟩,⟨1253179537449,1375852167012⟩,⟨-754058644410,-703207038137⟩,⟨-22011453002605,-19067919964859⟩,⟨5814163283558,7151286989598⟩,⟨4217702154782,4749696501353⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨982196688875,990350488563⟩,⟨1253179537449,1375852167012⟩,⟨-754058644410,-703207038137⟩,⟨-22011453002605,-19067919964859⟩,⟨5814163283558,7151286989598⟩,⟨4217702154782,4749696501353⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121169212049,123989251330⟩,⟨772009726123,801504369246⟩,⟨181795242402,193573161410⟩,⟨-2759671194781,-2158023687444⟩,⟨-817581515979,-546785472730⟩,⟨-220387496402,-111475730097⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11598353402,11871193859⟩,⟨167574804348,173459960510⟩,⟨21211208068,22209772706⟩,⟨652025618116,804717795220⟩,⟨88491693856,115707629362⟩,⟨-19442032306,-13576609946⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166777153224,177793802000⟩,⟨1463596874803,1883129953556⟩,⟨-5494127258,227142028797⟩,⟨-11019559817976,7398246355677⟩,⟨-6028337787628,6998095480436⟩,⟨-6371384102966,5236328514458⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177793802000,-166777153224⟩,⟨-1883129953556,-1463596874803⟩,⟨-227142028797,5494127258⟩,⟨-7398246355677,11019559817976⟩,⟨-6998095480436,6028337787628⟩,⟨-5236328514458,6371384102966⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48363375048,64568664064⟩,⟨-363118749793,227477911996⟩,⟨-24532639713,290118341665⟩,⟨-14752289112291,10633598557200⟩,⟨-10422410424162,6818096030258⟩,⟨-7349825785165,8311544818228⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27882211930008,29283564160843⟩,⟨-276522944593554,-230412911733694⟩,⟨-104946927815030,-67225026896708⟩,⟨2661709252963052,4601105985607427⟩,⟨467779005072203,2268412190452872⟩,⟨-646659402227986,1280497745672022⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13353181155,13981966227⟩,⟨170155199536,180767395580⟩,⟨40068673616,43657548960⟩,⟨461713083260,692895308258⟩,⟨70897613528,161701190790⟩,⟨10411585167,43588702176⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338619635752,372385152426⟩,⟨798508028453,2016139001921⟩,⟨-318469711440,346318005336⟩,⟨-46890633847864,5648910492070⟩,⟨-20754829826227,14352756087302⟩,⟨-16293345812978,12544727239851⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372385152426,-338619635752⟩,⟨-2016139001921,-798508028453⟩,⟨-346318005336,318469711440⟩,⟨-5648910492070,46890633847864⟩,⟨-14352756087302,20754829826227⟩,⟨-12544727239851,16293345812978⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58466640318,108865096932⟩,⟨-1289286971568,289293832164⟩,⟨-569572897777,396052884630⟩,⟨-30723189374840,33362370457827⟩,⟨-25516605427281,21059985828740⟩,⟨-20635187716146,21524171787179⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236267881880,238711483397⟩,⟨1565610291292,1573924739750⟩,⟨309191259649,311223385853⟩,⟨-3952509420833,-3938729622240⟩,⟨-1563348634180,-1555479113230⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1711076126115,-1623821550910⟩,⟨-5541699263413,-2626126399433⟩,⟨-573505348972,1503382438147⟩,⟨-21054510305005,102687259578189⟩,⟨-60877478539850,44579628678350⟩,⟨-51703121093292,55723809260951⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192953891970,-178949610773⟩,⟨-1872236802193,-1429554410924⟩,⟨-365914196663,-98952813910⟩,⟨-7266571578056,12186622997220⟩,⟨-7451182902207,6961171770858⟩,⟨-5867737008722,7156160934601⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43313989910,59761872624⟩,⟨-306626510901,144370328826⟩,⟨-56722937014,212270571943⟩,⟨-11219080998889,8247893374980⟩,⟨-9014531536387,5405692657628⟩,⟨-6216153144383,6808428302723⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2571727285,6393087344⟩,⟨-111666390916,39511834261⟩,⟨-35877118805,51983413002⟩,⟨-3798353004104,3863642609411⟩,⟨-3001396063539,2176257003879⟩,⟨-2240097355024,2295954402030⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1706304576,3248243429⟩,⟨-33332206818,15693951722⟩,⟨-6166135676,23075130016⟩,⟨-1300106414093,1067618305534⟩,⟨-1098329576572,643376348894⟩,⟨-697636210514,822079929477⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3009149286,5776309519⟩,⟨-83084343316,15937801596⟩,⟨-21578677116,35682419158⟩,⟨-2488214887493,2521572456433⟩,⟨-2135924986344,1384571886593⟩,⟨-1380524853404,1528701894132⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5776309519,-3009149286⟩,⟨-15937801596,83084343316⟩,⟨-35682419158,21578677116⟩,⟨-2521572456433,2488214887493⟩,⟨-1384571886593,2135924986344⟩,⟨-1528701894132,1380524853404⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3204582234,3383938058⟩,⟨-127604192512,122596177577⟩,⟨-71559537963,73562090118⟩,⟨-6319925460537,6351857496904⟩,⟨-4385967950132,4312181990223⟩,⟨-3768799249156,3676479255434⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48363375048,64568664064⟩,⟨-363118749793,227477911996⟩,⟨-24532639713,290118341665⟩,⟨-14752289112291,10633598557200⟩,⟨-10422410424162,6818096030258⟩,⟨-7349825785165,8311544818228⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3204582234,3383938058⟩,⟨-127604192512,122596177577⟩,⟨-71559537963,73562090118⟩,⟨-6319925460537,6351857496904⟩,⟨-4385967950132,4312181990223⟩,⟨-3768799249156,3676479255434⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (523/5120) u, BivariateJet2.affineZ (557/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000038

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000039Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2109398152640,-2109398113792⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2109398152640,-2109398113728⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-174597302144,-174597302080⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-174597302144,-174597302080⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨87179043520,87179043584⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-94691282432,-94691282368⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨87179166720,87179166784⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-94691427776,-94691427712⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7512261056,-7512260992⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7512238848,-7512238784⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨181870325888,181870325952⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨181870594432,181870594496⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2389873986368,2389874044224⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1934800811648,1934800850240⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1934800811712,1934800850304⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2506246686912,-2506246629056⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2116280894528,-2116280855616⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2102553117568,-2102553078720⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-175779629056,-175779628992⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-173417129152,-173417129088⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨84614299776,84614299840⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-91672874112,-91672874048⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨89765985920,89765985984⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-97751403968,-97751403904⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7985417984,-7985417920⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7058574272,-7058574208⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨176287173888,176287173952⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨187517389824,187517389888⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1926773449728,1926773488320⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1942863726528,1942863765120⟩



end LaneCBRB2Cell000039Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000039
open Set LaneCBRB2Cell000039Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112313394790,112313394791⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨123480309760,123480309760⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112313394791,-112313394790⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437442419097,437442419098⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49126834175,49126834177⟩,⟨-123480309760,-123480309760⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161440228965,161440228968⟩,⟨976031318016,976031318016⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49126834174,49126834178⟩,⟨-123480309760,-123480309760⟩,⟨437442419097,437442419098⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2109398152640,-2109398113728⟩,⟨6647400032148,6647400032274⟩,⟨2979263776780,2979263776844⟩,⟨-40188685660785,-40188685659279⟩,⟨-25500339022296,-25500339021439⟩,⟨-8072686479874,-8072686479534⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309720890752,-309720885032⟩,⟨-896471534298,-896471499717⟩,⟨-401784931876,-401784916373⟩,⟨5900865848628,5900865849184⟩,⟨3654564975174,3654565014397⟩,⟨1185304748639,1185304748769⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309720885032,309720890752⟩,⟨896471499717,896471534298⟩,⟨401784916373,401784931876⟩,⟨-5900865849184,-5900865848628⟩,⟨-3654565014397,-3654564975174⟩,⟨-1185304748769,-1185304748639⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161440228968,-161440228965⟩,⟨-976031318016,-976031318016⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938071398808,938071398811⟩,⟨-976031318016,-976031318016⟩,⟨-437442419098,-437442419097⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-174597302144,-174597302080⟩,⟨-1144004373864,-1144004373859⟩,⟨-512725392643,-512725392639⟩,⟨-1190297559716,-1190297559704⟩,⟨755262104514,755262104526⟩,⟨-239094632217,-239094632213⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148961349124,-148961349068⟩,⟨-821042111389,-821042111323⟩,⟨-367978609660,-367978609627⟩,⟨1015527320144,1015527320168⟩,⟨1380058253269,1380058253354⟩,⟨203988598591,203988598601⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148961349068,148961349124⟩,⟨821042111323,821042111389⟩,⟨367978609627,367978609660⟩,⟨-1015527320168,-1015527320144⟩,⟨-1380058253354,-1380058253269⟩,⟨-203988598601,-203988598591⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨458682234100,458682239876⟩,⟨1717513611040,1717513645687⟩,⟨769763526000,769763541536⟩,⟨-6916393169352,-6916393168772⟩,⟨-5034623267751,-5034623228443⟩,⟨-1389293347370,-1389293347230⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨821277079698,821277091446⟩,⟨4107387597396,4107387689987⟩,⟨769763526000,769763541536⟩,⟨-18904857512315,-18904857511238⟩,⟨-5034623267751,-5034623228443⟩,⟨-1389293347370,-1389293347230⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98253668348,98253668356⟩,⟨-246960619520,-246960619520⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12304129096069,12304129097072⟩,⟨30926431501868,30926431506911⟩,⟨-109560245181973,-109560245163859⟩,⟨155467186335897,155467186373919⟩,⟨-275379703225038,-275379703044187⟩,⟨1951125061618536,1951125062104622⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9190534194428,9190534326644⟩,⟨69064296071961,69064297446062⟩,⟨-73221644655689,-73221643296976⟩,⟨135630681829309,135630688794508⟩,⟨-649661214776982,-649661201520694⟩,⟨1288435017473831,1288435041808535⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨90728392704,90728526080⟩,⟨-675120097081,-675118071791⟩,⟨715757018424,715759164668⟩,⟨8671961211191,8672011140055⟩,⟨-4249076828679,-4249009115148⟩,⟨-1357111980562,-1357022637153⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1190240020480,1190240153856⟩,⟨-675120097081,-675118071791⟩,⟨715757018424,715759164668⟩,⟨8671961211191,8672011140055⟩,⟨-4249076828679,-4249009115148⟩,⟨-1357111980562,-1357022637153⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨87179043520,87179166784⟩,⟨-623657736351,-623655795556⟩,⟨661196954135,661199010871⟩,⟨7657175939752,7657225162072⟩,⟨-3550143958374,-3550078632878⟩,⟨-1651280095364,-1651194948195⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨94372795997,94372940008⟩,⟨-728649763561,-728647350694⟩,⟨772508509262,772511066337⟩,⟨9742482804992,9742546629758⟩,⟨-4991972991385,-4991891037904⟩,⟨-1034294696638,-1034189827893⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-90728526080,-90728392704⟩,⟨675118071791,675120097081⟩,⟨-715759164668,-715757018424⟩,⟨-8672011140055,-8671961211191⟩,⟨4249009115148,4249076828679⟩,⟨1357022637153,1357111980562⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1008783101696,1008783235072⟩,⟨675118071791,675120097081⟩,⟨-715759164668,-715757018424⟩,⟨-8672011140055,-8671961211191⟩,⟨4249009115148,4249076828679⟩,⟨1357022637153,1357111980562⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-94691427776,-94691282368⟩,⟨735837139484,735839444216⟩,⟨-780133532092,-780131089671⟩,⟨-9944414279788,-9944355525861⟩,⟨5153253290595,5153330976334⟩,⟨925545089525,925646129834⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-86877775944,-86877631047⟩,⟨616975727096,616978194615⟩,⟨-654117391927,-654114776917⟩,⟨-7473359236254,-7473293136329⟩,⟨3404053163493,3404137330829⟩,⟨1747990591433,1748097505872⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7495020053,7495308961⟩,⟨-111674036465,-111669156079⟩,⟨118391117335,118396289420⟩,⟨2269123568738,2269253493429⟩,⟨-1587919827892,-1587753707075⟩,⟨713695894795,713907677979⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3747510026,3747654481⟩,⟨-55837018233,-55834578039⟩,⟨59195558667,59198144710⟩,⟨1134561784369,1134626746715⟩,⟨-793959913946,-793876853537⟩,⟨356847947397,356953838990⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3747654481,-3747510026⟩,⟨55834578039,55837018233⟩,⟨-59198144710,-59195558667⟩,⟨-1134626746715,-1134561784369⟩,⟨793876853537,793959913946⟩,⟨-356953838990,-356847947397⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758375729135,758375892854⟩,⟨55834578039,55837018233⟩,⟨-59198144710,-59195558667⟩,⟨-1134626746715,-1134561784369⟩,⟨793876853537,793959913946⟩,⟨-356953838990,-356847947397⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7486634097,7486656109⟩,⟨-111417923718,-111417425684⟩,⟨118124232990,118124760846⟩,⟨2260235329487,2260250647614⟩,⟨-1580221350388,-1580203871980⟩,⟨707913094995,707933757576⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7486656109,-7486634097⟩,⟨111417425684,111417923718⟩,⟨-118124760846,-118124232990⟩,⟨-2260250647614,-2260235329487⟩,⟨1580203871980,1580221350388⟩,⟨-707933757576,-707913094995⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092024971667,1092024993679⟩,⟨111417425684,111417923718⟩,⟨-118124760846,-118124232990⟩,⟨-2260250647614,-2260235329487⟩,⟨1580203871980,1580221350388⟩,⟨-707933757576,-707913094995⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7512261056,-7512238784⟩,⟨112181274041,112181777752⟩,⟨-118934595315,-118934061442⟩,⟨-2287192137819,-2287176566013⟩,⟨1603171968208,1603189707475⟩,⟨-725652379149,-725631445042⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3756130528,-3756119392⟩,⟨56090637020,56090888876⟩,⟨-59467297658,-59467030721⟩,⟨-1143596068910,-1143588283006⟩,⟨801585984104,801594853738⟩,⟨-362826189575,-362815722521⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3756119392,3756130528⟩,⟨-56090888876,-56090637020⟩,⟨59467030721,59467297658⟩,⟨1143588283006,1143596068910⟩,⟨-801594853738,-801585984104⟩,⟨362815722521,362826189575⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765879503008,765879533408⟩,⟨-56090888876,-56090637020⟩,⟨59467030721,59467297658⟩,⟨1143588283006,1143596068910⟩,⟨-801594853738,-801585984104⟩,⟨362815722521,362826189575⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273006242916,273006248420⟩,⟨27854356421,27854480930⟩,⟨-29531190212,-29531058247⟩,⟨-565062661904,-565058832371⟩,⟨395050967995,395055337597⟩,⟨-176983439394,-176978273748⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531759006016,1531759066816⟩,⟨-112181777752,-112181274040⟩,⟨118934061442,118934595316⟩,⟨2287176566012,2287192137820⟩,⟨-1603189707476,-1603171968208⟩,⟨725631445042,725652379150⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1198399990785,1198400149232⟩,⟨-802019803596,-802017185540⟩,⟨850294864607,850297639118⟩,⟨11375477335768,11375546240250⟩,⟨-6185869236352,-6185780181889⟩,⟨-405591971291,-405477693239⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1297288353794,1297288670688⟩,⟨-1604039607191,-1604034371079⟩,⟨1700589729213,1700595278235⟩,⟨22750954671539,22751092480490⟩,⟨-12371738472699,-12371560363778⟩,⟨-811183796212,-810955532846⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨181870325888,181870594496⟩,⟨-1359497442773,-1359492672835⟩,⟨1441327765819,1441332820952⟩,⟨17601518801105,17601652106388⟩,⟨-8703486439165,-8703320419042⟩,⟨-2576936573973,-2576729688988⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62578884326,62578989831⟩,⟨-461049262308,-461047556728⟩,⟨488800460802,488802268302⟩,⟨5819191308405,5819235738029⟩,⟨-2792550986034,-2792493304068⟩,⟨-1042581184146,-1042506979283⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380332286372,380332309137⟩,⟨10950166159,10950466790⟩,⟨-11609633559,-11609314925⟩,⟨-224987074851,-224977779755⟩,⟨158313681815,158324257705⟩,⟨-72776523421,-72764058481⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178604053801,3178604244059⟩,⟨-91517868613,-91515345151⟩,⟨97024140720,97026815301⟩,⟨1885507704675,1885585903271⟩,⟨-1328772637572,-1328683784084⟩,⟨614044332437,614148906432⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨180910770178,180911086014⟩,⟨-1338067011295,-1338061848408⟩,⟨1418606906266,1418612377729⟩,⟨17006899637503,17007036118931⟩,⟨-8230050251516,-8229875285227⟩,⟨-2892807859160,-2892584450349⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨362781096066,362781680510⟩,⟨-2697564454068,-2697554521243⟩,⟨2859934672085,2859945198681⟩,⟨34608418438608,34608688225319⟩,⟨-16933536690681,-16933195704269⟩,⟨-5469744433133,-5469314139337⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523081095289,523081321137⟩,⟨77022539392,77025922214⟩,⟨-81662521280,-81658936260⟩,⟨-1559521610018,-1559431162356⟩,⟨1089122615228,1089237957040⟩,⟨-486035918924,-485889180635⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360789278635,360789512300⟩,⟨79688140164,79691657264⟩,⟨-84488721071,-84484993740⟩,⟨-1607627026824,-1607532585677⟩,⟨1120594377546,1120714500231⟩,⟨-496262252414,-496109748668⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721578557270,721579024600⟩,⟨159376280328,159383314528⟩,⟨-168977442142,-168969987480⟩,⟨-3215254053648,-3215065171354⟩,⟨2241188755092,2241429000462⟩,⟨-992524504828,-992219497336⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524272349907,1524272432719⟩,⟨-764352068,-763350322⟩,⟨809300596,810362326⟩,⟨26925918398,26956808333⟩,⟨-22985835496,-22950617820⟩,⟨17697687466,17739284155⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000337072703,1000337774919⟩,⟨220444523542,220454944927⟩,⟨-233725297997,-233714253611⟩,⟨-4439914485144,-4439631808281⟩,⟨3092149127190,3092505792755⟩,⟨-1364588875391,-1364138319779⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67786830796,67786833531⟩,⟨13832347022,13832409132⟩,⟨-14665055372,-14664989542⟩,⟨-279196269327,-279194349321⟩,⟨194684261364,194686448622⟩,⟨-86302864331,-86300283142⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50633180251,50633183019⟩,⟨263559720810,263559783279⟩,⟨36503257313,36503309515⟩,⟨-1270717173547,-1270715222954⟩,⟨-210074067035,-210072125407⟩,⟨-170649957168,-170647932178⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133934369804,2133934539209⟩,⟨-312566872170,-312565456292⟩,⟨331380433154,331381933818⟩,⟨6395544808733,6395588654262⟩,⟨-4491162443796,-4491112622478⟩,⟨2047523252190,2047581891172⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2972840947399,2972841301403⟩,⟨-653167908830,-653164924157⟩,⟨692482394108,692485557517⟩,⟨13412542125836,13412634711374⟩,⟨-9435853564737,-9435748623713⟩,⟨4332457050212,4332580242196⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136901136599,136901160386⟩,⟨682529534823,682529927674⟩,⟨130586125973,130586426291⟩,⟨-3131225110187,-3131213624581⟩,⟨-858214195619,-858203094152⟩,⟨-215908072248,-215896582392⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8830646987987,8830648522341⟩,⟨-44025798813658,-44025758174018⟩,⟨-8423325481529,-8423303182711⟩,⟨640961715800788,640963261025199⟩,⟨139347211671570,139348232276844⟩,⟨29995652005363,29996480273388⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8034133823490,8034140859246⟩,⟨-38284271664864,-38284122567042⟩,⟨-9540705493239,-9540590797753⟩,⟨529834353170035,529839295736306⟩,⟨159281937745122,159286359316279⟩,⟨19911431097498,19916003024193⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16068267646980,16068281718492⟩,⟨-76568543329728,-76568245134084⟩,⟨-19081410986478,-19081181595506⟩,⟨1059668706340070,1059678591472612⟩,⟨318563875490244,318572718632558⟩,⟨39822862194996,39832006048386⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10763861442032,10763861442129⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311394,2063168215367208⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9664349814256,9664349814353⟩,⟨-105374704749331,-105374704747430⟩,⟨0,0⟩,⟨2063168215311405,2063168215367197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2389873986368,2389874044224⟩,⟨-11988464342936,-11988464342527⟩,⟨0,0⟩,⟨104010778944236,104010778977589⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7488380234236,7488380234376⟩,⟨-45273062834591,-45273062832896⟩,⟨-20290699448657,-20290699447851⟩,⟨547421512839495,547421512870214⟩,⟨296346689407470,296346689423707⟩,⟨109960357568579,109960357575253⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6388868606460,6388868606600⟩,⟨-45273062834592,-45273062832895⟩,⟨-20290699448658,-20290699447850⟩,⟨547421512839502,547421512870215⟩,⟨296346689407473,296346689423709⟩,⟨109960357568579,109960357575253⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1934800811648,1934800850304⟩,⟨-7791404406332,-7791404405833⟩,⟨-3491989169574,-3491989169342⟩,⟨38998388091294,38998388108347⟩,⟨26255601121995,26255601130353⟩,⟨7833591845607,7833591849175⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100840757001,100840757003⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137736116275,137736116279⟩,⟨689411849008,689411849014⟩,⟨308983924405,308983924411⟩,⟨-1732836851712,-1732836851712⟩,⟨-1553262339690,-1553262339682⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4324674798016,4324674894528⟩,⟨-19779868749268,-19779868748360⟩,⟨-3491989169574,-3491989169342⟩,⟨143009167035530,143009167085936⟩,⟨26255601121995,26255601130353⟩,⟨7833591845607,7833591849175⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨725562192132,725563361020⟩,⟨-5395128908136,-5395109042486⟩,⟨5719869344170,5719890397362⟩,⟨69216836877216,69217376450638⟩,⟨-33867073381362,-33866391408538⟩,⟨-10939488866266,-10938628278674⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5050236990148,5050238255548⟩,⟨-25174997657404,-25174977790846⟩,⟨2227880174596,2227901228020⟩,⟨212226003912746,212226543536574⟩,⟨-7611472259367,-7610790278185⟩,⟨-3105897020659,-3105036429499⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463178113132,463178229198⟩,⟨1709586240981,1709589069965⟩,⟨204328101348,204330032249⟩,⟨-30700000920056,-30699917281880⟩,⟨1074651628664,1074730928272⟩,⟨-284854656217,-284775727838⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35839135354,35839137415⟩,⟨-729863422451,-729863412040⟩,⟨319124126993,319124145312⟩,⟨9056632116758,9056632144571⟩,⟨-6498957778804,-6498957686573⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨499017248486,499017366613⟩,⟨979722818530,979725657925⟩,⟨523452228341,523454177561⟩,⟨-21643368803298,-21643285137309⟩,⟨-5424306150140,-5424226758301⟩,⟨-284854656217,-284775727838⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505853361827,505853374074⟩,⟨2537541677330,2537541800300⟩,⟨0,0⟩,⟨3442964323895,3442967248197⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229583340802,229583400708⟩,⟨1602414292529,1602415938201⟩,⟨240825165257,240826067868⟩,⟨-3872717191762,-3872663436172⟩,⟨-1287500456377,-1287459312966⟩,⟨-131053356171,-131017040342⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-725563361020,-725562192132⟩,⟨5395109042486,5395128908136⟩,⟨-5719890397362,-5719869344170⟩,⟨-69217376450638,-69216836877216⟩,⟨33866391408538,33867073381362⟩,⟨10938628278674,10939488866266⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3599111436996,3599112702396⟩,⟨-14384759706782,-14384739840224⟩,⟨-9211879566936,-9211858513512⟩,⟨73791790584892,73792330208720⟩,⟨60121992530533,60122674511715⟩,⟨18772220124281,18773080715441⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450861654255,450861812787⟩,⟨454719279282,454722561473⟩,⟨-142555053578,-142552060552⟩,⟨-14467266783128,-14467172276283⟩,⟨-7371304394938,-7371198391257⟩,⟨-3965207124479,-3965087084387⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨322880457930,322880457936⟩,⟨1952062636032,1952062636032⟩,⟨874884838194,874884838196⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-322880457936,-322880457930⟩,⟨-1952062636032,-1952062636032⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨776631169840,776631169846⟩,⟨-1952062636032,-1952062636032⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1366630947593,1366630974909⟩,⟨-8938422949427,-8938422880401⟩,⟨-4006065467107,-4006065436160⟩,⟨55211769550532,55211769564564⟩,⟨34814323371122,34814323455307⟩,⟨11090367804983,11090367807930⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1366630974909,-1366630947593⟩,⟨8938422880401,8938422949427⟩,⟨4006065436160,4006065467107⟩,⟨-55211769564564,-55211769550532⟩,⟨-34814323455307,-34814323371122⟩,⟨-11090367807930,-11090367804983⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-267119347133,-267119319817⟩,⟨8938422880401,8938422949427⟩,⟨4006065436160,4006065467107⟩,⟨-55211769564564,-55211769550532⟩,⟨-34814323455307,-34814323371122⟩,⟨-11090367807930,-11090367804983⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11935051473,-11935050251⟩,⟨429372807935,429372814121⟩,⟨72719539252,72719551519⟩,⟨-4474548329377,-4474548313043⟩,⟨1817860198253,1817860260405⟩,⟨2692114549641,2692114574447⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438926602782,438926762536⟩,⟨884092087217,884095375594⟩,⟨-69835514326,-69832509033⟩,⟨-18941815112505,-18941720589326⟩,⟨-5553444196685,-5553338130852⟩,⟨-1273092574838,-1272972509940⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100840757003,-100840757001⟩,⟨-874884838196,-874884838194⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4505625063,4505625064⟩,⟨27765485770,27765485775⟩,⟨40119652736,40119652738⟩,⟨-294761005061,-294761005051⟩,⟨247233542879,247233542884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9793326289,9793326530⟩,⟨11223607304,11223608791⟩,⟨87203183662,87203185778⟩,⟨-819945103257,-819945087361⟩,⟨99938903425,99938916483⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1472007233863,1472007254920⟩,⟨-7361832721128,-7361832344549⟩,⟨-1379677511677,-1379677444357⟩,⟨107520209273603,107520216724986⟩,⟨22823894704961,22823896215441⟩,⟨5076362958524,5076363245407⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13111136596,13111137107⟩,⟨-50545714255,-50545707079⟩,⟨104457362601,104457368008⟩,⟨-290344641550,-290344487026⟩,⟨-260868173682,-260868089239⟩,⟨-173631697104,-173631677445⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13111137107,-13111136596⟩,⟨50545707079,50545714255⟩,⟨-104457368008,-104457362601⟩,⟨290344487026,290344641550⟩,⟨260868089239,260868173682⟩,⟨173631677445,173631697104⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113951894110,-113951893597⟩,⟨-824339131117,-824339123939⟩,⟨-104457368008,-104457362601⟩,⟨2489367742578,2489367897102⟩,⟨260868089239,260868173682⟩,⟨173631677445,173631697104⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86448052237,86448053972⟩,⟨-565411792745,-565411788350⟩,⟨613739370812,613739386218⟩,⟨3492493673374,3492493674392⟩,⟨-3469340624406,-3469340585047⟩,⟨-2428577146948,-2428577146567⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨115735163714,115735167693⟩,⟨-1335780665020,-1335780607081⟩,⟨713187871540,713187911391⟩,⟨20700847200872,20700848470802⟩,⟨-6250024063552,-6250023436149⟩,⟨-4392465005022,-4392464813613⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-115735167693,-115735163714⟩,⟨1335780607081,1335780665020⟩,⟨-713187911391,-713187871540⟩,⟨-20700848470802,-20700847200872⟩,⟨6250023436149,6250024063552⟩,⟨4392464813613,4392465005022⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨983776460083,983776464062⟩,⟨1335780607081,1335780665020⟩,⟨-713187911391,-713187871540⟩,⟨-20700848470802,-20700847200872⟩,⟨6250023436149,6250024063552⟩,⟨4392464813613,4392465005022⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123237940801,123237941304⟩,⟨784177592659,784177602424⟩,⟨187118874492,187118880612⟩,⟨-2468525623436,-2468525385330⟩,⟨-678623510019,-678623384487⟩,⟨-162029627135,-162029579471⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11809819674,11809819782⟩,⟨170866777150,170866779408⟩,⟨21651638722,21651639942⟩,⟨720077522136,720077578017⟩,⟨102558020936,102558048158⟩,⟨-16142294338,-16142288044⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172588755398,172588908119⟩,⟨1674627500986,1674632931165⟩,⟨111464306468,111467067151⟩,⟨-1892791367131,-1892582059828⟩,⟨447378516632,447516886340⟩,⟨-559671927578,-559564334551⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172588908119,-172588755398⟩,⟨-1674632931165,-1674627500986⟩,⟨-111467067151,-111464306468⟩,⟨1892582059828,1892791367131⟩,⟨-447516886340,-447378516632⟩,⟨559564334551,559671927578⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56994432683,56994645310⟩,⟨-72218638636,-72211562785⟩,⟨129358098106,129361761400⟩,⟨-1980135131934,-1979872069041⟩,⟨-1735017342717,-1734837829598⟩,⟨428510978380,428654887236⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28275187364810,28275212691245⟩,⟨-248600703093452,-248600075947863⟩,⟨-84609378915299,-84608929893447⟩,⟨3519774268830286,3519796426456646⟩,⟨1322663916649879,1322682397786908⟩,⟨305757671821035,305775320959495⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13813032685,13813032799⟩,⟨175787921292,175787924200⟩,⟨41946158994,41946160538⟩,⟨565193624315,565193707810⟩,⟨114782349998,114782390818⟩,⟨27367196730,27367211733⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355217787041,355218108146⟩,⟨1397444744104,1397456772563⟩,⟨15755521170,15762176857⟩,⟨-20738562360603,-20738066617273⟩,⟨-3443037462485,-3442705168215⟩,⟨-1910688162990,-1910430893248⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355218108146,-355217787041⟩,⟨-1397456772563,-1397444744104⟩,⟨-15762176857,-15755521170⟩,⟨20738066617273,20738562360603⟩,⟨3442705168215,3443037462485⟩,⟨1910430893248,1910688162990⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83708494636,83708975495⟩,⟨-513364685346,-513349368510⟩,⟨-85597691183,-85588030203⟩,⟨1796251504768,1796841771277⟩,⟨-2110739028470,-2110300668367⟩,⟨637338318410,637715653050⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238576873276,238576873282⟩,⟨1564296687202,1564296687210⟩,⟨308983924405,308983924411⟩,⟨-3931860107264,-3931860107264⟩,⟨-1553262339690,-1553262339682⟩,⟨-348074299885,-348074299882⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1665294927912,-1665293462062⟩,⟨-4111477090135,-4111435495053⟩,⟨451006015419,451031213953⟩,⟨41367315811052,41368823037662⟩,⟨-7624098503268,-7622976478242⟩,⟨2034873922929,2035867881031⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186653340807,-186653175745⟩,⟨-1648529138226,-1648523413947⟩,⟨-232855263831,-232852180531⟩,⟨2510737893512,2510969905138⟩,⟨-204761179500,-204609242392⟩,⟨626991047640,627111325610⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51923532469,51923697537⟩,⟨-84232451024,-84226726737⟩,⟨76128660574,76131743880⟩,⟨-1421122213752,-1420890202126⟩,⟨-1758023519190,-1757871582074⟩,⟨278916747755,279037025728⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4339124791,4339165906⟩,⟨-32109152388,-32107688859⟩,⟨5411276663,5412129477⟩,⟨9786865615,9847323201⟩,⟨-296283052209,-296240797781⟩,⟨45518944364,45552614476⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2452046122,2452061714⟩,⟨-7955641760,-7955075816⟩,⟨7190226786,7190540860⟩,⟨-121318914343,-121294820452⟩,⟨-177707706574,-177691563400⟩,⟨36885313909,36897611704⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4314843706,4314871230⟩,⟨-31375372497,-31374265839⟩,⟨4864963259,4865565707⟩,⟨-13769446762,-13718470783⟩,⟨-279846472063,-279813663450⟩,⟨36703097231,36726844913⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4314871230,-4314843706⟩,⟨31374265839,31375372497⟩,⟨-4865565707,-4864963259⟩,⟨13718470783,13769446762⟩,⟨279813663450,279846472063⟩,⟨-36726844913,-36703097231⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨24253561,24322200⟩,⟨-734886549,-732316362⟩,⟨545710956,547166218⟩,⟨23505336398,23616769963⟩,⟨-16469388759,-16394325718⟩,⟨8792099451,8849517245⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56994432683,56994645310⟩,⟨-72218638636,-72211562785⟩,⟨129358098106,129361761400⟩,⟨-1980135131934,-1979872069041⟩,⟨-1735017342717,-1734837829598⟩,⟨428510978380,428654887236⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨24253561,24322200⟩,⟨-734886549,-732316362⟩,⟨545710956,547166218⟩,⟨23505336398,23616769963⟩,⟨-16469388759,-16394325718⟩,⟨8792099451,8849517245⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112098646425,112528143156⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121547574476,125413045044⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112528143156,-112098646425⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437227670732,437657167463⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨48334152662,49920270665⟩,⟨-125413045044,-121547574476⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160432799087,162448413821⟩,⟨974098582732,977964053300⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47904655931,50349767396⟩,⟨-125413045044,-121547574476⟩,⟨437227670732,437657167463⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2116280894528,-2102553078720⟩,⟨6593063564745,6702387879971⟩,⟨2959320418388,2999443675755⟩,⟨-40856323988529,-39534358774084⟩,⟨-25819370714556,-25187045836745⟩,⟨-8182416753721,-7964970189903⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312671977114,-306789366412⟩,⟨-920320416558,-872479808262⟩,⟨-410576325284,-392937652329⟩,⟨5645727216747,6154351465316⟩,⟨3531390930616,3776898098682⟩,⟨1144665406261,1225647414668⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306789366412,312671977114⟩,⟨872479808262,920320416558⟩,⟨392937652329,410576325284⟩,⟨-6154351465316,-5645727216747⟩,⟨-3776898098682,-3531390930616⟩,⟨-1225647414668,-1144665406261⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162448413821,-160432799087⟩,⟨-977964053300,-974098582732⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937063213955,939078828689⟩,⟨-977964053300,-974098582732⟩,⟨-437657167463,-437227670732⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175779629056,-173417129088⟩,⟨-1147502998878,-1140514177929⟩,⟨-513529010039,-511923912315⟩,⟨-1197589092438,-1183045778868⟩,⟨751409392219,759107573501⟩,⟨-239844706950,-238347722188⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150131134580,-147795446844⟩,⟨-826430907581,-815660062118⟩,⟨-369638158946,-366320684427⟩,⟨998003021263,1033044725875⟩,⟨1371677234510,1388446912984⟩,⟨202291187703,205684428962⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147795446844,150131134580⟩,⟨815660062118,826430907581⟩,⟨366320684427,369638158946⟩,⟨-1033044725875,-998003021263⟩,⟨-1388446912984,-1371677234510⟩,⟨-205684428962,-202291187703⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨454584813256,462803111694⟩,⟨1688139870380,1746751324139⟩,⟨759258336756,780214484230⟩,⟨-7187396191191,-6643730238010⟩,⟨-5165345011666,-4903068165126⟩,⟨-1431331843630,-1346956593964⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨816237796684,826341197410⟩,⟨4070983396319,4143643925628⟩,⟨759258336756,780214484230⟩,⟨-19279979925146,-18527838728910⟩,⟨-5165345011666,-4903068165126⟩,⟨-1431331843630,-1346956593964⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95809311862,100699534792⟩,⟨-250826090088,-243095148952⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12005277105914,12618040941114⟩,⟨28981510513432,33033677127217⟩,⟨-115278482850907,-104251511317365⟩,⟨139926458045092,172962479617509⟩,⟨-341426766122090,-213729377122278⟩,⟨1810600041310296,2106369549825448⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8912284950849,9483125777705⟩,⟨65964821308118,72379186359407⟩,⟨-78347741534250,-68438790179969⟩,⟨97228788921734,176672779651731⟩,⟨-730306118683986,-574754727597406⟩,⟨1164094738224918,1424361190089535⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨87955249664,93532098816⟩,⟨-752148213226,-605817060187⟩,⟨628537845588,814172095175⟩,⟨6456946349671,11157579978390⟩,⟨-7765723739946,-1014732899357⟩,⟨-5875046994003,3428917565119⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1187466877440,1193043726592⟩,⟨-752148213226,-605817060187⟩,⟨628537845588,814172095175⟩,⟨6456946349671,11157579978390⟩,⟨-7765723739946,-1014732899357⟩,⟨-5875046994003,3428917565119⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨84614299776,89765985984⟩,⟨-696436862338,-558322287048⟩,⟨579261811044,753866657390⟩,⟨5509608411086,10047630871190⟩,⟨-6896375313861,-457676601465⟩,⟨-5956763775023,2869763145782⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨91383006603,97402104475⟩,⟨-817087271159,-649606599059⟩,⟨673969683400,884466178078⟩,⟨7062508141689,12766105673297⟩,⟨-9148438104201,-1210710337041⟩,⟨-6280864087978,4510281974792⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-93532098816,-87955249664⟩,⟨605817060187,752148213226⟩,⟨-814172095175,-628537845588⟩,⟨-11157579978390,-6456946349671⟩,⟨1014732899357,7765723739946⟩,⟨-3428917565119,5875046994003⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1005979528960,1011556378112⟩,⟨605817060187,752148213226⟩,⟨-814172095175,-628537845588⟩,⟨-11157579978390,-6456946349671⟩,⟨1014732899357,7765723739946⟩,⟨-3428917565119,5875046994003⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-97751403968,-91672874048⟩,⟨658493106655,822080054759⟩,⟨-889870678166,-683189473839⟩,⟨-12809619477771,-7412749414331⟩,⟨1512123786293,9153087041719⟩,⟨-4467926512045,5996781513593⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-89931796678,-83874542409⟩,⟨535607834008,705807298488⟩,⟨-766280654208,-552689161583⟩,⟨-10520918966382,-4665483145547⟩,⟨-524391093963,7583425411220⟩,⟨-3851739868158,7139787924876⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1451209925,13527562066⟩,⟨-281479437151,56200699429⟩,⟨-92310970808,331777016495⟩,⟨-3458410824693,8100622527750⟩,⟨-9672829198164,6372715074179⟩,⟨-10132603956136,11650069899668⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨725604962,6763781033⟩,⟨-140739718576,28100349715⟩,⟨-46155485404,165888508248⟩,⟨-1729205412347,4050311263875⟩,⟨-4836414599082,3186357537090⟩,⟨-5066301978068,5825034949834⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6763781033,-725604962⟩,⟨-28100349715,140739718576⟩,⟨-165888508248,46155485404⟩,⟨-4050311263875,1729205412347⟩,⟨-3186357537090,4836414599082⟩,⟨-5825034949834,5066301978068⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755359602583,761397797918⟩,⟨-28100349715,140739718576⟩,⟨-165888508248,46155485404⟩,⟨-4050311263875,1729205412347⟩,⟨-3186357537090,4836414599082⟩,⟨-5825034949834,5066301978068⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7035965557,7956490217⟩,⟨-127965906366,-96924469796⟩,⟨100559560690,138518271086⟩,⟨1700639838720,2927333858218⟩,⟨-2435122090660,-854979653622⟩,⟨-280935005605,1789139891289⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7956490217,-7035965557⟩,⟨96924469796,127965906366⟩,⟨-138518271086,-100559560690⟩,⟨-2927333858218,-1700639838720⟩,⟨854979653622,2435122090660⟩,⟨-1789139891289,280935005605⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091555137559,1092475662219⟩,⟨96924469796,127965906366⟩,⟨-138518271086,-100559560690⟩,⟨-2927333858218,-1700639838720⟩,⟨854979653622,2435122090660⟩,⟨-1789139891289,280935005605⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7985417984,-7058574208⟩,⟨97548700847,128898666836⟩,⟨-139527949142,-101207203131⟩,⟨-2963782715970,-1720247139987⟩,⟨869465158831,2469229250516⟩,⟨-1819887256376,273666916704⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3992708992,-3529287104⟩,⟨48774350423,64449333418⟩,⟨-69763974571,-50603601565⟩,⟨-1481891357985,-860123569993⟩,⟨434732579415,1234614625258⟩,⟨-909943628188,136833458352⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3529287104,3992708992⟩,⟨-64449333418,-48774350423⟩,⟨50603601565,69763974571⟩,⟨860123569993,1481891357985⟩,⟨-1234614625258,-434732579415⟩,⟨-136833458352,909943628188⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765652670720,766116111872⟩,⟨-64449333418,-48774350423⟩,⟨50603601565,69763974571⟩,⟨860123569993,1481891357985⟩,⟨-1234614625258,-434732579415⟩,⟨-136833458352,909943628188⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272888784389,273118915555⟩,⟨24231117449,31991476592⟩,⟨-34629567772,-25139890172⟩,⟨-731833464555,-425159959680⟩,⟨213744913405,608780522665⟩,⟨-447284972823,70233751402⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531305341440,1532232223744⟩,⟨-128898666836,-97548700846⟩,⟨101207203130,139527949142⟩,⟨1720247139986,2963782715970⟩,⟨-2469229250516,-869465158830⟩,⟨-273666916704,1819887256376⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1195114623142,1201739980599⟩,⟨-898513889349,-715749357370⟩,⟨742593083998,972607423605⟩,⟨8485950493811,14672407096500⟩,⟨-10731302434579,-2088339602654⟩,⟨-6095481527950,5670500056602⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1290717618508,1303968333422⟩,⟨-1797027778698,-1431498714740⟩,⟨1485186167996,1945214847210⟩,⟨16971900987624,29344814192984⟩,⟨-21462604869146,-4176679205307⟩,⟨-12186282350505,11341000113199⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨176287173888,187517389888⟩,⟨-1530817360656,-1207045786052⟩,⟨1252315274281,1657052102150⟩,⟨12179467362677,23672597300019⟩,⟨-16908355940494,-1214729223291⟩,⟨-12878325403715,8234597745047⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨60424865688,64769787126⟩,⟨-523243468656,-404221330022⟩,⟨417691077842,567730112212⟩,⟨3898792837848,7912025733095⟩,⟨-5701100189380,-68002131927⟩,⟨-4809589133480,2873811497085⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380056056341,380606801016⟩,⟨1728563324,20371248800⟩,⟨-23139572478,-353907984⟩,⟨-600402912180,139778399943⟩,⟨-311210679052,640696502152⟩,⟨-700085043002,545306988939⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176311659138,3180914497861⟩,⟨-170499060774,-14425532662⟩,⟨2953499655,193668803172⟩,⟨-1169757283749,5043405712148⟩,⟨-5383130485725,2604679884777⟩,⟨-4563992049206,5883009762200⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨174557685919,187380605797⟩,⟨-1523800095339,-1168522962229⟩,⟨1206804431865,1653865940137⟩,⟨11204682262504,23349059771265⟩,⟨-16990734228820,-49577180708⟩,⟨-14180871672585,8860564019297⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨350844859807,374897995685⟩,⟨-3054617455995,-2375568748281⟩,⟨2459119706146,3310918042287⟩,⟨23384149625181,47021657071284⟩,⟨-33899090169314,-1264306403999⟩,⟨-27059197076300,17095161764344⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518928690520,527258277248⟩,⟨-38918268536,194920925066⟩,⟨-229751358130,63924171534⟩,⟨-5616771727562,2430935385735⟩,⟨-4455492151622,6710127009842⟩,⟨-8081452412117,7066755946395⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356501704518,365119641384⟩,⟨-40425607898,202470386895⟩,⟨-238649833794,66400011893⟩,⟨-5841786747993,2562513098910⟩,⟨-4672170308879,6982289868064⟩,⟨-8408921106856,7392453234498⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713003409036,730239282768⟩,⟨-80851215796,404940773790⟩,⟨-477299667588,132800023786⟩,⟨-11683573495986,5125026197820⟩,⟨-9344340617758,13964579736128⟩,⟨-16817842213712,14784906468996⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523348851223,1525196258187⟩,⟨-31974197040,30417205520⟩,⟨-37311067956,38968388452⟩,⟨-1207086718232,1263142877250⟩,⟨-1614249596894,1565656931830⟩,⟨-2062806807993,2100822261981⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨987850329759,1012957201655⟩,⟨-133389027284,581918349158⟩,⟨-686870111661,210095411058⟩,⟨-17032198256742,7970540229711⟩,⟨-14061123427462,20439138205485⟩,⟨-24732846010739,21936652125657⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67728513973,67842795065⟩,⟨12027885868,15893378794⟩,⟨-17203983582,-12478984114⟩,⟨-362507153393,-209180016085⟩,⟨104083917140,301334345806⟩,⟨-221061732454,37073501487⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50279207260,50987452151⟩,⟨259696454031,267618578922⟩,⟨33839640742,38877363170⟩,⟨-1373002009861,-1176786658728⟩,⟨-297976953625,-110479986131⟩,⟨-278872506889,-72342620413⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132670532521,2135253077977⟩,⟨-359255301964,-271714901202⟩,⟨281905396596,388880325388⟩,⟨4808933923584,8290623096214⟩,⟨-6914738318454,-2439790974846⟩,⟨-744109220944,5107645750091⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2970200310283,2975597064438⟩,⟨-750964159424,-567631759021⟩,⟨588920428873,812890401549⟩,⟨10082364914652,17393359565741⟩,⟨-14522508116617,-5134412900103⟩,⟨-1516522878843,10750717247023⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135823317581,137986819886⟩,⟨666714858376,698296374113⟩,⟨118344327105,142909428338⟩,⟨-3620253989657,-2640511338824⟩,⟨-1367316140620,-352852821529⟩,⟨-788784872471,360601623781⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8761168788536,8900723683868⟩,⟨-45760501113667,-42331589443705⟩,⟨-9365088087306,-7514012032374⟩,⟨576722942921676,707769962845827⟩,⟨95014944715433,185898251604149⟩,⟨-10742035631368,71397718288548⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7871425147486,8200051666350⟩,⟨-43238003880785,-33321866939111⟩,⟨-14188185098441,-5050167658662⟩,⟨331837607885265,727679575574026⟩,⟨-42161825817504,366445251293873⟩,⟨-213691759811872,255058794429911⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15742850294972,16400103332700⟩,⟨-86476007761570,-66643733878222⟩,⟨-28376370196882,-10100335317324⟩,⟨663675215770530,1455359151148052⟩,⟨-84323651635008,732890502587746⟩,⟨-427383519623744,510117588859822⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10743319721704,10784481866367⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239228,2075048233589864⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9643808093928,9684970238591⟩,⟨-105778825969536,-104972894989945⟩,⟨0,0⟩,⟨2051378711239235,2075048233589852⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2387534470720,2392217527616⟩,⟨-12060075023605,-11917323006543⟩,⟨0,0⟩,⟨100606314842521,107411991083576⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7441905963740,7535403150070⟩,⟨-45934207031422,-44624320309409⟩,⟨-20556415004412,-20029787510993⟩,⟨535166655633472,560010216728981⟩,⟨290581091457895,302258226107813⟩,⟨107819795006902,112154901182601⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6342394335964,6435891522294⟩,⟨-45934207031423,-44624320309408⟩,⟨-20556415004412,-20029787510993⟩,⟨535166655633473,560010216728976⟩,⟨290581091457893,302258226107812⟩,⟨107819795006901,112154901182602⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1926773449728,1942863765120⟩,⟨-7963111731731,-7623646062341⟩,⟨-3563641130715,-3421901098525⟩,⟨33756093867842,44223041034433⟩,⟨23833707874095,28672888799342⟩,⟨6869836827327,8793426401652⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100626050579,101055547311⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136729499296,138745114031⟩,⟨685689191787,693133165859⟩,⟨307966960202,310000287878⟩,⟨-1739706366693,-1725980926276⟩,⟨-1557197100160,-1549327579210⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4314307920448,4335081292736⟩,⟨-20023186755336,-19540969068884⟩,⟨-3563641130715,-3421901098525⟩,⟨134362408710363,151635032118009⟩,⟨23833707874095,28672888799342⟩,⟨6869836827327,8793426401652⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨701689719614,749795991370⟩,⟨-6109234911990,-4751137496562⟩,⟨4918239412292,6621836084574⟩,⟨46768299250362,94043314142568⟩,⟨-67798180338628,-2528612807998⟩,⟨-54118394152600,34190323528688⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5015997640062,5084877284106⟩,⟨-26132421667326,-24292106565446⟩,⟨1354598281577,3199934986049⟩,⟨181130707960725,245678346260577⟩,⟨-43964472464533,26144275991344⟩,⟨-47248557325273,42983749930340⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459058385088,467348451780⟩,⟨1587468209408,1824853128886⟩,⟨123971290300,294104376167⟩,⟨-35200593813165,-26091457038636⟩,⟨-2963423070724,4950355181314⟩,⟨-4342590564339,3950614313626⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34825788541,36859477160⟩,⟨-750558684312,-709355035256⟩,⟨317856335867,320395012775⟩,⟨8714277307219,9406473708370⟩,⟨-6530975501168,-6467144718132⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨493884173629,504207928940⟩,⟨836909525096,1115498093630⟩,⟨441827626167,614499388942⟩,⟨-26486316505946,-16684983330266⟩,⟨-9494398571892,-1516789536818⟩,⟨-4342590564339,3950614313626⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨505357813684,506349053570⟩,⟨2517543755956,2557704464203⟩,⟨0,0⟩,⟨2303354216540,4586136051397⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226999169352,232198733667⟩,⟨1515503559256,1686609061568⟩,⟨203072925783,282990353308⟩,⟨-7330362134891,-375886546907⟩,⟨-3360727850695,732312752191⟩,⟨-1999857542883,1819343941611⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-749795991370,-701689719614⟩,⟨4751137496562,6109234911990⟩,⟨-6621836084574,-4918239412292⟩,⟨-94043314142568,-46768299250362⟩,⟨2528612807998,67798180338628⟩,⟨-34190323528688,54118394152600⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3564511929078,3633391573122⟩,⟨-15272049258774,-13431734156894⟩,⟨-10185477215289,-8340140510817⟩,⟨40319094567795,104866732867647⟩,⟨26362320682093,96471069137970⟩,⟨-27320486701361,62911820554252⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443264008297,458490220019⟩,⟨295790494299,620193457449⟩,⟨-286884909923,-12724560711⟩,⟨-19990104687081,-9115431264915⟩,⟨-12594347616865,-1812606292054⟩,⟨-10342335401077,2139345415973⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨320865598174,324896827642⟩,⟨1948197165464,1955928106600⟩,⟨874455341464,875314334926⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-324896827642,-320865598174⟩,⟨-1955928106600,-1948197165464⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨774614800134,778646029602⟩,⟨-1955928106600,-1948197165464⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1357427418647,1375886455907⟩,⟨-9095444673843,-8784921778099⟩,⟨-4070381257203,-3943143902158⟩,⟨50797735823879,59648885710491⟩,⟨32770948134171,36869901415685⟩,⟨10282816827462,11901264667121⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1375886455907,-1357427418647⟩,⟨8784921778099,9095444673843⟩,⟨3943143902158,4070381257203⟩,⟨-59648885710491,-50797735823879⟩,⟨-36869901415685,-32770948134171⟩,⟨-11901264667121,-10282816827462⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-276374828131,-257915790871⟩,⟨8784921778099,9095444673843⟩,⟨3943143902158,4070381257203⟩,⟨-59648885710491,-50797735823879⟩,⟨-36869901415685,-32770948134171⟩,⟨-11901264667121,-10282816827462⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12655990132,-11237141025⟩,⟨411262311862,448030307290⟩,⟨61788821295,83832518637⟩,⟨-4806390594337,-4155499413986⟩,⟨1598639236818,2033087473964⟩,⟨2591038846453,2792392716332⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430608018165,447253078994⟩,⟨707052806161,1068223764739⟩,⟨-225096088628,71107957926⟩,⟨-24796495281418,-13270930678901⟩,⟨-10995708380047,220481181910⟩,⟨-7751296554624,4931738132305⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101055547311,-100626050579⟩,⟨-875314334926,-874455341464⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4384179492,4627621185⟩,⟨26572523304,28959239703⟩,⟨40014577925,40224844809⟩,⟨-300380617449,-289145922512⟩,⟨246677084567,247790085082⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9520026344,10068357833⟩,⟨6942497466,15487892306⟩,⟨86889653291,87517563587⟩,⟨-887667595280,-751816094842⟩,⟨94437742819,105411467849⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1462986262095,1481095122679⟩,⟨-7518802527035,-7207425698604⟩,⟨-1415729425827,-1344220183546⟩,⟨103817399512412,111322907907409⟩,⟨21925225948912,23746663844531⟩,⟨4854895007975,5303704187292⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12667140032,13562562963⟩,⟨-59613026589,-41541935177⟩,⟨102649481621,106251559391⟩,⟨-508659081992,-71970876751⟩,⟨-302920028973,-218614009514⟩,⟨-183339263204,-163889180649⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13562562963,-12667140032⟩,⟨41541935177,59613026589⟩,⟨-106251559391,-102649481621⟩,⟨71970876751,508659081992⟩,⟨218614009514,302920028973⟩,⟨163889180649,183339263204⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114618110274,-113293190611⟩,⟨-833772399749,-814842314875⟩,⟨-106251559391,-102649481621⟩,⟨2270994132303,2707682337544⟩,⟨218614009514,302920028973⟩,⟨163889180649,183339263204⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨83947651697,88969262521⟩,⟨-586261452856,-545153653487⟩,⟨603004232686,624261936041⟩,⟨3156260788632,3841683801722⟩,⟨-3695863480739,-3238872937002⟩,⟨-2537680299368,-2318804690393⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨111698919834,119845881990⟩,⟨-1398121907470,-1275656148172⟩,⟨687787638034,738279760274⟩,⟨19273194967692,22200933332257⟩,⟨-6906929977196,-5585956437164⟩,⟨-4655303986250,-4130609956549⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-119845881990,-111698919834⟩,⟨1275656148172,1398121907470⟩,⟨-738279760274,-687787638034⟩,⟨-22200933332257,-19273194967692⟩,⟨5585956437164,6906929977196⟩,⟨4130609956549,4655303986250⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨979665745786,987812707942⟩,⟨1275656148172,1398121907470⟩,⟨-738279760274,-687787638034⟩,⟨-22200933332257,-19273194967692⟩,⟨5585956437164,6906929977196⟩,⟨4130609956549,4655303986250⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121826093981,124650056755⟩,⟨769583530075,799144193492⟩,⟨181236802943,192977826793⟩,⟨-2773383873692,-2171809102178⟩,⟨-812470078819,-543614739310⟩,⟨-215666233774,-107677626165⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11673680127,11948314935⟩,⟨167921981658,173832480610⟩,⟨21153914144,22152294972⟩,⟨643228423285,796514074820⟩,⟨88990454858,116091794556⟩,⟨-19057704432,-13238849184⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167144206562,178218760617⟩,⟨1464584823606,1885285212503⟩,⟨-5481437532,223182581002⟩,⟨-11087556171805,7339719467029⟩,⟨-5870732813184,6871123166999⟩,⟨-6072027334208,4965209093411⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178218760617,-167144206562⟩,⟨-1885285212503,-1464584823606⟩,⟨-223182581002,5481437532⟩,⟨-7339719467029,11087556171805⟩,⟨-6871123166999,5870732813184⟩,⟨-4965209093411,6072027334208⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48780408735,65054527105⟩,⟨-369781653247,222024237962⟩,⟨-20109655219,288471790840⟩,⟨-14670081601920,10711669624898⟩,⟨-10231851017694,6603045565375⟩,⟨-6965066636294,7891371275819⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27587617270359,28979381121942⟩,⟨-271581445560892,-225941490215139⟩,⟨-103296319344318,-66694642228911⟩,⟨2570509783267365,4483866383899226⟩,⟨469691054122129,2208506343715669⟩,⟨-593965927989564,1216493256770013⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13498353996,14131398211⟩,⟨170539998108,181195662798⟩,⟨40162143318,43755239062⟩,⟨448483392579,680390116399⟩,⟨69489791988,160054058934⟩,⟨10848399070,43878566484⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338684388972,372455519521⟩,⟨788501568559,2001888744926⟩,⟨-319908925823,334450176905⟩,⟨-46701207677675,5471941461029⟩,⟨-20320696622233,14005446698770⟩,⟨-15583098379394,11919041548171⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372455519521,-338684388972⟩,⟨-2001888744926,-788501568559⟩,⟨-334450176905,319908925823⟩,⟨-5471941461029,46701207677675⟩,⟨-14005446698770,20320696622233⟩,⟨-11919041548171,15583098379394⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58152498644,108568690022⟩,⟨-1294835938765,279722196180⟩,⟨-559546265533,391016883749⟩,⟨-30268436742447,33430276998774⟩,⟨-25001155078817,20541177804143⟩,⟨-19670338102795,20514836511699⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237355549875,239800661342⟩,⟨1560144533251,1568447500785⟩,⟨307966960202,310000287878⟩,⟨-3938729622245,-3925004181828⟩,⟨-1557197100160,-1549327579210⟩,⟨-348416135661,-347732631878⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1709621621824,-1622136314134⟩,⟨-5569447481815,-2652290262098⟩,⟨-544093690163,1488343065273⟩,⟨-20418452785153,103153983607551⟩,⟨-59562618365217,43183338064689⟩,⟨-48944496345646,52771375894338⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-193817352002,-179733006967⟩,⟨-1873983034650,-1429259603927⟩,⟨-361742763360,-98651755209⟩,⟨-7206630578924,12293884666989⟩,⟨-7323483928173,6803502460960⟩,⟨-5580898228353,6840397943184⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43538197873,60067654375⟩,⟨-313838501399,139187896858⟩,⟨-53775803158,211348532669⟩,⟨-11145360201169,8368880485161⟩,⟨-8880681028333,5254174881750⟩,⟨-5929314364014,6492665311306⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2579966033,6423656294⟩,⟨-113124451094,38473513872⟩,⟨-35092213350,51619665922⟩,⟨-3762379770438,3906603477399⟩,⟨-2960779505924,2128929301239⟩,⟨-2145188164327,2198188222980⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1724015122,3281568845⟩,⟨-34290756288,15208007394⟩,⟨-5875674758,23092453582⟩,⟨-1297227145938,1093564834172⟩,⟨-1090977066980,627593396694⟩,⟨-668524886331,790655354929⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3021147280,5798611894⟩,⟨-84359059874,14919174110⟩,⟨-21018394631,35439445194⟩,⟨-2459588108538,2561037665316⟩,⟨-2106947984363,1348243251738⟩,⟨-1320218425414,1461439266121⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5798611894,-3021147280⟩,⟨-14919174110,84359059874⟩,⟨-35439445194,21018394631⟩,⟨-2561037665316,2459588108538⟩,⟨-1348243251738,2106947984363⟩,⟨-1461439266121,1320218425414⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3218645861,3402509014⟩,⟨-128043625204,122832573746⟩,⟨-70531658544,72638060553⟩,⟨-6323417435754,6366191585937⟩,⟨-4309022757662,4235877285602⟩,⟨-3606627430448,3518406648394⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48780408735,65054527105⟩,⟨-369781653247,222024237962⟩,⟨-20109655219,288471790840⟩,⟨-14670081601920,10711669624898⟩,⟨-10231851017694,6603045565375⟩,⟨-6965066636294,7891371275819⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3218645861,3402509014⟩,⟨-128043625204,122832573746⟩,⟨-70531658544,72638060553⟩,⟨-6323417435754,6366191585937⟩,⟨-4309022757662,4235877285602⟩,⟨-3606627430448,3518406648394⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (523/5120) u, BivariateJet2.affineZ (115/1024) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000039

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000040Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2504150381952,-2504150324096⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-118951416704,-118951416640⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2138576338304,-2138576299136⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2138576338304,-2138576299136⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-169652971264,-169652971200⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-169652971264,-169652971200⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨79884074112,79884074176⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-86145900224,-86145900160⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨79884197696,79884197760⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-86146043904,-86146043840⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-6261846208,-6261846144⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-6261826048,-6261825984⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨166029974336,166029974400⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨166030241600,166030241664⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1968923327936,1968923366528⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1968923327936,1968923366528⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2506246686976,-2506246629120⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2145623515136,-2145623475840⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2131568795328,-2131568756224⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-170826463040,-170826462976⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-168481610624,-168481610560⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨77324937536,77324937600⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-83177095488,-83177095424⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨82466073920,82466073984⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-89156413760,-89156413696⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-6690339840,-6690339776⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-5852157952,-5852157888⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨160502033024,160502033088⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨171622487616,171622487680⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1960742293248,1960742331840⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1977141865344,1977141903936⟩



end LaneCBRB2Cell000040Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000040
open Set LaneCBRB2Cell000040Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112742891520,112742891520⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112742891520,-112742891520⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437012922368,437012922368⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨44469479014,44469479015⟩,⟨-111883898061,-111883898060⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157212370534,157212370535⟩,⟨987627729715,987627729716⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44469479014,44469479015⟩,⟨-111883898061,-111883898060⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2504150381952,-2504150324096⟩,⟨10722856255644,10722856255645⟩,⟨0,0⟩,⟨-104573379102681,-104573379102661⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-256773232525,-256773226591⟩,⟨-1404638754177,-1404638696319⟩,⟨0,0⟩,⟨10722856255641,10722856255647⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256773226591,256773232525⟩,⟨1404638696319,1404638754177⟩,⟨0,0⟩,⟨-10722856255647,-10722856255641⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986768736256,986768736256⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-118951416704,-118951416640⟩,⟨-1225135916043,-1225135916042⟩,⟨0,0⟩,⟨-1365113360206,-1365113360203⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106754249953,-106754249894⟩,⟨-980560211137,-980560211071⟩,⟨0,0⟩,⟨1225135916039,1225135916045⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106754249894,106754249953⟩,⟨980560211071,980560211137⟩,⟨0,0⟩,⟨-1225135916045,-1225135916039⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨363527476485,363527482478⟩,⟨2385198907390,2385198965314⟩,⟨0,0⟩,⟨-11947992171692,-11947992171680⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2138576338304,-2138576299136⟩,⟨6907269250124,6907269250177⟩,⟨3056380283541,3056380283561⟩,⟨-43392327365317,-43392327364663⟩,⟨-26890325016139,-26890325015818⟩,⟨-8496008774947,-8496008774835⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-305781810053,-305781804449⟩,⟨-933331758548,-933331723348⟩,⟨-412987633973,-412987618398⟩,⟨6204400640788,6204400641030⟩,⟨3784434383033,3784434422315⟩,⟨1214791772836,1214791772878⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305781804449,305781810053⟩,⟨933331723348,933331758548⟩,⟨412987618398,412987633973⟩,⟨-6204400641030,-6204400640788⟩,⟨-3784434422315,-3784434383033⟩,⟨-1214791772878,-1214791772836⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157212370535,-157212370534⟩,⟨-987627729716,-987627729715⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨942299257241,942299257242⟩,⟨-987627729716,-987627729715⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-169652971264,-169652971200⟩,⟨-1152402662311,-1152402662306⟩,⟨-509923769907,-509923769905⟩,⟨-1207837973290,-1207837973279⟩,⟨748499968551,748499968559⟩,⟨-236488859734,-236488859731⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145395341689,-145395341633⟩,⟨-835238273753,-835238273688⟩,⟨-369582493388,-369582493358⟩,⟨1035136688261,1035136688284⟩,⟨1387893699043,1387893699122⟩,⟨202674779636,202674779643⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145395341633,145395341689⟩,⟨835238273688,835238273753⟩,⟨369582493358,369582493388⟩,⟨-1035136688284,-1035136688261⟩,⟨-1387893699122,-1387893699043⟩,⟨-202674779643,-202674779636⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨451177146082,451177151742⟩,⟨1768569997036,1768570032301⟩,⟨782570111756,782570127361⟩,⟨-7239537329314,-7239537329049⟩,⟨-5172328121437,-5172328082076⟩,⟨-1417466552521,-1417466552472⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨814704622567,814704634220⟩,⟨4153768904426,4153768997615⟩,⟨782570111756,782570127361⟩,⟨-19187529501006,-19187529500729⟩,⟨-5172328121437,-5172328082076⟩,⟨-1417466552521,-1417466552472⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨88938958028,88938958030⟩,⟨-223767796122,-223767796120⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13592758970785,13592758971092⟩,⟨34198980800480,34198980802332⟩,⟨-133579512346680,-133579512340644⟩,⟨172087254736938,172087254751677⟩,⟨-336082114624421,-336082114557677⟩,⟨2625439935412000,2625439935589917⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨10071820331120,10071820475409⟩,⟨76691546640572,76691548157611⟩,⟨-89303794847046,-89303793233714⟩,⟨148700695886279,148700703540880⟩,⟨-793269648613447,-793269632683014⟩,⟨1737698856663187,1737698888421622⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨82857603584,82857736448⟩,⟨-625760335397,-625758291951⟩,⟨728666868340,728669246588⟩,⟨8199624357523,8199675299708⟩,⟨-4488373767015,-4488297985872⟩,⟨-1415146785048,-1415036898663⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1182369231360,1182369364224⟩,⟨-625760335397,-625758291951⟩,⟨728666868340,728669246588⟩,⟨8199624357523,8199675299708⟩,⟨-4488373767015,-4488297985872⟩,⟨-1415146785048,-1415036898663⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨79884074112,79884197760⟩,⟨-581908549988,-581906584351⟩,⟨677603563452,677605851182⟩,⟨7317042589175,7317092898880⟩,⟨-3815223727205,-3815150365469⟩,⟨-1733570898050,-1733465744618⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨85904022221,85904164841⟩,⟨-671224556454,-671222153534⟩,⟨781607452698,781610249445⟩,⟨9126534825967,9126598834745⟩,⟨-5200119194105,-5200028709671⟩,⟨-1068905888213,-1068778494670⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-82857736448,-82857603584⟩,⟨625758291951,625760335397⟩,⟨-728669246588,-728666868340⟩,⟨-8199675299708,-8199624357523⟩,⟨4488297985872,4488373767015⟩,⟨1415036898663,1415146785048⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1016653891328,1016654024192⟩,⟨625758291951,625760335397⟩,⟨-728669246588,-728666868340⟩,⟨-8199675299708,-8199624357523⟩,⟨4488297985872,4488373767015⟩,⟨1415036898663,1415146785048⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-86146043904,-86145900160⟩,⟨676757777774,676760076207⟩,⟨-788056108634,-788053433567⟩,⟨-9284504814084,-9284445731748⟩,⟨5339148486878,5339234372478⟩,⟨965537119276,965659996060⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-79654202822,-79654059499⟩,⟨576730281803,576732730721⟩,⟨-671578846635,-671575996331⟩,⟨-7172085659884,-7172019713012⟩,⟨3688130102335,3688222659181⟩,⟨1826415089000,1826544571938⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6249819399,6250105342⟩,⟨-94494274651,-94489422813⟩,⟨110028606063,110034253114⟩,⟨1954449166083,1954579121733⟩,⟨-1511989091770,-1511806050490⟩,⟨757509200787,757766077268⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3124909699,3125052671⟩,⟨-47247137326,-47244711406⟩,⟨55014303031,55017126557⟩,⟨977224583041,977289560867⟩,⟨-755994545885,-755903025245⟩,⟨378754600393,378883038634⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3125052671,-3124909699⟩,⟨47244711406,47247137326⟩,⟨-55017126557,-55014303031⟩,⟨-977289560867,-977224583041⟩,⟨755903025245,755994545885⟩,⟨-378883038634,-378754600393⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758998330945,758998493181⟩,⟨47244711406,47247137326⟩,⟨-55017126557,-55014303031⟩,⟨-977289560867,-977224583041⟩,⟨755903025245,755994545885⟩,⟨-378883038634,-378754600393⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6244028983,6244049009⟩,⟨-94312936108,-94312476892⟩,⟨109822559390,109823093938⟩,⟨1948091566188,1948105877634⟩,⟨-1505884579832,-1505866658068⟩,⟨752515089816,752538298034⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6244049009,-6244028983⟩,⟨94312476892,94312936108⟩,⟨-109823093938,-109822559390⟩,⟨-1948105877634,-1948091566188⟩,⟨1505866658068,1505884579832⟩,⟨-752538298034,-752515089816⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1093267578767,1093267598793⟩,⟨94312476892,94312936108⟩,⟨-109823093938,-109822559390⟩,⟨-1948105877634,-1948091566188⟩,⟨1505866658068,1505884579832⟩,⟨-752538298034,-752515089816⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6261846208,-6261825984⟩,⟨94851128032,94851591609⟩,⟨-110450333595,-110449793970⟩,⟨-1967414783419,-1967400274359⟩,⟨1523995310851,1524013455837⟩,⟨-767931495184,-767908032134⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3130923104,-3130912992⟩,⟨47425564016,47425795805⟩,⟨-55225166798,-55224896985⟩,⟨-983707391710,-983700137179⟩,⟨761997655425,762006727919⟩,⟨-383965747592,-383954016067⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3130912992,3130923104⟩,⟨-47425795805,-47425564016⟩,⟨55224896985,55225166798⟩,⟨983700137179,983707391710⟩,⟨-762006727919,-761997655425⟩,⟨383954016067,383965747592⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765254296608,765254325984⟩,⟨-47425795805,-47425564016⟩,⟨55224896985,55225166798⟩,⟨983700137179,983707391710⟩,⟨-762006727919,-761997655425⟩,⟨383954016067,383965747592⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273316894691,273316899699⟩,⟨23578119223,23578234027⟩,⟨-27455773485,-27455639847⟩,⟨-487026469409,-487022891547⟩,⟨376466664517,376471144958⟩,⟨-188134574509,-188128772454⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530508593216,1530508651968⟩,⟨-94851591610,-94851128032⟩,⟨110449793970,110450333596⟩,⟨1967400274358,1967414783420⟩,⟨-1524013455838,-1523995310850⟩,⟨767908032134,767931495184⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1189122150552,1189122305956⟩,⟨-731916318180,-731913736771⟩,⟨852280021420,852283025889⟩,⟨10491629281415,10491697610132⟩,⟨-6298972779941,-6298875509097⟩,⟨-433506767713,-433369353321⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1278732673328,1278732984136⟩,⟨-1463832636361,-1463827473542⟩,⟨1704560042840,1704566051779⟩,⟨20983258562837,20983395220262⟩,⟨-12597945559881,-12597751018198⟩,⟨-867013387795,-866738854274⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨166029974336,166030241664⟩,⟨-1258668866737,-1258664121583⟩,⟨1465656716918,1465662239916⟩,⟨16601476640152,16601609393735⟩,⟨-9154469754173,-9154287197876⟩,⟨-2699242359916,-2698991398133⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57197014781,57197118725⟩,⟨-428405263020,-428403571562⟩,⟨498856336263,498858304924⟩,⟨5532815004579,5532859331755⟩,⟨-2978763678205,-2978700296529⟩,⟨-1078357167678,-1078267398635⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380454235706,380454257282⟩,⟨9242258903,9242535640⟩,⟨-10762509336,-10762187201⟩,⟨-192946897748,-192938236058⟩,⟨149934957400,149945777884⟩,⟨-76510654209,-76496678007⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177585206303,3177585386509⟩,⟨-77194425578,-77192105491⟩,⟨89886671479,89889372174⟩,⟨1615186403396,1615259154562⟩,⟨-1256727036139,-1256636258289⟩,⟨643991917680,644109025851⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨165299195953,165299505726⟩,⟨-1242105647181,-1242100560667⟩,⟨1446369209094,1446375129271⟩,⟨16133993718292,16134128713218⟩,⟨-8744041460563,-8743850576985⟩,⟨-3001383894109,-3001115359665⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨331329170289,331329747390⟩,⟨-2500774513918,-2500764682250⟩,⟨2912025926012,2912037369187⟩,⟨32735470358444,32735738106953⟩,⟨-17898511214736,-17898137774861⟩,⟨-5700626254025,-5700106757798⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523940312975,523940536961⟩,⟨65226517294,65229880490⟩,⟨-75957207002,-75953292576⟩,⟨-1345195853618,-1345105439214⟩,⟨1038878931982,1039005994810⟩,⟨-517584488768,-517406488725⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361678597130,361678829059⟩,⟨67539282680,67542779565⟩,⟨-78650471999,-78646401964⟩,⟨-1388689295024,-1388594943773⟩,⟨1070818981926,1070951284421⟩,⟨-530236315962,-530051302748⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨723357194260,723357658118⟩,⟨135078565360,135085559130⟩,⟨-157300943998,-157292803928⟩,⟨-2777378590048,-2777189887546⟩,⟨2141637963852,2141902568842⟩,⟨-1060472631924,-1060102605496⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524264544207,1524264622985⟩,⟨-539114718,-538191924⟩,⟨626700032,627774206⟩,⟨19294396724,19323217232⟩,⟨-18146797770,-18110731018⟩,⟨15369734100,15416405368⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002797693224,1002798388104⟩,⟨186906158979,186916471520⟩,⟨-217655666458,-217643663569⟩,⟨-3837748265137,-3837467263417⟩,⟨2957190642652,2957581628359⟩,⟨-1460212486293,-1459668411102⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67941186829,67941189319⟩,⟨11722110372,11722167664⟩,⟨-13649927292,-13649860602⟩,⟨-241119118046,-241117324985⟩,⟨185986829906,185989072302⟩,⟨-92161911148,-92159011529⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50342349797,50342352363⟩,⟨265356035639,265356093382⟩,⟨38242508842,38242561140⟩,⟨-1275732358544,-1275730549046⟩,⟨-225022691339,-225020719627⟩,⟨-175307968847,-175305720805⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130451824912,2130451988477⟩,⟨-264064841054,-264063540324⟩,⟨307489897368,307491411480⟩,⟨5493565845769,5493606608918⟩,⟨-4261877929478,-4261827065102⟩,⟨2160029905949,2160095525488⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2965566477960,2965566819482⟩,⟨-551363233054,-551360495984⟩,⟨642034042696,642037228785⟩,⟨11504648399321,11504734287773⟩,⟨-8938523607618,-8938416671610⟩,⟨4556440938091,4556578578303⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135781724547,135781747106⟩,⟨690464768792,690465133565⟩,⟨132542667973,132542968287⟩,⟨-3180242589355,-3180231974188⟩,⟨-880412759182,-880401530130⟩,⟨-219551627161,-219538914009⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8903448698968,8903450178203⟩,⟨-45275031945516,-45274992982559⟩,⟨-8691079145972,-8691056565950⟩,⟨668989825897607,668991307267750⟩,⟨146119393847902,146120440365003⟩,⟨31363016006061,31363939760143⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8120294130152,8120301106161⟩,⟨-39779133347411,-39778985439605⟩,⟨-9689107665307,-9688984090876⟩,⟨563674762167366,563679679178263⟩,⟨164697390354378,164702194519972⟩,⟨20220739101861,20226207805376⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16240588260304,16240602212322⟩,⟨-79558266694822,-79557970879210⟩,⟨-19378215330614,-19377968181752⟩,⟨1127349524334732,1127359358356526⟩,⟨329394780708756,329404389039944⟩,⟨40441478203722,40452415610752⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10722856255644,10722856255645⟩,⟨-104573379102681,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974382⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9623344627868,9623344627869⟩,⟨-104573379102680,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974364⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2385198907456,2385198965312⟩,⟨-11947992171781,-11947992171683⟩,⟨0,0⟩,⟨103208265737483,103208265748560⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7689762678983,7689762679033⟩,⟨-48308048730211,-48308048729533⟩,⟨-21375707581192,-21375707580913⟩,⟨606954380642495,606954380655574⟩,⟨322350374886494,322350374892710⟩,⟨118838745396792,118838745399113⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6590251051207,6590251051257⟩,⟨-48308048730212,-48308048729533⟩,⟨-21375707581192,-21375707580913⟩,⟨606954380642505,606954380655573⟩,⟨322350374886497,322350374892711⟩,⟨118838745396793,118838745399114⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1968923327936,1968923366528⟩,⟨-8059671912584,-8059671912338⟩,⟨-3566304053511,-3566304053405⟩,⟨42184489386369,42184489395782⟩,⟨27638824982078,27638824986437⟩,⟨8259519914138,8259519915935⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101182341120,101182341120⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134733545549,134733545551⟩,⟨705198162491,705198162496⟩,⟨312041370008,312041370010⟩,⟨-1774257784753,-1774257784749⟩,⟨-1570173773416,-1570173773412⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4354122235392,4354122331840⟩,⟨-20007664084365,-20007664084021⟩,⟨-3566304053511,-3566304053405⟩,⟨145392755123852,145392755144342⟩,⟨27638824982078,27638824986437⟩,⟨8259519914138,8259519915935⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨662658340578,662659494780⟩,⟨-5001549027836,-5001529364500⟩,⟨5824051852024,5824074738374⟩,⟨65470940716888,65471476213906⟩,⟨-35797022429472,-35796275549722⟩,⟨-11401252508050,-11400213515596⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5016780575970,5016781826620⟩,⟨-25009213112201,-25009193448521⟩,⟨2257747798513,2257770684969⟩,⟨210863695840740,210864231358248⟩,⟨-8158197447394,-8157450563285⟩,⟨-3141732593912,-3140693599661⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461668245008,461668360100⟩,⟨1686480708035,1686483511752⟩,⟨207768796746,207770902869⟩,⟨-30389614708415,-30389531664042⟩,⟨1043976599020,1044063523830⟩,⟨-289117323542,-289021710299⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨225485783040,225485783040⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-225485783040,-225485783040⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨874025844736,874025844736⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1896046787762,1896046833754⟩,⟨-14268118270302,-14268118154511⟩,⟨0,0⟩,⟨129834476802270,129834476811468⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨796535159986,796535205978⟩,⟨-14268118270302,-14268118154511⟩,⟨0,0⟩,⟨129834476802270,129834476811468⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32215669835,32215671697⟩,⟨-658124235809,-658124226430⟩,⟨316591611439,316591629720⟩,⟨8154908660495,8154908684579⟩,⟨-6467554870054,-6467554778038⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨493883914843,493884031797⟩,⟨1028356472226,1028359285322⟩,⟨524360408185,524362532589⟩,⟨-22234706047920,-22234622979463⟩,⟨-5423578271034,-5423491254208⟩,⟨-289117323542,-289021710299⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506844853278,506844865574⟩,⟨2538898610666,2538898733883⟩,⟨0,0⟩,⟨3504487769187,3504490687699⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227667005997,227667065434⟩,⟨1614478942890,1614480576560⟩,⟨241715837684,241716822841⟩,⟨-3926243900209,-3926190453529⟩,⟨-1289313229686,-1289268092393⟩,⟨-133275198992,-133231120663⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-662659494780,-662658340578⟩,⟨5001529364500,5001549027836⟩,⟨-5824074738374,-5824051852024⟩,⟨-65471476213906,-65470940716888⟩,⟨35796275549722,35797022429472⟩,⟨11400213515596,11401252508050⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3691462740612,3691463991262⟩,⟨-15006134719865,-15006115056185⟩,⟨-9390378791885,-9390355905429⟩,⟨79921278909946,79921814427454⟩,⟨63435100531800,63435847415909⟩,⟨19659733429734,19660772423985⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨452349798528,452349951790⟩,⟨528764763439,528767975196⟩,⟨-103054788073,-103051628619⟩,⟨-15412414279598,-15412321415589⟩,⟨-7779832816054,-7779719247748⟩,⟨-4087205152330,-4087064448983⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨314424741068,314424741070⟩,⟨1975255459430,1975255459432⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-314424741070,-314424741068⟩,⟨-1975255459432,-1975255459430⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨785086886706,785086886708⟩,⟨-1975255459432,-1975255459430⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1405874978165,1405875005725⟩,⟨-9292006651482,-9292006581957⟩,⟨-4111596767940,-4111596737179⟩,⟨59079239992340,59079240000053⟩,⟨36486481209860,36486481290602⟩,⟨11567430738797,11567430740266⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1405875005725,-1405874978165⟩,⟨9292006581957,9292006651482⟩,⟨4111596737179,4111596767940⟩,⟨-59079240000053,-59079239992340⟩,⟨-36486481290602,-36486481209860⟩,⟨-11567430740266,-11567430738797⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-306363377949,-306363350389⟩,⟨9292006581957,9292006651482⟩,⟨4111596737179,4111596767940⟩,⟨-59079240000053,-59079239992340⟩,⟨-36486481290602,-36486481209860⟩,⟨-11567430740266,-11567430738797⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12390791933,-12390790817⟩,⟨406987799176,406987804804⟩,⟨44525049555,44525061759⟩,⟨-4280513961347,-4280513946813⟩,⟨2105499087868,2105499149498⟩,⟨2800556278875,2800556303399⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439959006595,439959160973⟩,⟨935752562615,935755780000⟩,⟨-58529738518,-58526566860⟩,⟨-19692928240945,-19692835362402⟩,⟨-5674333728186,-5674220098250⟩,⟨-1286648873455,-1286508145584⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101182341120,-101182341120⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4092295052,4092295054⟩,⟨25053667941,25053667944⟩,⟨40216028160,40216028160⟩,⟨-266816874088,-266816874084⟩,⟨246208790528,246208790528⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8877521110,8877521331⟩,⟨9880088446,9880089795⟩,⟨87241666214,87241668331⟩,⟨-739177916094,-739177901743⟩,⟨97094151476,97094164437⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1483882340711,1483882361936⟩,⟨-7565569631482,-7565569245314⟩,⟨-1425353406381,-1425353337181⟩,⟨112093739133249,112093746905560⟩,⟨23955065702603,23955067283404⟩,⟨5320003403010,5320003703671⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11980952699,11980953169⟩,⟨-47750852005,-47750845354⟩,⟨106231493736,106231499124⟩,⟨-228497402705,-228497258275⟩,⟨-288653280171,-288653195645⟩,⟨-183237694504,-183237674535⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-11980953169,-11980952699⟩,⟨47750845354,47750852005⟩,⟨-106231499124,-106231493736⟩,⟨228497258275,228497402705⟩,⟨288653195645,288653280171⟩,⟨183237674535,183237694504⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113163294289,-113163293819⟩,⟨-826274999382,-826274992731⟩,⟨-106231499124,-106231493736⟩,⟨2427520513827,2427520658257⟩,⟨288653195645,288653280171⟩,⟨183237674535,183237694504⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨79632622702,79632624266⟩,⟨-526324795115,-526324791167⟩,⟨638331816108,638331831456⟩,⟨3346410527917,3346410528403⟩,⟨-3691583301471,-3691583262563⟩,⟨-2500878841119,-2500878840952⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨107470843951,107470847600⟩,⟨-1258258856927,-1258258802707⟩,⟨758249986737,758250026815⟩,⟨19877817275298,19877818486958⟩,⟨-6957103106395,-6957102466008⟩,⟨-4644844992660,-4644844794669⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-107470847600,-107470843951⟩,⟨1258258802707,1258258856927⟩,⟨-758250026815,-758249986737⟩,⟨-19877818486958,-19877817275298⟩,⟨6957102466008,6957103106395⟩,⟨4644844794669,4644844992660⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨992040780176,992040783825⟩,⟨1258258802707,1258258856927⟩,⟨-758250026815,-758249986737⟩,⟨-19877818486958,-19877817275298⟩,⟨6957102466008,6957103106395⟩,⟨4644844794669,4644844992660⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121564127441,121564127891⟩,⟨790455492280,790455501274⟩,⟨188625608300,188625614252⟩,⟨-2422622360290,-2422622136321⟩,⟨-693407004230,-693406879427⟩,⟨-174641643006,-174641594830⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11646926457,11646926555⟩,⟨170082784784,170082786862⟩,⟨21866991552,21866992754⟩,⟨742191566986,742191618786⟩,⟨100247181076,100247208110⟩,⟨-17190633821,-17190627468⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172033594104,172033743344⟩,⟨1669500478605,1669505808142⟩,⟨117721497703,117724412666⟩,⟨-1709121337428,-1708915064142⟩,⟨390090525948,390238244051⟩,⟨-596313758846,-596187712383⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172033743344,-172033594104⟩,⟨-1669505808142,-1669500478605⟩,⟨-117724412666,-117721497703⟩,⟨1708915064142,1709121337428⟩,⟨-390238244051,-390090525948⟩,⟨596187712383,596313758846⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨55633262653,55633471330⟩,⟨-55026865252,-55019902045⟩,⟨123991425018,123995325138⟩,⟨-2217328836067,-2217069116101⟩,⟨-1679551473737,-1679358618341⟩,⟨462912513391,463082638183⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29082432852297,29082458406563⟩,⟨-261514338299097,-261513703507032⟩,⟨-87378017694684,-87377529183373⟩,⟨3808225289404559,3808247811263971⟩,⟨1398195149040669,1398215488423870⟩,⟨320124931887666,320146227308869⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13440364528,13440364628⟩,⟨174788569346,174788571984⟩,⟨41709622538,41709624010⟩,⟨600841141635,600841219009⟩,⟨117882755734,117882795544⟩,⟨26101517651,26101532535⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355501923782,355502238802⟩,⟨1426477655662,1426489571228⟩,⟨35129122322,35136110132⟩,⟨-20701533902355,-20701039159381⟩,⟨-3601393333940,-3601038487931⟩,⟨-2025733116234,-2025434475832⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355502238802,-355501923782⟩,⟨-1426489571228,-1426477655662⟩,⟨-35136110132,-35129122322⟩,⟨20701039159381,20701533902355⟩,⟨3601038487931,3601393333940⟩,⟨2025434475832,2025733116234⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84456767793,84457237191⟩,⟨-490737008613,-490721875662⟩,⟨-93665848650,-93655689182⟩,⟨1008110918436,1008698539953⟩,⟨-2073295240255,-2072826764310⟩,⟨738785602377,739224970650⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235915886669,235915886671⟩,⟨1579224007227,1579224007232⟩,⟨312041370008,312041370010⟩,⟨-3973281040305,-3973281040301⟩,⟨-1570173773416,-1570173773412⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1671505785984,-1671504343079⟩,⟨-4016475530719,-4016434467867⟩,⟨425289897316,425316770099⟩,⟨39401298580898,39402789700161⟩,⟨-7390095118266,-7388886344619⟩,⟨2287615665835,2288791944137⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-184804906110,-184804745895⟩,⟨-1645740020678,-1645734428044⟩,⟨-239732626443,-239729398576⟩,⟨2264203018556,2264430522552⟩,⟨-146224271310,-146063135270⟩,⟨664337965415,664477545248⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51110980559,51111140776⟩,⟨-66516013451,-66510420812⟩,⟨72308743565,72311971434⟩,⟨-1709078021749,-1708850517749⟩,⟨-1716398044726,-1716236908682⟩,⟨316946833767,317086413600⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4273356849,4273396630⟩,⟨-29057282800,-29055865605⟩,⟨4784814050,4785698395⟩,⟨-70200284309,-70141733632⟩,⟨-284572758208,-284528581051⟩,⟨51812906709,51851499574⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2375902416,2375917313⟩,⟨-6184035242,-6183495906⟩,⟨6722567898,6722889070⟩,⟨-150847502102,-150824499624⟩,⟨-168323760876,-168307153648⟩,⟨38977337416,38991255745⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4254588649,4254615410⟩,⟨-28489926556,-28488851335⟩,⟨4331902539,4332526227⟩,⟨-88318342819,-88268667918⟩,⟨-270921635618,-270887412619⟩,⟨44033612660,44060733313⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4254615410,-4254588649⟩,⟨28488851335,28489926556⟩,⟨-4332526227,-4331902539⟩,⟨88268667918,88318342819⟩,⟨270887412619,270921635618⟩,⟨-44060733313,-44033612660⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨18741439,18807981⟩,⟨-568431465,-565939049⟩,⟨452287823,453795856⟩,⟨18068383609,18176609187⟩,⟨-13685345589,-13606945433⟩,⟨7752173396,7817886914⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨55633262653,55633471330⟩,⟨-55026865252,-55019902045⟩,⟨123991425018,123995325138⟩,⟨-2217328836067,-2217069116101⟩,⟨-1679551473737,-1679358618341⟩,⟨462912513391,463082638183⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨18741439,18807981⟩,⟨-568431465,-565939049⟩,⟨452287823,453795856⟩,⟨18068383609,18176609187⟩,⟨-13685345589,-13606945433⟩,⟨7752173396,7817886914⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112528143155,112957639885⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112957639885,-112528143155⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436798174003,437227670733⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨43679817400,45259895604⟩,⟨-113816633344,-109951162777⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156207960555,158217535489⟩,⟨985694994432,989560464999⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨43250320670,45689392334⟩,⟨-113816633344,-109951162777⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2506246686976,-2502058008320⟩,⟨10702470597344,10743319721800⟩,⟨0,0⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-257477686983,-256069999288⟩,⟨-1410915711782,-1398349771273⟩,⟨0,0⟩,⟨10620616435743,10824862650847⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256069999288,257477686983⟩,⟨1398349771273,1410915711782⟩,⟨0,0⟩,⟨-10824862650847,-10620616435743⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986553987891,986983484621⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-119190727104,-118712158336⟩,⟨-1225402597783,-1224869350350⟩,⟨0,0⟩,⟨-1365707727613,-1364519380719⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106992301127,-106516338944⟩,⟨-981278142331,-979842436080⟩,⟨0,0⟩,⟨1223802623334,1226468860601⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106516338944,106992301127⟩,⟨979842436080,981278142331⟩,⟨0,0⟩,⟨-1226468860601,-1223802623334⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨362586338232,364469988110⟩,⟨2378192207353,2392193854113⟩,⟨0,0⟩,⟨-12051331511448,-11844419059077⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2145623515136,-2131568756224⟩,⟨6849955692135,6965286748436⟩,⟨3035470561611,3077544231731⟩,⟨-44124335079626,-42675213066299⟩,⟨-27235115966596,-26551885952188⟩,⟨-8614077613180,-8380158333611⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308750954585,-302832639310⟩,⟨-957885817835,-908627180238⟩,⟨-421970349671,-403946502753⟩,⟨5932352473107,6474635290881⟩,⟨3654993618084,3912968397577⟩,⟨1172227590935,1257037683549⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨302832639310,308750954585⟩,⟨908627180238,957885817835⟩,⟨403946502753,421970349671⟩,⟨-6474635290881,-5932352473107⟩,⟨-3912968397577,-3654993618084⟩,⟨-1257037683549,-1172227590935⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158217535489,-156207960555⟩,⟨-989560464999,-985694994432⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941294092287,943303667221⟩,⟨-989560464999,-985694994432⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-170826463040,-168481610560⟩,⟨-1155890859796,-1148922818259⟩,⟨-510719138573,-509130503777⟩,⟨-1215161027868,-1200554508901⟩,⟨744680022723,752312748116⟩,⟨-237227176063,-235753641278⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146557094053,-144237442035⟩,⟨-840631952789,-829851294038⟩,⟨-371229158637,-367937426629⟩,⟨1017459988398,1052806443768⟩,⟨1379550669079,1396244279766⟩,⟨200995858551,204352153510⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144237442035,146557094053⟩,⟨829851294038,840631952789⟩,⟨367937426629,371229158637⟩,⟨-1052806443768,-1017459988398⟩,⟨-1396244279766,-1379550669079⟩,⟨-204352153510,-200995858551⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨447070081345,455308048638⟩,⟨1738478474276,1798517770624⟩,⟨771883929382,793199508308⟩,⟨-7527441734649,-6949812461505⟩,⟨-5309212677343,-5034544287163⟩,⟨-1461389837059,-1373223449486⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨809656419577,819778036748⟩,⟨4116670681629,4190711624737⟩,⟨771883929382,793199508308⟩,⟨-19578773246097,-18794231520582⟩,⟨-5309212677343,-5034544287163⟩,⟨-1461389837059,-1373223449486⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨86500641340,91378784668⟩,⟨-227633266688,-219902325554⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13229830359496,13975917413870⟩,⟨31837482554708,36778730037113⟩,⟨-141285838406784,-126479374055860⟩,⟨153233301996771,193572263356446⟩,⟨-425234850288736,-253446823964098⟩,⟨2418327616737727,2856583584916896⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9742158982117,10420217349106⟩,⟨72978106707025,80689855782638⟩,⟨-96052766627021,-83054279755353⟩,⟨102376244032720,198542600890514⟩,⟨-900684129122795,-694228288307735⟩,⟨1558377790160694,1935715933817237⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨80108814336,85637441792⟩,⟨-703488445966,-556449822824⟩,⟨633279504498,837428830053⟩,⟨5957951972184,10741105992108⟩,⟨-8421972699602,-898003515942⟩,⟨-6917644725481,4444265235923⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1179620442112,1185149069568⟩,⟨-703488445966,-556449822824⟩,⟨633279504498,837428830053⟩,⟨5957951972184,10741105992108⟩,⟨-8421972699602,-898003515942⟩,⟨-6917644725481,4444265235923⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨77324937536,82466073984⟩,⟨-655714074403,-516241430026⟩,⟨587519491603,780558477293⟩,⟨5136390347802,9769285209578⟩,⟨-7574179419147,-367614395429⟩,⟨-7001992073090,3828513596148⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨82958719760,88889092561⟩,⟨-759548907275,-592987263839⟩,⟨674861712979,904162899099⟩,⟨6452150247760,12174869578568⟩,⟨-9794608973093,-1052225120888⟩,⟨-7389414610973,5649039646332⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-85637441792,-80108814336⟩,⟨556449822824,703488445966⟩,⟨-837428830053,-633279504498⟩,⟨-10741105992108,-5957951972184⟩,⟨898003515942,8421972699602⟩,⟨-4444265235923,6917644725481⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1013874185984,1019402813440⟩,⟨556449822824,703488445966⟩,⟨-837428830053,-633279504498⟩,⟨-10741105992108,-5957951972184⟩,⟨898003515942,8421972699602⟩,⟨-4444265235923,6917644725481⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-89156413760,-83177095424⟩,⟨600177910441,762908985197⟩,⟨-908162717631,-683045180617⟩,⟨-12177712738518,-6753764333689⟩,⟨1341418386595,9763478573362⟩,⟨-5569766963209,7077621992213⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-82660607426,-76698697662⟩,⟨496388005039,665229605054⟩,⟨-794088263901,-561940146527⟩,⟨-10232262596522,-4380520761745⟩,⟨-608094856699,8292830410066⟩,⟨-4938075545242,8305710985777⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨298112334,12190394899⟩,⟨-263160902236,72242341215⟩,⟨-119226550922,342222752572⟩,⟨-3780112348762,7794348816823⟩,⟨-10402703829792,7240605289178⟩,⟨-12327490156215,13954750632109⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨149056167,6095197450⟩,⟨-131580451118,36121170608⟩,⟨-59613275461,171111376286⟩,⟨-1890056174381,3897174408412⟩,⟨-5201351914896,3620302644589⟩,⟨-6163745078108,6977375316055⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6095197450,-149056167⟩,⟨-36121170608,131580451118⟩,⟨-171111376286,59613275461⟩,⟨-3897174408412,1890056174381⟩,⟨-3620302644589,5201351914896⟩,⟨-6977375316055,6163745078108⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨756028186166,761974346713⟩,⟨-36121170608,131580451118⟩,⟨-171111376286,59613275461⟩,⟨-3897174408412,1890056174381⟩,⟨-3620302644589,5201351914896⟩,⟨-6977375316055,6163745078108⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨5836611430,6670026266⟩,⟨-109584927202,-81084245800⟩,⟨92279643010,130449302904⟩,⟨1431400730658,2573391307650⟩,⟨-2383526776790,-771844979694⟩,⟨-348093575121,1967932895884⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6670026266,-5836611430⟩,⟨81084245800,109584927202⟩,⟨-130449302904,-92279643010⟩,⟨-2573391307650,-1431400730658⟩,⟨771844979694,2383526776790⟩,⟨-1967932895884,348093575121⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092841601510,1093675016346⟩,⟨81084245800,109584927202⟩,⟨-130449302904,-92279643010⟩,⟨-2573391307650,-1431400730658⟩,⟨771844979694,2383526776790⟩,⟨-1967932895884,348093575121⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6690339840,-5852157888⟩,⟨81516967795,110253765524⟩,⟨-131245484415,-92772111440⟩,⟨-2600153409719,-1445083288542⟩,⟨782842136744,2411235012843⟩,⟨-1995610325089,342390406160⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3345169920,-2926078944⟩,⟨40758483897,55126882762⟩,⟨-65622742208,-46386055720⟩,⟨-1300076704860,-722541644271⟩,⟨391421068372,1205617506422⟩,⟨-997805162545,171195203080⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨2926078944,3345169920⟩,⟨-55126882762,-40758483897⟩,⟨46386055720,65622742208⟩,⟨722541644271,1300076704860⟩,⟨-1205617506422,-391421068372⟩,⟨-171195203080,997805162545⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765049462560,765468572800⟩,⟨-55126882762,-40758483897⟩,⟨46386055720,65622742208⟩,⟨722541644271,1300076704860⟩,⟨-1205617506422,-391421068372⟩,⟨-171195203080,997805162545⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273210400377,273418754087⟩,⟨20271061450,27396231801⟩,⟨-32612325726,-23069910752⟩,⟨-643347826913,-357850182664⟩,⟨192961244923,595881694198⟩,⟨-491983223971,87023393781⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530098925120,1530937145600⟩,⟨-110253765524,-81516967794⟩,⟨92772111440,131245484416⟩,⟨1445083288542,2600153409720⟩,⟨-2411235012844,-782842136744⟩,⟨-342390406160,1995610325090⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1185915718179,1192382483278⟩,⟨-827348513016,-647342328826⟩,⟨736721645734,984871181999⟩,⟨7637859968280,13780375384409⟩,⟨-11271520543915,-1848978360823⟩,⟨-7220262277713,6853693641491⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1272319808582,1285253338780⟩,⟨-1654697026032,-1294684657652⟩,⟨1473443291469,1969742363998⟩,⟨15275719936565,27560750768808⟩,⟨-22543041087822,-3697956721646⟩,⟨-14435921984065,13707387282978⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨160502033024,171622487680⟩,⟨-1429953859319,-1107579955203⟩,⟨1260504822633,1702209317447⟩,⟨11208404055477,22701705190085⟩,⟨-18211460514151,-949753364283⟩,⟨-15110491681767,10400560542982⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨55083111509,59347743230⟩,⟨-490339037861,-372368537698⟩,⟨422117968441,584991006787⟩,⟨3624795610528,7637143834733⟩,⟨-6184151755376,-2656959666⟩,⟨-5598103227645,3650809240898⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380204201017,380702592280⟩,⟨792426483,17890329679⟩,⟨-22356393991,532719409⟩,⟨-542199247645,145591598037⟩,⟨-327659928402,641710421269⟩,⟨-777956112716,613530706818⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175512444962,3179675070347⟩,⟨-149618113447,-6609779417⟩,⟨-4455170721,186968130405⟩,⟨-1217565486331,4548531712759⟩,⟨-5384265787703,2740662812381⟩,⟨-5131525352028,6528090739565⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨159086181251,171627597984⟩,⟨-1426086157230,-1075773082255⟩,⟨1218883387717,1701825983450⟩,⟨10407571931517,22464799399774⟩,⟨-18337541601120,139706918937⟩,⟨-16470863731915,11109081181128⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨319588214275,343250085664⟩,⟨-2856040016549,-2183353037458⟩,⟨2479388210350,3404035300897⟩,⟨21615975986994,45166504589859⟩,⟨-36549002115271,-810046445346⟩,⟨-31581355413682,21509641724110⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519847724970,528057084966⟩,⟨-50064782730,182373566134⟩,⟨-237164348002,82625386540⟩,⟨-5410219753322,2651154743656⟩,⟨-5058778068994,7223462797002⟩,⟨-9689359117750,8596352440313⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357449182585,365949701831⟩,⟨-52043215121,189580503838⟩,⟨-246536477516,85890530861⟩,⟨-5633004833013,2788659048663⟩,⟨-5301260861674,7523747487618⟩,⟨-10091545701598,8991421354247⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714898365170,731899403662⟩,⟨-104086430242,379161007676⟩,⟨-493072955032,171781061722⟩,⟨-11266009666026,5577318097326⟩,⟨-10602521723348,15047494975236⟩,⟨-20183091403196,17982842708494⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523428898854,1525100534170⟩,⟨-29169519724,28067959408⟩,⟨-37677191464,38965841406⟩,⟨-1128308019108,1168752679062⟩,⟨-1639390033150,1600684640046⟩,⟨-2310323302044,2343703900211⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨990527795914,1015196331977⟩,⟨-163792196376,544606862692⟩,⟨-709007273207,264210452844⟩,⟨-16397939557409,8533483878499⟩,⟨-15823302787821,21963969436124⟩,⟨-29568212751097,26537376212046⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67888252373,67991836738⟩,⟨10074045012,13625401272⟩,⟨-16219603764,-11464980258⟩,⟨-319218898490,-176474419573⟩,⟨94270152016,295508614424⟩,⟨-243717694228,45215332091⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49991430703,50693610716⟩,⟨261598046005,269305005814⟩,⟨35566132346,40607480155⟩,⟨-1373284562292,-1186518533649⟩,⟨-313641409237,-123622910793⟩,⟨-295483692361,-67173888922⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2129311470210,2131645072749⟩,⟨-307030104674,-226880774426⟩,⟨258206469870,365486971142⟩,⟨4034091766780,7262910607119⟩,⟨-6741028404212,-2192588750750⟩,⟨-937819143340,5588625484968⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2963185754028,2968058309404⟩,⟨-641253507725,-473596668252⟩,⟨538986717412,763344697162⟩,⟨8446096365741,15215270003112⟩,⟨-14134075761431,-4605580078406⟩,⟨-1926026257796,11737669677624⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134726992912,136844021217⟩,⟨675441831401,705437910483⟩,⟨120356866160,144811627086⟩,⟨-3637198255421,-2721518983289⟩,⟨-1393759832656,-370917986532⟩,⟨-851569628048,416522339891⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8834334221277,8973152250227⟩,⟨-46983916415181,-43604965949991⟩,⟨-9644813926001,-7769961537426⟩,⟨606150299217394,734267151789201⟩,⟨100648369148502,193829412949490⟩,⟨-14073770182815,77450153779437⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7958673090405,8285052218254⟩,⟨-44717700731860,-34838276876958⟩,⟨-14691440746249,-4843570656277⟩,⟨365700529988366,761600646894480⟩,⟨-54529820270076,389948249488901⟩,⟨-258936994177338,300522074707904⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15917346180810,16570104436508⟩,⟨-89435401463720,-69676553753916⟩,⟨-29382881492498,-9687141312554⟩,⟨731401059976732,1523201293788960⟩,⟨-109059640540152,779896498977802⟩,⟨-517873988354676,601044149415808⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10702470597344,10743319721800⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803854,2051378711294242⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9602958969568,9643808094024⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803861,2051378711294240⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2382867281216,2387534528576⟩,⟨-12019099426619,-11877349255562⟩,⟨0,0⟩,⟨99839973091184,106573343585493⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7640909181641,7739207498257⟩,⟨-49027038977332,-47602852047811⟩,⟨-21662120520363,-21094597181961⟩,⟨593131385079281,621161934584665⟩,⟨315938091445643,328928849474386⟩,⟨116473581792701,121264991420478⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6541397553865,6639695870481⟩,⟨-49027038977332,-47602852047811⟩,⟨-21662120520364,-21094597181960⟩,⟨593131385079287,621161934584663⟩,⟨315938091445645,328928849474386⟩,⟨116473581792701,121264991420479⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1960742293248,1977141903936⟩,⟨-8240715991844,-7882874511523⟩,⟨-3641080242924,-3493195371771⟩,⟨36457351780938,47892344107655⟩,⟨25028813792337,30243818107275⟩,⟨7230044591913,9284810487395⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100967634698,101397131429⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133729945845,135739520780⟩,⟨701459664074,708935304612⟩,⟨311027594034,313054545840⟩,⟨-1781208837000,-1767320322048⟩,⟨-1574105513986,-1566242032842⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4343609574464,4364676432512⟩,⟨-20259815418463,-19760223767085⟩,⟨-3641080242924,-3493195371771⟩,⟨136297324872122,154465687693148⟩,⟨25028813792337,30243818107275⟩,⟨7230044591913,9284810487395⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨639176428550,686500171328⟩,⟨-5712080033098,-4366706074916⟩,⟨4958776420700,6808070601794⟩,⟨43231951973988,90333009179718⟩,⟨-73098004230542,-1620092890692⟩,⟨-63162710827364,43019283448220⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4982786003014,5051176603840⟩,⟨-25971895451561,-24126929842001⟩,⟨1317696177776,3314875230023⟩,⟨179529276846110,244798696872866⟩,⟨-48069190438205,28623725216583⟩,⟨-55932666235451,52304093935615⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457566890809,465820283326⟩,⟨1563846998183,1801699293761⟩,⟨121003419117,305698303573⟩,⟨-34927810510253,-25729397980047⟩,⟨-3385997344469,5276046048458⟩,⟨-5158119083218,4823491587617⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨225056286310,225915279770⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-225915279770,-225056286310⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨873596348006,874455341466⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1893262519527,1898836054759⟩,⟨-14334009069890,-14202659713135⟩,⟨0,0⟩,⟨126835375642316,132835510026853⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨793750891751,799324426983⟩,⟨-14334009069890,-14202659713135⟩,⟨0,0⟩,⟨126835375642316,132835510026853⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨31222935467,33215335268⟩,⟨-678381711025,-638050023974⟩,⟨315329944105,317856354168⟩,⟨7829720351583,8487469170013⟩,⟨-6499332721185,-6435979379349⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨488789826276,499035618594⟩,⟨885465287158,1163649269787⟩,⟨436333363222,623554657741⟩,⟨-27098090158670,-17241928810034⟩,⟨-9885330065654,-1159933330891⟩,⟨-5158119083218,4823491587617⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506349041299,507340811276⟩,⟨2518951804351,2559009350623⟩,⟨0,0⟩,⟨2371496934072,4641016220299⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225098356105,230266901411⟩,⟨1527580492713,1698393661037⟩,⟨200941012875,287722947118⟩,⟨-7392295360804,-417297085953⟩,⟨-3561698270146,917089955435⟩,⟨-2380078804289,2225673720427⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-686500171328,-639176428550⟩,⟨4366706074916,5712080033098⟩,⟨-6808070601794,-4958776420700⟩,⟨-90333009179718,-43231951973988⟩,⟨1620092890692,73098004230542⟩,⟨-43019283448220,63162710827364⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3657109403136,3725500003962⟩,⟨-15893109343547,-14048143733987⟩,⟨-10449150844718,-8451971792471⟩,⟨45964315692404,111233735719160⟩,⟨26648906683029,103341822337817⟩,⟨-35789238856307,72447521314759⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨444802064912,459929274443⟩,⟨371066278064,693472410942⟩,⟨-255477779724,32744521084⟩,⟨-20939715530724,-10070727654272⟩,⟨-13354797661678,-1817558464391⟩,⟨-11546763195928,3007880730446⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨312415921110,316435070978⟩,⟨1971389988864,1979120929998⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-316435070978,-312415921110⟩,⟨-1979120929998,-1971389988864⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨783076556798,787095706666⟩,⟨-1979120929998,-1971389988864⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1396448464006,1415355567640⟩,⟨-9458049226569,-9129764255526⟩,⟨-4178947097503,-4045738670093⟩,⟨54232566338728,63950761090894⟩,⟨34273485649781,38712493410324⟩,⟨10700172300705,12438211893913⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1415355567640,-1396448464006⟩,⟨9129764255526,9458049226569⟩,⟨4045738670093,4178947097503⟩,⟨-63950761090894,-54232566338728⟩,⟨-38712493410324,-34273485649781⟩,⟨-12438211893913,-10700172300705⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-315843939864,-296936836230⟩,⟨9129764255526,9458049226569⟩,⟨4045738670093,4178947097503⟩,⟨-63950761090894,-54232566338728⟩,⟨-38712493410324,-34273485649781⟩,⟨-12438211893913,-10700172300705⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13124661278,-11680288831⟩,⟨388821519761,425717021904⟩,⟨33545606753,55690257452⟩,⟨-4615538323816,-3959241691024⟩,⟨1882622992369,2324142771208⟩,⟨2697605108573,2902667554633⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨431677403634,448248985612⟩,⟨759887797825,1119189432846⟩,⟨-221932172971,88434778536⟩,⟨-25555253854540,-14029969345296⟩,⟨-11472174669309,506584306817⟩,⟨-8849158087355,5910548285079⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101397131429,-100967634698⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨3971656567,4213482789⟩,⟨23867543910,26240581372⟩,⟨40110970503,40321203045⟩,⟨-272418367081,-261219910940⟩,⟨245652667759,246764997182⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8607394634,9149367220⟩,⟨5666989538,14076742361⟩,⟨86928702539,87555476515⟩,⟨-804588567821,-673365993679⟩,⟨91616271808,102543659135⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1474698961697,1493134359691⟩,⟨-7728334349185,-7405480151587⟩,⟨-1462785215196,-1388542237268⟩,⟨108184991278773,116108732019282⟩,⟨23002298944758,24933526610746⟩,⟨5085130223909,5561139634857⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11544503585,12424820458⟩,⟨-56709055000,-38856726338⟩,⟨104419185188,108030107515⟩,⟨-443603735806,-13300688908⟩,⟨-331195189393,-245909344549⟩,⟨-193158476131,-173283698615⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12424820458,-11544503585⟩,⟨38856726338,56709055000⟩,⟨-108030107515,-104419185188⟩,⟨13300688908,443603735806⟩,⟨245909344549,331195189393⟩,⟨173283698615,193158476131⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113821951887,-112512138283⟩,⟨-835598615128,-816887293006⟩,⟨-108030107515,-104419185188⟩,⟨2212323944460,2642626991358⟩,⟨245909344549,331195189393⟩,⟨173283698615,193158476131⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨77127636299,82158669238⟩,⟨-547101936913,-506154488423⟩,⟨627633116566,648814720422⟩,⟨3010659013341,3696216663959⟩,⟨-3920262730377,-3458669177106⟩,⟨-2611396048518,-2389629453814⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨103445968459,111571291187⟩,⟨-1320446577497,-1198343559996⟩,⟨732497409138,783686638419⟩,⟨18445009497247,21386459042821⟩,⟨-7631393818000,-6275170054565⟩,⟨-4915922775792,-4374740843788⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-111571291187,-103445968459⟩,⟨1198343559996,1320446577497⟩,⟨-783686638419,-732497409138⟩,⟨-21386459042821,-18445009497247⟩,⟨6275170054565,7631393818000⟩,⟨4374740843788,4915922775792⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨987940336589,996065659317⟩,⟨1198343559996,1320446577497⟩,⟨-783686638419,-732497409138⟩,⟨-21386459042821,-18445009497247⟩,⟨6275170054565,7631393818000⟩,⟨4374740843788,4915922775792⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120159900425,122968663401⟩,⟨776030643474,805251054087⟩,⟨182716991910,194510033680⟩,⟨-2724854597712,-2128613015627⟩,⟨-829094921296,-556535746264⟩,⟨-229196308699,-119355997635⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11513276386,11782901067⟩,⟨167182835998,173003109682⟩,⟨21370262044,22366653322⟩,⟨666688515063,817293308572⟩,⟨86586483328,113872414756⟩,⟨-20158601805,-14235438958⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166674732018,177573293737⟩,⟨1461829550620,1877628323454⟩,⟨-5509470394,235638295745⟩,⟨-10834328983230,7451415431067⟩,⟨-6357834003257,7246663813485⟩,⟨-7049021910506,5858437219034⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177573293737,-166674732018⟩,⟨-1877628323454,-1461829550620⟩,⟨-235638295745,5509470394⟩,⟨-7451415431067,10834328983230⟩,⟨-7246663813485,6357834003257⟩,⟨-5858437219034,7049021910506⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47525062368,63592169393⟩,⟨-350047830741,236564110417⟩,⟨-34697282870,293232417512⟩,⟨-14843710791871,10417031897277⟩,⟨-10808362083631,7274923958692⟩,⟨-8238516023323,9274695630933⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28385160342608,29796363227448⟩,⟨-285013815797099,-238371474818327⟩,⟨-107708916533885,-67845019368066⟩,⟨2831162728426140,4801395094373981⟩,⟨457041317280448,2374587646179413⟩,⟨-765020637359078,1415329017563553⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13131649821,13752735121⟩,⟨169616696160,180117505486⟩,⟨39936377204,43507750634⟩,⟨485946351123,714235888350⟩,⟨72470885242,163265449006⟩,⟨9461537766,42732332825⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339008680141,372694094983⟩,⟨813886438482,2034208484887⟩,⟨-316223785214,368759815193⟩,⟨-47021287564667,5866589043406⟩,⟨-21593011442392,15001615221481⟩,⟨-17848746469420,13932498976134⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372694094983,-339008680141⟩,⟨-2034208484887,-813886438482⟩,⟨-368759815193,316223785214⟩,⟨-5866589043406,47021287564667⟩,⟨-15001615221481,21593011442392⟩,⟨-13932498976134,17848746469420⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58983308651,109240305471⟩,⟨-1274320687062,305302994364⟩,⟨-590691988164,404658563750⟩,⟨-31421842897946,32991318219371⟩,⟨-26473789890790,22099595749209⟩,⟨-22781657063489,23759294754499⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234697580543,237136652209⟩,⟨1575056012080,1583390646078⟩,⟨311027594034,313054545840⟩,⟨-3980232092552,-3966343577600⟩,⟨-1574105513986,-1566242032842⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1715344869749,-1628809199786⟩,⟨-5462878351527,-2567472503035⟩,⟨-636781970467,1530079866812⟩,⟨-22122217636709,100918717404153⟩,⟨-63361081632811,47398617566489⟩,⟨-57871834390525,62295435783921⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-191843051566,-178004075912⟩,⟨-1867234562904,-1430192325383⟩,⟨-374671814074,-99552599987⟩,⟨-7322534814601,11913498809979⟩,⟨-7694589823217,7288423095824⟩,⟨-6520835942516,7866009545505⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨42854528977,59132576297⟩,⟨-292178550824,153198320695⟩,⟨-63644220040,213501945853⟩,⟨-11302766907153,7947155232379⟩,⟨-9268695337203,5722181062982⟩,⟨-6868568574396,7518959746317⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2549482289,6318103270⟩,⟨-108481025521,41161197642⟩,⟨-37610995379,52537793450⟩,⟨-3840461192228,3754481101728⟩,⟨-3073688726593,2270436503871⟩,⟨-2451209258143,2511472938197⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1670296709,3180195181⟩,⟨-31427171870,16478245720⟩,⟨-6845669664,22964595888⟩,⟨-1297163161934,1010092216684⟩,⟨-1110424861216,674982307578⟩,⟨-763510470457,891665953090⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨2978614611,5718627249⟩,⟨-80347548385,17656103194⟩,⟨-22841237475,35988334371⟩,⟨-2524180795308,2425956559818⟩,⟨-2185429645112,1456609537301⟩,⟨-1514057747315,1675588368803⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5718627249,-2978614611⟩,⟨-17656103194,80347548385⟩,⟨-35988334371,22841237475⟩,⟨-2425956559818,2524180795308⟩,⟨-1456609537301,2185429645112⟩,⟨-1675588368803,1514057747315⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3169144960,3339488659⟩,⟨-126137128715,121508746027⟩,⟨-73599329750,75379030925⟩,⟨-6266417752046,6278661897036⟩,⟨-4530298263894,4455866148983⟩,⟨-4126797626946,4025530685512⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47525062368,63592169393⟩,⟨-350047830741,236564110417⟩,⟨-34697282870,293232417512⟩,⟨-14843710791871,10417031897277⟩,⟨-10808362083631,7274923958692⟩,⟨-8238516023323,9274695630933⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3169144960,3339488659⟩,⟨-126137128715,121508746027⟩,⟨-73599329750,75379030925⟩,⟨-6266417752046,6278661897036⟩,⟨-4530298263894,4455866148983⟩,⟨-4126797626946,4025530685512⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (105/1024) u, BivariateJet2.affineZ (521/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000040

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000041Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2504150381952,-2504150324096⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-118951416704,-118951416640⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2127883415360,-2127883376320⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2127883415360,-2127883376320⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-171447135040,-171447134976⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-171447135040,-171447134976⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨82255630784,82255630848⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-88910471296,-88910471232⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨82255754048,82255754112⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-88910615360,-88910615296⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-6654861312,-6654861248⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-6654840512,-6654840448⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨171166102080,171166102144⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨171166369408,171166369472⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1956436241344,1956436279936⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1956436241344,1956436279936⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2506246686976,-2506246629120⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2134867434944,-2134867395776⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2120938281856,-2120938242880⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-172623427648,-172623427584⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-170272980992,-170272980928⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨79697016768,79697016832⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-85928392448,-85928392384⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨84836844480,84836844544⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-91934177024,-91934176960⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-7097332480,-7097332416⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-6231375616,-6231375552⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨165625409152,165625409216⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨176771021440,176771021504⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1948314815296,1948314853888⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1964594414848,1964594453440⟩



end LaneCBRB2Cell000041Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000041
open Set LaneCBRB2Cell000041Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112742891520,112742891520⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨115749368627,115749368628⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112742891520,-112742891520⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437012922368,437012922368⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46005852569,46005852570⟩,⟨-115749368628,-115749368627⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158748744089,158748744090⟩,⟨983762259148,983762259149⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46005852569,46005852570⟩,⟨-115749368628,-115749368627⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2504150381952,-2504150324096⟩,⟨10722856255644,10722856255645⟩,⟨0,0⟩,⟨-104573379102681,-104573379102661⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-256773232525,-256773226591⟩,⟨-1404638754177,-1404638696319⟩,⟨0,0⟩,⟨10722856255641,10722856255647⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256773226591,256773232525⟩,⟨1404638696319,1404638754177⟩,⟨0,0⟩,⟨-10722856255647,-10722856255641⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986768736256,986768736256⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-118951416704,-118951416640⟩,⟨-1225135916043,-1225135916042⟩,⟨0,0⟩,⟨-1365113360206,-1365113360203⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106754249953,-106754249894⟩,⟨-980560211137,-980560211071⟩,⟨0,0⟩,⟨1225135916039,1225135916045⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106754249894,106754249953⟩,⟨980560211071,980560211137⟩,⟨0,0⟩,⟨-1225135916045,-1225135916039⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨363527476485,363527482478⟩,⟨2385198907390,2385198965314⟩,⟨0,0⟩,⟨-11947992171692,-11947992171680⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2127883415360,-2127883376320⟩,⟨6813647875457,6813647875509⟩,⟨3026800573361,3026800573381⟩,⟨-42224016734888,-42224016734256⟩,⟨-26372353455157,-26372353454846⟩,⟨-8332355456348,-8332355456239⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-307226236836,-307226231196⟩,⟨-920111554486,-920111519538⟩,⟨-408737614795,-408737599271⟩,⟨6096351741596,6096351741833⟩,⟨3736530620873,3736530660025⟩,⟨1203034993497,1203034993539⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307226231196,307226236836⟩,⟨920111519538,920111554486⟩,⟨408737599271,408737614795⟩,⟨-6096351741833,-6096351741596⟩,⟨-3736530660025,-3736530620873⟩,⟨-1203034993539,-1203034993497⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158748744090,-158748744089⟩,⟨-983762259149,-983762259148⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940762883686,940762883687⟩,⟨-983762259149,-983762259148⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-171447135040,-171447134976⟩,⟨-1149766919656,-1149766919652⟩,⟨-510756533835,-510756533834⟩,⟨-1202319226227,-1202319226218⟩,⟨750946737230,750946737236⟩,⟨-237261917260,-237261917258⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146693401949,-146693401893⟩,⟨-830363953424,-830363953361⟩,⟨-368869383370,-368869383342⟩,⟨1028727003688,1028727003708⟩,⟨1385051930522,1385051930597⟩,⟨203005770769,203005770774⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146693401893,146693401949⟩,⟨830363953361,830363953424⟩,⟨368869383342,368869383370⟩,⟨-1028727003708,-1028727003688⟩,⟨-1385051930597,-1385051930522⟩,⟨-203005770774,-203005770769⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨453919633089,453919638785⟩,⟨1750475472899,1750475507910⟩,⟨777606982613,777606998165⟩,⟨-7125078745541,-7125078745284⟩,⟨-5121582590622,-5121582551395⟩,⟨-1406040764313,-1406040764266⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨817447109574,817447121263⟩,⟨4135674380289,4135674473224⟩,⟨777606982613,777606998165⟩,⟨-19073070917233,-19073070916964⟩,⟨-5121582590622,-5121582551395⟩,⟨-1406040764313,-1406040764266⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92011705138,92011705140⟩,⟨-231498737256,-231498737254⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13138826389264,13138826389550⟩,⟨33056899809498,33056899811224⟩,⟨-124806662551716,-124806662546280⟩,⟨166340370538441,166340370552181⟩,⟨-314009883203014,-314009883142893⟩,⟨2371095036109057,2371095036263926⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9768241993786,9768242133680⟩,⟨73996647994040,73996649458376⟩,⟨-83497074114086,-83497072597169⟩,⟨144429427448684,144429434836636⟩,⟨-740722054486806,-740722039595372⟩,⟨1569487712784397,1569487741646112⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨85410629632,85410762496⟩,⟨-641386985734,-641384952506⟩,⟨723732322935,723734616035⟩,⟨8338983280505,8339033748292⟩,⟨-4401891013227,-4401818250735⟩,⟨-1392277550969,-1392175328423⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1184922257408,1184922390272⟩,⟨-641386985734,-641384952506⟩,⟨723732322935,723734616035⟩,⟨8338983280505,8339033748292⟩,⟨-4401891013227,-4401818250735⟩,⟨-1392277550969,-1392175328423⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨82255630784,82255754112⟩,⟨-595155035962,-595153082556⟩,⟨671564746346,671566949461⟩,⟨7415746732033,7415796544414⟩,⟨-3721087059546,-3721016698225⟩,⟨-1702104582883,-1702006892546⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨88645290555,88645433404⟩,⟨-689369970119,-689367569001⟩,⟨777875424298,777878132433⟩,⟨9310002634355,9310066403333⟩,⟨-5122955227023,-5122867959110⟩,⟨-1054393981562,-1054274991856⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-85410762496,-85410629632⟩,⟨641384952506,641386985734⟩,⟨-723734616035,-723732322935⟩,⟨-8339033748292,-8338983280505⟩,⟨4401818250735,4401891013227⟩,⟨1392175328423,1392277550969⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1014100865280,1014100998144⟩,⟨641384952506,641386985734⟩,⟨-723734616035,-723732322935⟩,⟨-8339033748292,-8338983280505⟩,⟨4401818250735,4401891013227⟩,⟨1392175328423,1392277550969⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-88910615360,-88910471232⟩,⟨695404318161,695406613744⟩,⟨-784689820312,-784687231272⟩,⟨-9481196251478,-9481137444807⟩,⟨5268841015223,5268923807060⟩,⟨949417960390,949532685643⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-82003992959,-82003849282⟩,⟨589519922123,589522371907⟩,⟨-665211107967,-665208344923⟩,⟨-7259062766032,-7258996957579⟩,⟨3588121868826,3588211249564⟩,⟨1796092280224,1796213338289⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6641297596,6641584122⟩,⟨-99850047996,-99845197094⟩,⟨112664316331,112669787510⟩,⟨2050939868323,2051069445754⟩,⟨-1534833358197,-1534656709546⟩,⟨741698298662,741938346433⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3320648798,3320792061⟩,⟨-49925023998,-49922598547⟩,⟨56332158165,56334893755⟩,⟨1025469934161,1025534722877⟩,⟨-767416679099,-767328354773⟩,⟨370849149331,370969173217⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3320792061,-3320648798⟩,⟨49922598547,49925023998⟩,⟨-56334893755,-56332158165⟩,⟨-1025534722877,-1025469934161⟩,⟨767328354773,767416679099⟩,⟨-370969173217,-370849149331⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758802591555,758802754082⟩,⟨49922598547,49925023998⟩,⟨-56334893755,-56332158165⟩,⟨-1025534722877,-1025469934161⟩,⟨767328354773,767416679099⟩,⟨-370969173217,-370849149331⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6634741706,6634762349⟩,⟨-99646697904,-99646227008⟩,⟨112439799316,112440330488⟩,⟨2043839176220,2043853776542⟩,⟨-1528247288142,-1528229567870⟩,⟨736459675001,736481930452⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6634762349,-6634741706⟩,⟨99646227008,99646697904⟩,⟨-112440330488,-112439799316⟩,⟨-2043853776542,-2043839176220⟩,⟨1528229567870,1528247288142⟩,⟨-736481930452,-736459675001⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092876865427,1092876886070⟩,⟨99646227008,99646697904⟩,⟨-112440330488,-112439799316⟩,⟨-2043853776542,-2043839176220⟩,⟨1528229567870,1528247288142⟩,⟨-736481930452,-736459675001⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6654861312,-6654840448⟩,⟨100251168869,100251644519⟩,⟨-113122946156,-113122409622⟩,⟨-2065402617191,-2065387802650⟩,⟨1547821554881,1547839509634⟩,⟨-752591672174,-752569157212⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3327430656,-3327420224⟩,⟨50125584434,50125822260⟩,⟨-56561473078,-56561204811⟩,⟨-1032701308596,-1032693901325⟩,⟨773910777440,773919754817⟩,⟨-376295836087,-376284578606⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3327420224,3327430656⟩,⟨-50125822260,-50125584434⟩,⟨56561204811,56561473078⟩,⟨1032693901325,1032701308596⟩,⟨-773919754817,-773910777440⟩,⟨376284578606,376295836087⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765450803840,765450833536⟩,⟨-50125822260,-50125584434⟩,⟨56561204811,56561473078⟩,⟨1032693901325,1032701308596⟩,⟨-773919754817,-773910777440⟩,⟨376284578606,376295836087⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273219216356,273219221518⟩,⟨24911556752,24911674476⟩,⟨-28110082622,-28109949829⟩,⟨-510963444136,-510959794055⟩,⟨382057391967,382061822036⟩,⟨-184120482613,-184114918750⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530901607680,1530901667072⟩,⟨-100251644520,-100251168868⟩,⟨113122409622,113122946156⟩,⟨2065387802650,2065402617192⟩,⟨-1547839509634,-1547821554880⟩,⟨752569157212,752591672174⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1192115796974,1192115953161⟩,⟨-753975944625,-753973356916⟩,⟨850775944930,850778863494⟩,⟨10756530218174,10756598535356⟩,⟨-6250780074785,-6250685939339⟩,⟨-422333077413,-422204309438⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1284719966172,1284720278546⟩,⟨-1507951889250,-1507946713833⟩,⟨1701551889860,1701557726988⟩,⟨21513060436354,21513197070705⟩,⟨-12501560149568,-12501371878681⟩,⟨-844666008085,-844408765618⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨171166102080,171166369472⟩,⟨-1290561896768,-1290557153656⟩,⟨1456251698837,1456257048555⟩,⟨16896872212335,16897004760415⟩,⟨-8990022436078,-8989846144001⟩,⟨-2651648312963,-2651413808547⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨58944176190,58944280509⟩,⟨-438760517348,-438758824910⟩,⟨495091040651,495092949473⟩,⟨5617046463360,5617090696293⟩,⟨-2912536573867,-2912475353445⟩,⟨-1063828517974,-1063744561012⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380415929219,380415951166⟩,⟨9773853897,9774137825⟩,⟨-11029038651,-11028718381⟩,⟨-202750037897,-202741194109⟩,⟨152457578573,152468284813⟩,⟨-75136803493,-75123393650⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177905174347,3177905357688⟩,⟨-81650852594,-81648471304⟩,⟨92131313374,92133999466⟩,⟨1697847654104,1697921972943⟩,⟨-1278418706078,-1278328845878⟩,⟨632905116820,633017523102⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨170365640325,170365951667⟩,⟨-1272521557969,-1272516457765⟩,⟨1435894759402,1435900511746⟩,⟨16391065606854,16391200686556⟩,⟨-8560137372192,-8559952575532⟩,⟨-2957870947816,-2957619285633⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨341531742405,341532321139⟩,⟨-2563083454737,-2563073611421⟩,⟨2892146458239,2892157560301⟩,⟨33287937819189,33288205446971⟩,⟨-17550159808270,-17549798719533⟩,⟨-5609519260779,-5609033094180⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523670108078,523670332407⟩,⟨68905860014,68909222514⟩,⟨-77756471970,-77752679504⟩,⟨-1410965171600,-1410875003023⟩,⟨1053991988104,1054114621932⟩,⟨-506259526945,-506093193204⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361398847534,361399079759⟩,⟨71330685139,71334181247⟩,⟨-80492770956,-80488827791⟩,⟨-1455924983180,-1455830870991⟩,⟨1085786413629,1085914113057⟩,⟨-518099769670,-517926887830⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722797695068,722798159518⟩,⟨142661370278,142668362494⟩,⟨-160985541912,-160977655582⟩,⟨-2911849966360,-2911661741982⟩,⟨2171572827258,2171828226114⟩,⟨-1036199539340,-1035853775660⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524266845331,1524266925366⟩,⟨-605417512,-604470964⟩,⟨682079134,683146840⟩,⟨21534026108,21563440972⟩,⟨-19609941764,-19574266738⟩,⟨16087226760,16131997173⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002023566319,1002024262806⟩,⟨197375267962,197385594245⟩,⟨-222727914456,-222716267638⟩,⟨-4022735628283,-4022454879291⟩,⟨2997764609660,2998142576572⟩,⟨-1426121188163,-1425612015720⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67892633693,67892636259⟩,⟨12380616706,12380675448⟩,⟨-13970229504,-13970163242⟩,⟨-252811239573,-252809410077⟩,⟨188602192806,188604410102⟩,⟨-90067416106,-90064635649⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50475716465,50475719095⟩,⟨264574123425,264574182622⟩,⟨37629308404,37629360593⟩,⟨-1272543602220,-1272541750842⟩,⟨-219819861808,-219817904808⟩,⟨-173542376298,-173540210763⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131546109373,2131546274763⟩,⟨-279170143990,-279168808614⟩,⟨315011272968,315012779274⟩,⟨5769753996753,5769795647326⟩,⟨-4330887981350,-4330837619920⟩,⟨2118951692363,2119014691750⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2967851619981,2967851965401⟩,⟨-583052549925,-583049738344⟩,⟨657907454603,657910626078⟩,⟨12088429687884,12088517507246⟩,⟨-9088231554032,-9088125611822⟩,⟨4474088273159,4474220483397⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136246341644,136246364602⟩,⟨687384039414,687384412789⟩,⟨131773553260,131773853123⟩,⟨-3160557921656,-3160547048199⟩,⟨-872207636752,-872196477531⟩,⟨-218007759433,-217995499935⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8873086802323,8873088297472⟩,⟨-44766138418015,-44766099015324⟩,⟨-8581815995572,-8581793574763⟩,⟨657535432252491,657536928813962⟩,⟨143395025449364,143396059200178⟩,⟨30797150963085,30798038093425⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8086355666747,8086362649999⟩,⟨-39204159258339,-39204011390337⟩,⟨-9618336023578,-9618215861553⟩,⟨550698613289765,550703519804875⟩,⟨162400130672757,162404784679312⟩,⟨20034332814475,20039462663041⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16172711333494,16172725299998⟩,⟨-78408318516678,-78408022780674⟩,⟨-19236672047156,-19236431723106⟩,⟨1101397226579530,1101407039609750⟩,⟨324800261345514,324809569358624⟩,⟨40068665628950,40078925326082⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10722856255644,10722856255645⟩,⟨-104573379102681,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974382⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9623344627868,9623344627869⟩,⟨-104573379102680,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974364⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2385198907456,2385198965312⟩,⟨-11947992171781,-11947992171683⟩,⟨0,0⟩,⟨103208265737483,103208265748560⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7615341000299,7615341000348⟩,⟨-47192090303990,-47192090303333⟩,⟨-20963960656757,-20963960656485⟩,⟨584896562638631,584896562651128⟩,⟨312571055953688,312571055959655⟩,⟨115421659092987,115421659095220⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6515829372523,6515829372572⟩,⟨-47192090303991,-47192090303333⟩,⟨-20963960656758,-20963960656485⟩,⟨584896562638635,584896562651124⟩,⟨312571055953689,312571055959654⟩,⟨115421659092987,115421659095220⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1956436241344,1956436279936⟩,⟨-7963414795226,-7963414795028⟩,⟨-3537557107244,-3537557107159⟩,⟨41021697505204,41021697511843⟩,⟨27123300190755,27123300193847⟩,⟨8095093538441,8095093539712⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101182341120,101182341120⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135828419179,135828419181⟩,⟨699688822946,699688822951⟩,⟨310820073062,310820073064⟩,⟨-1760396448892,-1760396448888⟩,⟨-1564028279196,-1564028279192⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4341635148800,4341635245248⟩,⟨-19911406967007,-19911406966711⟩,⟨-3537557107244,-3537557107159⟩,⟨144229963242687,144229963260403⟩,⟨27123300190755,27123300193847⟩,⟨8095093538441,8095093539712⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨683063484810,683064642278⟩,⟨-5126166909474,-5126147222842⟩,⟨5784292916478,5784315120602⟩,⟨66575875638378,66576410893942⟩,⟨-35100319616540,-35099597439066⟩,⟨-11219038521558,-11218066188360⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5024698633610,5024699887526⟩,⟨-25037573876481,-25037554189553⟩,⟨2246735809234,2246758013443⟩,⟨210805838881065,210806374154345⟩,⟨-7977019425785,-7976297245219⟩,⟨-3123944983117,-3122972648648⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨462396902704,462397018096⟩,⟨1690165051511,1690167859963⟩,⟨206755420600,206757463939⟩,⟨-30455864289389,-30455781223998⟩,⟨1051895799630,1051979908769⟩,⟨-287480422160,-287390943270⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨225485783040,225485783040⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-225485783040,-225485783040⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨874025844736,874025844736⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1896046787762,1896046833754⟩,⟨-14268118270302,-14268118154511⟩,⟨0,0⟩,⟨129834476802270,129834476811468⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨796535159986,796535205978⟩,⟨-14268118270302,-14268118154511⟩,⟨0,0⟩,⟨129834476802270,129834476811468⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33328687219,33328689145⟩,⟨-680861733397,-680861723695⟩,⟨316591611439,316591629720⟩,⟨8436652145881,8436652170792⟩,⟨-6467554870054,-6467554778038⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨495725589923,495725707241⟩,⟨1009303318114,1009306136268⟩,⟨523347032039,523349093659⟩,⟨-22019212143508,-22019129053206⟩,⟨-5415659070424,-5415574869269⟩,⟨-287480422160,-287390943270⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506844853278,506844865574⟩,⟨2538898610666,2538898733883⟩,⟨0,0⟩,⟨3504487769187,3504490687699⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228515967947,228516027572⟩,⟨1609948598078,1609950234914⟩,⟨241248698937,241249655141⟩,⟨-3909028935564,-3908975456086⟩,⟨-1288002696132,-1287959001966⟩,⟨-132520632110,-132479381568⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-683064642278,-683063484810⟩,⟨5126147222842,5126166909474⟩,⟨-5784315120602,-5784292916478⟩,⟨-66576410893942,-66575875638378⟩,⟨35099597439066,35100319616540⟩,⟨11218066188360,11219038521558⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3658570506522,3658571760438⟩,⟨-14785259744165,-14785240057237⟩,⟨-9321872227846,-9321850023637⟩,⟨77653552348745,77654087622025⟩,⟨62222897629821,62223619810387⟩,⟨19313159726801,19314132061270⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451962340190,451962495100⟩,⟨501679490427,501682720448⟩,⟨-117341202328,-117338104832⟩,⟨-15082277469235,-15082184280152⟩,⟨-7629239183873,-7629128490042⟩,⟨-4040456990823,-4040323923234⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨317497488178,317497488180⟩,⟨1967524518296,1967524518298⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-317497488180,-317497488178⟩,⟨-1967524518298,-1967524518296⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨782014139596,782014139598⟩,⟨-1967524518298,-1967524518296⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1391491245111,1391491272564⟩,⟨-9164831970896,-9164831901677⟩,⟨-4071258035532,-4071258004786⟩,⟨57676493448940,57676493454476⟩,⟨35864571819558,35864571899309⟩,⟨11381698901627,11381698902683⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1391491272564,-1391491245111⟩,⟨9164831901677,9164831970896⟩,⟨4071258004786,4071258035532⟩,⟨-57676493454476,-57676493448940⟩,⟨-35864571899309,-35864571819558⟩,⟨-11381698902683,-11381698901627⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-291979644788,-291979617335⟩,⟨9164831901677,9164831970896⟩,⟨4071258004786,4071258035532⟩,⟨-57676493454476,-57676493448940⟩,⟨-35864571899309,-35864571819558⟩,⟨-11381698902683,-11381698901627⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12217035412,-12217034262⟩,⟨414213319932,414213325730⟩,⟨54299396376,54299408580⟩,⟨-4342931136351,-4342931121475⟩,⟨2005398712095,2005398773672⟩,⟨2760098100277,2760098124774⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439745304778,439745460838⟩,⟨915892810359,915896046178⟩,⟨-63041805952,-63038696252⟩,⟨-19425208605586,-19425115401627⟩,⟨-5623840471778,-5623729716370⟩,⟨-1280358890546,-1280225798460⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101182341120,-101182341120⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4233679526,4233679528⟩,⟨25919245720,25919245723⟩,⟨40216028160,40216028160⟩,⟨-276035115420,-276035115416⟩,⟨246208790528,246208790528⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9184230093,9184230321⟩,⟨10221435072,10221436466⟩,⟨87241666214,87241668331⟩,⟨-764715732765,-764715717928⟩,⟨97094151476,97094164437⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1478904002679,1478904023827⟩,⟨-7482154561509,-7482154179385⟩,⟨-1406826331727,-1406826263355⟩,⟨110214771423190,110214779061010⟩,⟨23500822383926,23500823935158⟩,⟨5220295055934,5220295350656⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12353297866,12353298351⟩,⟨-48750107044,-48750100227⟩,⟨105593637555,105593642946⟩,⟨-247073411476,-247073264078⟩,⟨-279856561267,-279856476988⟩,⟨-179646450776,-179646430963⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12353298351,-12353297866⟩,⟨48750100227,48750107044⟩,⟨-105593642946,-105593637555⟩,⟨247073264078,247073411476⟩,⟨279856476988,279856561267⟩,⟨179646430963,179646450776⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113535639471,-113535638986⟩,⟨-825275744509,-825275737692⟩,⟨-105593642946,-105593637555⟩,⟨2446096519630,2446096667028⟩,⟨279856476988,279856561267⟩,⟨179646430963,179646450776⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨81861360085,81861361703⟩,⟨-539166604710,-539166600628⟩,⟨629588238118,629588253465⟩,⟨3393105213793,3393105214166⟩,⟨-3614276519409,-3614276480570⟩,⟨-2473365983951,-2473365983821⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨110108060739,110108064490⟩,⟨-1282273862760,-1282273807436⟩,⟨742089329103,742089369017⟩,⟨20107712080876,20107713307805⟩,⟨-6706178912976,-6706178279145⟩,⟨-4549268050123,-4549267855176⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-110108064490,-110108060739⟩,⟨1282273807436,1282273862760⟩,⟨-742089369017,-742089329103⟩,⟨-20107713307805,-20107712080876⟩,⟨6706178279145,6706178912976⟩,⟨4549267855176,4549268050123⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨989403563286,989403567037⟩,⟨1282273807436,1282273862760⟩,⟨-742089369017,-742089329103⟩,⟨-20107713307805,-20107712080876⟩,⟨6706178279145,6706178912976⟩,⟨4549267855176,4549268050123⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122226194372,122226194838⟩,⟨788026080801,788026090031⟩,⟨188019532236,188019538232⟩,⟨-2436132613947,-2436132385906⟩,⟨-688706461566,-688706336865⟩,⟨-170168921083,-170168873234⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11723697134,11723697235⟩,⟨170436047880,170436050018⟩,⟨21807211146,21807212354⟩,⟨733709191851,733709244921⟩,⟨100717758840,100717785898⟩,⟨-16818846010,-16818839684⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172443805703,172443956110⟩,⟨1670903308139,1670908665076⟩,⟨115648446773,115651305805⟩,⟨-1772326615437,-1772119791518⟩,⟨407680892303,407825089340⟩,⟨-583213532646,-583094251586⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172443956110,-172443805703⟩,⟨-1670908665076,-1670903308139⟩,⟨-115651305805,-115648446773⟩,⟨1772119791518,1772326615437⟩,⟨-407825089340,-407680892303⟩,⟨583094251586,583213532646⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56072011837,56072221869⟩,⟨-60960066998,-60953073225⟩,⟨125597393132,125601208368⟩,⟨-2136909144046,-2136648840649⟩,⟨-1695827785472,-1695639894269⟩,⟨450573619476,450734151078⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28777211422168,28777236841375⟩,⟨-256651218412969,-256650588279716⟩,⟨-86263082654842,-86262609417695⟩,⟨3698948366653493,3698970671354877⟩,⟨1368488347111028,1368507957572574⟩,⟨314149794676736,314169701145712⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13587161984,13587162089⟩,⟨175200382586,175200385308⟩,⟨41802035216,41802036710⟩,⟨587944458854,587944538082⟩,⟨116390447044,116390487106⟩,⟨26470379084,26470393973⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355613004140,355613321006⟩,⟨1413915693779,1413927626767⟩,⟨28081120908,28087982661⟩,⟨-20693889461049,-20693395726012⟩,⟨-3545759341460,-3545413209544⟩,⟨-1984333041832,-1984049798774⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355613321006,-355613004140⟩,⟨-1413927626767,-1413915693779⟩,⟨-28087982661,-28081120908⟩,⟨20693395726012,20693889461049⟩,⟨3545413209544,3545759341460⟩,⟨1984049798774,1984333041832⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84131983772,84132456698⟩,⟨-498034816408,-498019647601⟩,⟨-91129788613,-91119817160⟩,⟨1268187120426,1268774059422⟩,⟨-2078427262234,-2077970374910⟩,⟨703690908228,704107243372⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237010760299,237010760301⟩,⟨1573714667682,1573714667687⟩,⟨310820073062,310820073064⟩,⟨-3959419704444,-3959419704440⟩,⟨-1564028279196,-1564028279192⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1669996626265,-1669995176948⟩,⟨-4042570203331,-4042529047721⟩,⟨433177398646,433203643605⟩,⟨39951863098821,39953355039935⟩,⟨-7454832872593,-7453657500144⟩,⟨2198678932737,2199787289334⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185643632923,-185643471102⟩,⟨-1646284440613,-1646278811120⟩,⟨-237420290065,-237417115438⟩,⟨2346670896709,2346899382219⟩,⟨-163496851591,-163339218704⟩,⟨651024474699,651156962700⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51367127376,51367289199⟩,⟨-72569772931,-72564143433⟩,⟨73399782997,73402957626⟩,⟨-1612748807735,-1612520322221⟩,⟨-1727525130787,-1727367497896⟩,⟨303633343051,303765831052⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4290495407,4290535598⟩,⟨-30063018969,-30061588897⟩,⟨4963029018,4963900900⟩,⟨-43621145512,-43562116365⟩,⟨-287596716753,-287553320024⟩,⟨49542899650,49579653954⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2399776144,2399791265⟩,⟨-6780669562,-6780122200⟩,⟨6858201236,6858519470⟩,⟨-141111703671,-141088393946⟩,⟨-171103454632,-171087046820⟩,⟨38170220707,38183537037⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4270085827,4270112818⟩,⟨-29446238113,-29445154397⟩,⟨4482203441,4482818591⟩,⟨-63343863665,-63293889217⟩,⟨-273117005660,-273083365143⟩,⟨41454047181,41479902278⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4270112818,-4270085827⟩,⟨29445154397,29446238113⟩,⟨-4482818591,-4482203441⟩,⟨63293889217,63343863665⟩,⟨273083365143,273117005660⟩,⟨-41479902278,-41454047181⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨20382589,20449771⟩,⟨-617864572,-615350784⟩,⟨480210427,481697459⟩,⟨19672743705,19781747300⟩,⟨-14513351610,-14436314364⟩,⟨8062997372,8125606773⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56072011837,56072221869⟩,⟨-60960066998,-60953073225⟩,⟨125597393132,125601208368⟩,⟨-2136909144046,-2136648840649⟩,⟨-1695827785472,-1695639894269⟩,⟨450573619476,450734151078⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨20382589,20449771⟩,⟨-617864572,-615350784⟩,⟨480210427,481697459⟩,⟨19672743705,19781747300⟩,⟨-14513351610,-14436314364⟩,⟨8062997372,8125606773⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112528143155,112957639885⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨113816633344,117682103911⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112957639885,-112528143155⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436798174003,437227670733⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨45215435980,46797024134⟩,⟨-117682103911,-113816633344⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157743579135,159754664019⟩,⟨981829523865,985694994432⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44785939250,47226520864⟩,⟨-117682103911,-113816633344⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2506246686976,-2502058008320⟩,⟨10702470597344,10743319721800⟩,⟨0,0⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-257477686983,-256069999288⟩,⟨-1410915711782,-1398349771273⟩,⟨0,0⟩,⟨10620616435743,10824862650847⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256069999288,257477686983⟩,⟨1398349771273,1410915711782⟩,⟨0,0⟩,⟨-10824862650847,-10620616435743⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986553987891,986983484621⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-119190727104,-118712158336⟩,⟨-1225402597783,-1224869350350⟩,⟨0,0⟩,⟨-1365707727613,-1364519380719⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106992301127,-106516338944⟩,⟨-981278142331,-979842436080⟩,⟨0,0⟩,⟨1223802623334,1226468860601⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106516338944,106992301127⟩,⟨979842436080,981278142331⟩,⟨0,0⟩,⟨-1226468860601,-1223802623334⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨362586338232,364469988110⟩,⟨2378192207353,2392193854113⟩,⟨0,0⟩,⟨-12051331511448,-11844419059077⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2134867434944,-2120938242880⟩,⟨6757442636258,6870537068841⟩,⟨3006263849989,3047584634459⟩,⟨-42932042210230,-41530284745321⟩,⟨-26707361161772,-26043461388815⟩,⟨-8447179520036,-8219669630993⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310187742612,-304284539703⟩,⟨-944405616936,-895669876709⟩,⟨-417643874593,-399773937092⟩,⟨5830515322721,6360434997451⟩,⟨3609464292369,3862715488626⟩,⟨1161229005775,1244531227052⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨304284539703,310187742612⟩,⟨895669876709,944405616936⟩,⟨399773937092,417643874593⟩,⟨-6360434997451,-5830515322721⟩,⟨-3862715488626,-3609464292369⟩,⟨-1244531227052,-1161229005775⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159754664019,-157743579135⟩,⟨-985694994432,-981829523865⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939756963757,941768048641⟩,⟨-985694994432,-981829523865⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-172623427648,-170272980928⟩,⟨-1153258927167,-1146283290817⟩,⟨-511554504513,-509960676623⟩,⟨-1209633549561,-1195044553975⟩,⟨747116062081,754770221803⟩,⟨-238003859602,-236523093646⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147857671078,-145532994398⟩,⟨-835755936010,-824978684639⟩,⟨-370519738079,-367220634792⟩,⟨1011099200453,1046347881118⟩,⟨1376697539659,1393413900123⟩,⟨201321521942,204688462491⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145532994398,147857671078⟩,⟨824978684639,835755936010⟩,⟨367220634792,370519738079⟩,⟨-1046347881118,-1011099200453⟩,⟨-1393413900123,-1376697539659⟩,⟨-204688462491,-201321521942⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨449817534101,458045413690⟩,⟨1720648561348,1780161552946⟩,⟨766994571884,788163612672⟩,⟨-7406782878569,-6841614523174⟩,⟨-5256129388749,-4986161832028⟩,⟨-1449219689543,-1362550527717⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨812403872333,822515401800⟩,⟨4098840768701,4172355407059⟩,⟨766994571884,788163612672⟩,⟨-19458114390017,-18686033582251⟩,⟨-5256129388749,-4986161832028⟩,⟨-1449219689543,-1362550527717⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89571878500,94453041728⟩,⟨-235364207822,-227633266688⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12799225916895,13496711689648⟩,⟨30846329067205,35464734113354⟩,⟨-131763136230752,-118380062872958⟩,⟨148680244117945,186378340836239⟩,⟨-394469576453077,-239246162278246⟩,⟨2189794816779853,2572704295473670⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9457053872893,10096531003355⟩,⟨70505544660989,77746670308257⟩,⟨-89640045313618,-77793451455826⟩,⟨100986861439592,191062318540703⟩,⟨-838100670156517,-650700290285217⟩,⟨1411295915663427,1743551896644011⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨82656466944,88195621120⟩,⟨-718751695329,-572182164561⟩,⟨631326595046,828703458078⟩,⟨6110608532421,10856099154487⟩,⟨-8181037647489,-943085563878⟩,⟨-6529248243151,4067807942984⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1182168094720,1187707248896⟩,⟨-718751695329,-572182164561⟩,⟨631326595046,828703458078⟩,⟨6110608532421,10856099154487⟩,⟨-8181037647489,-943085563878⟩,⟨-6529248243151,4067807942984⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨79697016768,84836844544⟩,⟨-668497018342,-529693612399⟩,⟨584446152721,770761021386⟩,⟨5250410340601,9841865601084⟩,⟨-7327465521491,-404436365280⟩,⟨-6613033055685,3472726561046⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨85688289316,91641900543⟩,⟨-777577388720,-610987717771⟩,⟨674143339947,896528071020⟩,⟨6639336183897,12342951817031⟩,⟨-9554159002301,-1111486383562⟩,⟨-6976111141240,5226999881081⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-88195621120,-82656466944⟩,⟨572182164561,718751695329⟩,⟨-828703458078,-631326595046⟩,⟨-10856099154487,-6110608532421⟩,⟨943085563878,8181037647489⟩,⟨-4067807942984,6529248243151⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1011316006656,1016855160832⟩,⟨572182164561,718751695329⟩,⟨-828703458078,-631326595046⟩,⟨-10856099154487,-6110608532421⟩,⟨943085563878,8181037647489⟩,⟨-4067807942984,6529248243151⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-91934177024,-85928392384⟩,⟨618692776880,781433143842⟩,⟨-900973664155,-682644843547⟩,⟨-12358217972736,-6955454797185⟩,⟨1403868321333,9534826212364⟩,⟨-5160842001554,6674827773254⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-85022968382,-79035779566⟩,⟨508967844204,677971576452⟩,⟨-783903343099,-558596627091⟩,⟨-10307697277349,-4468168694674⟩,⟨-570721709520,8033844102904⟩,⟨-4534873549288,7871297954512⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨665320934,12606120977⟩,⟨-268609544516,66983858681⟩,⟨-109760003152,337931443929⟩,⟨-3668361093452,7874783122357⟩,⟨-10124880711821,6922357719342⟩,⟨-11510984690528,13098297835593⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨332660467,6303060489⟩,⟨-134304772258,33491929341⟩,⟨-54880001576,168965721965⟩,⟨-1834180546726,3937391561179⟩,⟨-5062440355911,3461178859671⟩,⟨-5755492345264,6549148917797⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6303060489,-332660467⟩,⟨-33491929341,134304772258⟩,⟨-168965721965,54880001576⟩,⟨-3937391561179,1834180546726⟩,⟨-3461178859671,5062440355911⟩,⟨-6549148917797,5755492345264⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755820323127,761790742413⟩,⟨-33491929341,134304772258⟩,⟨-168965721965,54880001576⟩,⟨-3937391561179,1834180546726⟩,⟨-3461178859671,5062440355911⟩,⟨-6549148917797,5755492345264⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6213751046,7074475057⟩,⟨-115307106536,-86028296520⟩,⟨94920734834,132946327012⟩,⟨1514260914717,2681307537222⟩,⟨-2395906835128,-798874568196⟩,⟨-322466502693,1901775739606⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7074475057,-6213751046⟩,⟨86028296520,115307106536⟩,⟨-132946327012,-94920734834⟩,⟨-2681307537222,-1514260914717⟩,⟨798874568196,2395906835128⟩,⟨-1901775739606,322466502693⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092437152719,1093297876730⟩,⟨86028296520,115307106536⟩,⟨-132946327012,-94920734834⟩,⟨-2681307537222,-1514260914717⟩,⟨798874568196,2395906835128⟩,⟨-1901775739606,322466502693⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7097332480,-6231375552⟩,⟨86517237758,116053819743⟩,⟨-133807269422,-95460216184⟩,⟨-2710920841174,-1529674985559⟩,⟨810926441474,2425545805330⟩,⟨-1930375325363,316266842588⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3548666240,-3115687776⟩,⟨43258618879,58026909872⟩,⟨-66903634711,-47730108092⟩,⟨-1355460420587,-764837492779⟩,⟨405463220737,1212772902665⟩,⟨-965187662682,158133421294⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3115687776,3548666240⟩,⟨-58026909872,-43258618879⟩,⟨47730108092,66903634711⟩,⟨764837492779,1355460420587⟩,⟨-1212772902665,-405463220737⟩,⟨-158133421294,965187662682⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765239071392,765672069120⟩,⟨-58026909872,-43258618879⟩,⟨47730108092,66903634711⟩,⟨764837492779,1355460420587⟩,⟨-1212772902665,-405463220737⟩,⟨-158133421294,965187662682⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273109288179,273324469183⟩,⟨21507074130,28826776634⟩,⟨-33236581753,-23730183708⟩,⟨-670326884306,-378565228679⟩,⟨199718642049,598976708782⟩,⟨-475443934902,80616625674⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530478142784,1531344138240⟩,⟨-116053819744,-86517237758⟩,⟨95460216184,133807269422⟩,⟨1529674985558,2710920841174⟩,⟨-2425545805330,-810926441474⟩,⟨-316266842588,1930375325364⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1188886939045,1195398680193⟩,⟨-849580964139,-668984068137⟩,⟨738134566290,979546465733⟩,⟨7897274348845,14039768009668⟩,⟨-11062519428735,-1933330382509⟩,⟨-6801161738958,6413583183337⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1278262250314,1291285732610⟩,⟨-1699161928278,-1337968136274⟩,⟨1476269132580,1959092931466⟩,⟨15794548697698,28079536019331⟩,⟨-22125038857466,-3866660765018⟩,⟨-13597706007156,12827166366671⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨165625409152,176771021504⟩,⟨-1461553211916,-1139261037487⟩,⟨1257022389395,1685135782984⟩,⟨11506029920364,22972480739530⟩,⟨-17728634498863,-1052398518278⟩,⟨-14278895791911,9596333794981⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨56819260457,61105863725⟩,⟨-500669765740,-382553312826⟩,⟨420429782269,578564866734⟩,⟨3709099342489,7712503510592⟩,⟨-6006939233305,-30536226161⟩,⟨-5303783909167,3362753113191⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380157686003,380672485082⟩,⟨1087535740,18658333106⟩,⟨-22578727069,231260310⟩,⟨-559724515929,143567127916⟩,⟨-321224309544,639813509475⟩,⟨-748883705586,588024733012⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175763594666,3180064126351⟩,⟨-156079169126,-9072776589⟩,⟨-1934519919,188873729546⟩,⟨-1200904210983,4697482843970⟩,⟨-5370655920244,2687269337807⟩,⟨-4919126419659,6286936583742⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨164113352034,176733524442⟩,⟨-1456737039570,-1105412950298⟩,⟨1214236714196,1683851833012⟩,⟨10652713184111,22709707743154⟩,⟨-17840189524025,58558879336⟩,⟨-15615295435623,10274098385250⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨329738761186,353504545946⟩,⟨-2918290251486,-2244673987785⟩,⟨2471259103591,3368987615996⟩,⟨22158743104475,45682188482684⟩,⟨-35568824022888,-993839638942⟩,⟨-29894191227534,19870432180231⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519561909506,527802635794⟩,⟨-46409407728,186104684268⟩,⟨-234133990996,76046630320⟩,⟨-5464183353078,2574414852028⟩,⟨-4837396620026,7028376500358⟩,⟨-9091952698056,8027255174695⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357154431483,365685229344⟩,⟨-48231764370,193412450603⟩,⟨-243327722490,79032750777⟩,⟨-5687248583160,2709603198095⟩,⟨-5070245526698,7318293106709⟩,⟨-9466495616332,8396431391560⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714308862966,731370458688⟩,⟨-96463528740,386824901206⟩,⟨-486655444980,158065501554⟩,⟨-11374497166320,5419206396190⟩,⟨-10140491053396,14636586213418⟩,⟨-18932991232664,16792862783120⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523403667727,1525130387194⟩,⟨-30025523224,28789868778⟩,⟨-37486110828,38886534588⟩,⟨-1151632551664,1196659926457⟩,⟨-1626671237134,1584980393654⟩,⟨-2218042582194,2252841828057⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989694619176,1014482505381⟩,⟨-153776672625,555714423979⟩,⟨-699973717295,245118792215⟩,⟨-16564709344555,8333219143337⟩,⟨-15173811009810,21383643434687⟩,⟨-27771729726493,24825069812819⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67838012264,67944952620⟩,⟨10684346682,14331932876⟩,⟨-16524374706,-11788749508⟩,⟨-332427927052,-186553183233⟩,⟨97474026274,296867481960⟩,⟨-235354199531,42089899192⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50123948180,50827811724⟩,⟨260785977800,268554436822⟩,⟨34960825789,39994587106⟩,⟨-1371446049925,-1181964824822⟩,⟨-308036682447,-119232509320⟩,⟨-289307935297,-69027867382⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130367052395,2132778599591⟩,⟨-323267771066,-240857373432⟩,⟨265753941448,372719983140⟩,⟨4272113734965,7575765682200⟩,⟨-6784601638630,-2272580146930⟩,⟨-864385079047,5409625963603⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2965389476046,2970426072941⟩,⟨-675346481744,-502896380885⟩,⟨554878986911,778658288328⟩,⟨8948356948386,15877895970901⟩,⟨-14232885670049,-4776384056919⟩,⟨-1771204843144,11369418169995⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135184589845,137315743974⟩,⟨672121687098,702597343667⟩,⟨119585084079,144044371331⟩,⟨-3627052785744,-2692326228900⟩,⟨-1383097851995,-365118094085⟩,⟨-828182460479,396059811598⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8803985505431,8942778322595⟩,⟨-46478465494203,-43093016283818⟩,⟨-9528873689730,-7667185979027⟩,⟨594474459711066,723064825119755⟩,⟨98466919872572,190544352751079⟩,⟨-12845939855105,75092977732335⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7924661151290,8251201650431⟩,⟨-44134850045608,-34269119565437⟩,⟨-14485145074677,-4907751359662⟩,⟨353389753407054,747926018809869⟩,⟨-49960295004500,380652743921886⟩,⟨-241979992867730,283330819585785⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15849322302580,16502403300862⟩,⟨-88269700091216,-68538239130874⟩,⟨-28970290149354,-9815502719324⟩,⟨706779506814108,1495852037619738⟩,⟨-99920590009000,761305487843772⟩,⟨-483959985735460,566661639171570⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10702470597344,10743319721800⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803854,2051378711294242⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9602958969568,9643808094024⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803861,2051378711294240⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2382867281216,2387534528576⟩,⟨-12019099426619,-11877349255562⟩,⟨0,0⟩,⟨99839973091184,106573343585493⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7567389828886,7663867057182⟩,⟨-47889336844526,-46508105401613⟩,⟨-21242416081809,-20690613820406⟩,⟨571664448893874,598493832499157⟩,⟨306405728063588,318894738042007⟩,⟨113143768180422,117757846691714⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6467878201110,6564355429406⟩,⟨-47889336844526,-46508105401613⟩,⟨-21242416081809,-20690613820405⟩,⟨571664448893882,598493832499153⟩,⟨306405728063592,318894738042006⟩,⟨113143768180423,117757846691715⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1948314815296,1964594453440⟩,⟨-8140982416499,-7789980787098⟩,⟨-3611119869281,-3465621373788⟩,⟨35474933526017,46549796275862⟩,⟨24584740750000,29657000226493⟩,⟨7091291806407,9094815456858⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100967634698,101397131429⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134824064825,136835149710⟩,⟨695956041102,703420253801⟩,⟨309805696940,311833849039⟩,⟨-1767320322048,-1753486165276⟩,⟨-1567960019766,-1560096538620⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4331182096512,4352128982016⟩,⟨-20160081843118,-19667330042660⟩,⟨-3611119869281,-3465621373788⟩,⟨135314906617201,153123139861355⟩,⟨24584740750000,29657000226493⟩,⟨7091291806407,9094815456858⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨659477522372,707009091892⟩,⟨-5836580502972,-4489347975570⟩,⟨4942518207182,6737975231992⟩,⟨44317486208950,91364376965368⟩,⟨-71137648045776,-1987679277884⟩,⟨-59788382455068,39740864360462⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4990659618884,5059138073908⟩,⟨-25996662346090,-24156678018230⟩,⟨1331398337901,3272353858204⟩,⟨179632392826151,244487516826723⟩,⟨-46552907295776,27669320948609⟩,⟨-52697090648661,48835679817320⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458289921245,466554491321⟩,⟨1567818825220,1805299389418⟩,⟨122261682025,301776976124⟩,⟨-34973659200139,-25821113994794⟩,⟨-3235278685444,5154212961545⟩,⟨-4859733804941,4503633904153⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨225056286310,225915279770⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-225915279770,-225056286310⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨873596348006,874455341466⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1893262519527,1898836054759⟩,⟨-14334009069890,-14202659713135⟩,⟨0,0⟩,⟨126835375642316,132835510026853⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨793750891751,799324426983⟩,⟨-14334009069890,-14202659713135⟩,⟨0,0⟩,⟨126835375642316,132835510026853⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32331517302,34332799013⟩,⟨-701230927625,-660676513973⟩,⟨315329944105,317856354168⟩,⟨8106725776474,8773960576411⟩,⟨-6499332721185,-6435979379349⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨490621438547,500887290334⟩,⟨866587897595,1144622875445⟩,⟨437591626130,619633330292⟩,⟨-26866933423665,-17047153418383⟩,⟨-9734611406629,-1281766417804⟩,⟨-4859733804941,4503633904153⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506349041299,507340811276⟩,⟨2518951804351,2559009350623⟩,⟨0,0⟩,⟨2371496934072,4641016220299⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225941853431,231121306785⟩,⟨1523083218698,1693924021136⟩,⟨201520470337,285913553384⟩,⟨-7368178799703,-408347176644⟩,⟨-3489270450053,851856647706⟩,⟨-2242396741335,2078083779110⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-707009091892,-659477522372⟩,⟨4489347975570,5836580502972⟩,⟨-6737975231992,-4942518207182⟩,⟨-91364376965368,-44317486208950⟩,⟨1987679277884,71137648045776⟩,⟨-39740864360462,59788382455068⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3624173004620,3692651459644⟩,⟨-15670733867548,-13830749539688⟩,⟨-10349095101273,-8408139580970⟩,⟨43950529651833,108805653652405⟩,⟨26572420027884,100794648272269⟩,⟨-32649572554055,68883197911926⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨444402518143,459553589560⟩,⟨343750690928,666448572179⟩,⟨-266782566559,16256455546⟩,⟨-20597082854434,-9747679275801⟩,⟨-13072855415148,-1817488291375⟩,⟨-11101347698134,2690371820431⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨315487158270,319509328038⟩,⟨1963659047730,1971389988864⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-319509328038,-315487158270⟩,⟨-1971389988864,-1963659047730⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨780002299738,784024469506⟩,⟨-1971389988864,-1963659047730⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1382150036574,1400885707111⟩,⟨-9327515052104,-9005842861127⟩,⟨-4137433691960,-4006536390973⟩,⟨52991037811626,62386135870478⟩,⟨33716006732652,38025840584247⟩,⟨10537707811213,12229142139906⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1400885707111,-1382150036574⟩,⟨9005842861127,9327515052104⟩,⟨4006536390973,4137433691960⟩,⟨-62386135870478,-52991037811626⟩,⟨-38025840584247,-33716006732652⟩,⟨-12229142139906,-10537707811213⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-301374079335,-282638408798⟩,⟨9005842861127,9327515052104⟩,⟨4006536390973,4137433691960⟩,⟨-62386135870478,-52991037811626⟩,⟨-38025840584247,-33716006732652⟩,⟨-12229142139906,-10537707811213⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12944700980,-11512590032⟩,⟨396088656467,432894394124⟩,⟨43353255643,65429647031⟩,⟨-4676297374771,-4022952298312⟩,⟨1784219310722,2222439863387⟩,⟨2658048945602,2861324765063⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨431457817163,448040999528⟩,⟨739839347395,1099342966303⟩,⟨-223429310916,81686102577⟩,⟨-25273380229205,-13770631574113⟩,⟨-11288636104426,404951572012⟩,⟨-8443298752532,5551696585494⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101397131429,-100967634698⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4112671698,4355237018⟩,⟨24731166570,27108114565⟩,⟨40110970503,40321203045⟩,⟨-281641138262,-270433622423⟩,⟨245652667759,246764997182⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8913003355,9457179441⟩,⟨5989077998,14437247409⟩,⟨86928702539,87555476515⟩,⟨-830777170503,-698252429351⟩,⟨91616271808,102543659135⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1469791102961,1488084757823⟩,⟨-7642526946158,-7324409586864⟩,⟨-1443683737401,-1370578344559⟩,⟨106390400665888,114142735962495⟩,⟨22570010298602,24456664967823⟩,⟨4990930182247,5455758966378⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11914610724,12799395862⟩,⟨-57729316866,-39834630485⟩,⟨103785948724,107387678039⟩,⟨-462644449002,-31422853685⟩,⟨-322110781004,-237401034207⟩,⟨-189466534423,-169792749974⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12799395862,-11914610724⟩,⟨39834630485,57729316866⟩,⟨-107387678039,-103785948724⟩,⟨31422853685,462644449002⟩,⟨237401034207,322110781004⟩,⟨169792749974,189466534423⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114196527291,-112882245422⟩,⟨-834620710981,-815867031140⟩,⟨-107387678039,-103785948724⟩,⟨2230446109237,2661667704554⟩,⟨237401034207,322110781004⟩,⟨169792749974,189466534423⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨79359878289,84383792405⟩,⟨-559946679059,-518986998268⟩,⟨618892705328,640069582463⟩,⟨3057754831203,3742098490320⟩,⟨-3841761246759,-3382668231694⟩,⟨-2583122199505,-2362901508408⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨106085683947,114205463693⟩,⟨-1344372799919,-1222421566088⟩,⟨716517645908,767348737100⟩,⟨18680963680748,21608840896040⟩,⟨-7372500271847,-6032412130864⟩,⟨-4816630512214,-4282879546059⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-114205463693,-106085683947⟩,⟨1222421566088,1344372799919⟩,⟨-767348737100,-716517645908⟩,⟨-21608840896040,-18680963680748⟩,⟨6032412130864,7372500271847⟩,⟨4282879546059,4816630512214⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨985306164083,993425943829⟩,⟨1222421566088,1344372799919⟩,⟨-767348737100,-716517645908⟩,⟨-21608840896040,-18680963680748⟩,⟨6032412130864,7372500271847⟩,⟨4282879546059,4816630512214⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120819988422,123632696841⟩,⟨773563098571,802859524706⟩,⟨182129209444,193886093494⟩,⟨-2738531739547,-2141901926117⟩,⟨-823450424386,-552790331415⟩,⟨-224265030704,-115349800095⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11589146498,11860581113⟩,⟨167523289638,173369311232⟩,⟨21310535766,22306812582⟩,⟨657902644594,809111890878⟩,⟨87114315220,114286410080⟩,⟨-19763132726,-13887026358⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167056094195,178013663490⟩,⟨1462649991398,1879662340745⟩,⟨-5317748572,231341544914⟩,⟨-10903233406495,7394612651868⟩,⟨-6180915360856,7103712068750⟩,⟨-6692658206350,5531991641806⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178013663490,-167056094195⟩,⟨-1879662340745,-1462649991398⟩,⟨-231341544914,5317748572⟩,⟨-7394612651868,10903233406495⟩,⟨-7103712068750,6180915360856⟩,⟨-5531991641806,6692658206350⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47928189941,64065212590⟩,⟨-356579122047,231274029738⟩,⟨-29821074577,291231301956⟩,⟨-14762791451571,10494886229851⟩,⟨-10592982518803,7032772008562⟩,⟨-7774388383141,8770741985460⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28084713862443,29486300257580⟩,⟨-279906033309370,-233740122838392⟩,⟨-105962524496682,-67349391883465⟩,⟨2734946766770047,4678559235523025⟩,⟨461421411281644,2309814051645192⟩,⟨-700637703852655,1339300985513552⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13276321262,13901666288⟩,⟨170006177746,180552321080⟩,⟨40026587114,43602377662⟩,⟨472624020632,701764020956⟩,⟨71091633646,161663002344⟩,⟨9903593999,43028659527⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339115725900,372809796544⟩,⟨803460888872,2019633929146⟩,⟨-317341262963,356085944297⟩,⟨-46831542661068,5691312338501⟩,⟨-21112811043440,14616922166634⟩,⟨-17009668196193,13183797574765⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372809796544,-339115725900⟩,⟨-2019633929146,-803460888872⟩,⟨-356085944297,317341262963⟩,⟨-5691312338501,46831542661068⟩,⟨-14616922166634,21112811043440⟩,⟨-13183797574765,17009668196193⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58648020619,108925273628⟩,⟨-1279794581751,295882077431⟩,⟨-579515255213,399027365540⟩,⟨-30964692567706,33060911086955⟩,⟨-25905558271060,21517762615452⟩,⟨-21627096327297,22561364781687⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235791699523,238232281139⟩,⟨1569552389108,1577875595267⟩,⟨309805696940,311833849039⟩,⟨-3966343577600,-3952509420828⟩,⟨-1567960019766,-1560096538620⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1713958362338,-1627183419197⟩,⟨-5490162262048,-2592829621017⟩,⟨-604048896677,1512825818158⟩,⟨-21494879015309,101394558316698⟩,⟨-61895067281873,45824407330069⟩,⟨-54553555673543,58767279610373⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192723104746,-178803276747⟩,⟨-1868858237418,-1429720844033⟩,⟨-370157872936,-99428592883⟩,⟨-7264916975823,12021680444214⟩,⟨-7550802685152,7111440398546⟩,⟨-6176507022044,7491116743982⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43068594777,59429004392⟩,⟨-299305848310,148154751234⟩,⟨-60352175996,212405256156⟩,⟨-11231260553423,8069171023386⟩,⟨-9118762704918,5551343859926⟩,⟨-6524239653924,7144066944794⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2556492719,6346745806⟩,⟨-109894963672,40151767430⟩,⟨-36720881994,52101515629⟩,⟨-3805114111700,3796147855802⟩,⟨-3027243735462,2216802218181⟩,⟨-2337326687118,2394856546846⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1687025229,3212159357⟩,⟨-32355180472,16015636652⟩,⟨-6524114238,22961163088⟩,⟨-1294767964749,1035235602142⟩,⟨-1101385576878,657345820438⟩,⟨-728592906764,854344359472⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨2989378342,5739448586⟩,⟨-81595263455,16664068257⟩,⟨-22206887592,35709293076⟩,⟨-2496210879081,2464866516910⟩,⟨-2152830098783,1415748645719⟩,⟨-1441783224218,1595956658663⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5739448586,-2989378342⟩,⟨-16664068257,81595263455⟩,⟨-35709293076,22206887592⟩,⟨-2464866516910,2496210879081⟩,⟨-1415748645719,2152830098783⟩,⟨-1595956658663,1441783224218⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3182955867,3357367464⟩,⟨-126559031929,121747030885⟩,⟨-72430175070,74308403221⟩,⟨-6269980628610,6292358734883⟩,⟨-4442992381181,4369632316964⟩,⟨-3933283345781,3836639771064⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47928189941,64065212590⟩,⟨-356579122047,231274029738⟩,⟨-29821074577,291231301956⟩,⟨-14762791451571,10494886229851⟩,⟨-10592982518803,7032772008562⟩,⟨-7774388383141,8770741985460⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3182955867,3357367464⟩,⟨-126559031929,121747030885⟩,⟨-72430175070,74308403221⟩,⟨-6269980628610,6292358734883⟩,⟨-4442992381181,4369632316964⟩,⟨-3933283345781,3836639771064⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (105/1024) u, BivariateJet2.affineZ (539/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000041

end


