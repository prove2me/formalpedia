-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000014_000017_data
-- name    : GeneralCK_RB2_cells000014_000017_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T01:03:04.214771+00:00
-- url     : https://prove2.me/theorems/7056597f-bee7-419e-a977-715d0a5f574f
-- title:
--   Exact certificate data for RB2 cells 000014–000017
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000014 through 000017. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000014Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2516788585792,-2516788527936⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2516788585792,-2516788527936⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-117516647104,-117516647040⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-117516647104,-117516647040⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2125198968640,-2125198929664⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2125198968640,-2125198929600⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-171900768192,-171900768128⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-171900768192,-171900768128⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨85323935104,85323935168⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-92506500416,-92506500352⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨85324058560,85324058624⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-92506645504,-92506645440⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7182586944,-7182586880⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7182565248,-7182565184⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨177830435520,177830435584⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨177830704000,177830704064⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1953298161472,1953298200064⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1953298161472,1953298200064⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2518909148928,-2518909091072⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2132186901504,-2132186862400⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2118249983808,-2118249944832⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-173081081152,-173081081088⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-170722602688,-170722602624⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨82743166720,82743166784⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-89480404736,-89480404672⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨87927401664,87927401728⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-95574908416,-95574908352⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7647506752,-7647506688⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6737238016,-6737237952⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨172223571392,172223571456⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨183502310016,183502310080⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1945168863744,1945168902336⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1961464259712,1961464298368⟩



end LaneCBRB2Cell000014Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000014
open Set LaneCBRB2Cell000014Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111454401331,111454401332⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨119614839193,119614839194⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111454401332,-111454401331⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438301412556,438301412557⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨47682399764,47682399765⟩,⟨-119614839194,-119614839193⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159136801095,159136801097⟩,⟨979896788582,979896788583⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47682399763,47682399766⟩,⟨-119614839194,-119614839193⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2516788585792,-2516788527936⟩,⟨10846819911700,10846819911799⟩,⟨0,0⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-255119780476,-255119774608⟩,⟨-1417276958026,-1417276900150⟩,⟨0,0⟩,⟨10846819911502,10846819911997⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨255119774608,255119780476⟩,⟨1417276900150,1417276958026⟩,⟨0,0⟩,⟨-10846819911997,-10846819911502⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988057226444,988057226445⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117516647104,-117516647040⟩,⟨-1223538259991,-1223538259989⟩,⟨0,0⟩,⟨-1361555290407,-1361555290401⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105604315103,-105604315045⟩,⟨-981994980738,-981994980670⟩,⟨0,0⟩,⟨1223538259985,1223538259996⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105604315045,105604315103⟩,⟨981994980670,981994980738⟩,⟨0,0⟩,⟨-1223538259996,-1223538259985⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨360724089653,360724095579⟩,⟨2399271880820,2399271938764⟩,⟨0,0⟩,⟨-12070358171993,-12070358171487⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2125198968640,-2125198929600⟩,⟨6770325315320,6770325315414⟩,⟨3028322149583,3028322149630⟩,⟨-41688785928759,-41688785927606⟩,⟨-26243891671155,-26243891670519⟩,⟨-8340734932003,-8340734931751⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-307588712135,-307588706479⟩,⟨-914103776648,-914103741826⟩,⟨-408872629442,-408872613863⟩,⟨6033787971276,6033787971701⟩,⟨3724561123712,3724561162983⟩,⟨1207188575605,1207188575702⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307588706479,307588712135⟩,⟨914103741826,914103776648⟩,⟨408872613863,408872629442⟩,⟨-6033787971701,-6033787971276⟩,⟨-3724561162983,-3724561123712⟩,⟨-1207188575702,-1207188575605⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159136801097,-159136801095⟩,⟨-979896788583,-979896788582⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940374826679,940374826681⟩,⟨-979896788583,-979896788582⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-171900768192,-171900768128⟩,⟨-1145721772321,-1145721772315⟩,⟨-512473841181,-512473841177⟩,⟨-1193874031351,-1193874031339⟩,⟨751566639551,751566639562⟩,⟨-238860082295,-238860082291⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147020869095,-147020869039⟩,⟨-826696943867,-826696943801⟩,⟨-369776125890,-369776125858⟩,⟨1021079774808,1021079774835⟩,⟨1384333152015,1384333152101⟩,⟨204288888637,204288888647⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147020869039,147020869095⟩,⟨826696943801,826696943867⟩,⟨369776125858,369776125890⟩,⟨-1021079774835,-1021079774808⟩,⟨-1384333152101,-1384333152015⟩,⟨-204288888647,-204288888637⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨454609575518,454609581230⟩,⟨1740800685627,1740800720515⟩,⟨778648739721,778648755332⟩,⟨-7054867746536,-7054867746084⟩,⟨-5108894315084,-5108894275727⟩,⟨-1411477464349,-1411477464242⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨815333665171,815333676809⟩,⟨4140072566447,4140072659279⟩,⟨778648739721,778648755332⟩,⟨-19125225918529,-19125225917571⟩,⟨-5108894315084,-5108894275727⟩,⟨-1411477464349,-1411477464242⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95364799526,95364799532⟩,⟨-239229678388,-239229678386⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12676855879186,12676855879984⟩,⟨31800833953472,31800833957743⟩,⟨-116526933765826,-116526933750887⟩,⟨159549504983607,159549505016409⟩,⟨-292316463007098,-292316462853654⟩,⟨2142254580913592,2142254581327960⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9400416608351,9400416743125⟩,⟨71314747180620,71314748593706⟩,⟨-77432119269923,-77432117844887⟩,⟨137291745445496,137291752585599⟩,⟨-691914889818995,-691914875804466⟩,⟨1407253947866970,1407253974181709⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨88721899520,88722032896⟩,⟨-666769202823,-666767158443⟩,⟨723962367235,723964585961⟩,⟨8691052313670,8691103075263⟩,⟨-4361208167199,-4361137546814⟩,⟨-1398022315358,-1397926866355⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1188233527296,1188233660672⟩,⟨-666769202823,-666767158443⟩,⟨723962367235,723964585961⟩,⟨8691052313670,8691103075263⟩,⟨-4361208167199,-4361137546814⟩,⟨-1398022315358,-1397926866355⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨85323935104,85324058624⟩,⟨-616983509307,-616981548319⟩,⟨669906153303,669908281560⟩,⟨7695899998725,7695950073602⟩,⟨-3659657482282,-3659589292892⟩,⟨-1701796504532,-1701705443829⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨92208902398,92209046236⟩,⟨-718511754157,-718509326536⟩,⟨780142972449,780145607212⟩,⟨9739639838123,9739704475504⟩,⟨-5105896534615,-5105811356310⟩,⟨-1065421328488,-1065309643109⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-88722032896,-88721899520⟩,⟨666767158443,666769202823⟩,⟨-723964585961,-723962367235⟩,⟨-8691103075263,-8691052313670⟩,⟨4361137546814,4361208167199⟩,⟨1397926866355,1398022315358⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1010789594880,1010789728256⟩,⟨666767158443,666769202823⟩,⟨-723964585961,-723962367235⟩,⟨-8691103075263,-8691052313670⟩,⟨4361137546814,4361208167199⟩,⟨1397926866355,1398022315358⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-92506645504,-92506500352⟩,⟨725292534375,725294853905⟩,⟨-787510560452,-787508043062⟩,⟨-9932406518486,-9932346993666⟩,⟨5263415124285,5263495891276⟩,⟨956585712378,956693346156⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-85042090242,-85041945580⟩,⟨610668907676,610671388048⟩,⟨-663054707201,-663052015170⟩,⟨-7520059777986,-7519992922982⟩,⟨3516642142179,3516729529443⟩,⟨1798828547263,1798942320335⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7166812156,7167100656⟩,⟨-107842846481,-107837938488⟩,⟨117088265248,117093592042⟩,⟨2219580060137,2219711552522⟩,⟨-1589254392436,-1589081826867⟩,⟨733407218775,733632677226⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3583406078,3583550328⟩,⟨-53921423241,-53918969244⟩,⟨58544132624,58546796021⟩,⟨1109790030068,1109855776261⟩,⟨-794627196218,-794540913433⟩,⟨366703609387,366816338613⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3583550328,-3583406078⟩,⟨53918969244,53921423241⟩,⟨-58546796021,-58544132624⟩,⟨-1109855776261,-1109790030068⟩,⟨794540913433,794627196218⟩,⟨-366816338613,-366703609387⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758539833288,758539996802⟩,⟨53918969244,53921423241⟩,⟨-58546796021,-58544132624⟩,⟨-1109855776261,-1109790030068⟩,⟨794540913433,794627196218⟩,⟨-366816338613,-366703609387⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7159156170,7159177696⟩,⟨-107606172874,-107605681176⟩,⟨116836083910,116836617620⟩,⟨2211281960033,2211297219729⟩,⟨-1581888762904,-1581870924640⟩,⟨727752426099,727774012836⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7159177696,-7159156170⟩,⟨107605681176,107606172874⟩,⟨-116836617620,-116836083910⟩,⟨-2211297219729,-2211281960033⟩,⟨1581870924640,1581888762904⟩,⟨-727774012836,-727752426099⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092352450080,1092352471606⟩,⟨107605681176,107606172874⟩,⟨-116836617620,-116836083910⟩,⟨-2211297219729,-2211281960033⟩,⟨1581870924640,1581888762904⟩,⟨-727774012836,-727752426099⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7182586944,-7182565184⟩,⟨108310916799,108311413855⟩,⟨-117602354089,-117601814562⟩,⟨-2236459470666,-2236443969165⟩,⟨1603823073764,1603841166630⟩,⟨-745122373941,-745100515875⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3591293472,-3591282592⟩,⟨54155458399,54155706928⟩,⟨-58801177045,-58800907281⟩,⟨-1118229735333,-1118221984582⟩,⟨801911536882,801920583315⟩,⟨-372561186971,-372550257937⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3591282592,3591293472⟩,⟨-54155706928,-54155458399⟩,⟨58800907281,58801177045⟩,⟨1118221984582,1118229735333⟩,⟨-801920583315,-801911536882⟩,⟨372550257937,372561186971⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765714666208,765714696352⟩,⟨-54155706928,-54155458399⟩,⟨58800907281,58801177045⟩,⟨1118221984582,1118229735333⟩,⟨-801920583315,-801911536882⟩,⟨372550257937,372561186971⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273088112520,273088117902⟩,⟨26901420294,26901543219⟩,⟨-29209154405,-29209020977⟩,⟨-552824304933,-552820490008⟩,⟨395467731160,395472190726⟩,⟨-181943503209,-181938106524⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531429332416,1531429392704⟩,⟨-108311413856,-108310916798⟩,⟨117601814562,117602354090⟩,⟨2236443969164,2236459470666⟩,⟨-1603841166630,-1603823073764⟩,⟨745100515874,745122373942⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1196021077203,1196021235021⟩,⟨-788957592633,-788954965401⟩,⟨856631429969,856634281358⟩,⟨11324591011436,11324660584128⟩,⟨-6290579487872,-6290487187999⟩,⟨-427118270983,-426996886859⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1292530526630,1292530842266⟩,⟨-1577915185266,-1577909930802⟩,⟨1713262859937,1713268562716⟩,⟨22649182022873,22649321168248⟩,⟨-12581158975740,-12580974375998⟩,⟨-854236393112,-853993922571⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨177830435520,177830704064⟩,⟨-1342278621743,-1342273824164⟩,⟨1457413915658,1457419122721⟩,⟨17628234399782,17628369184720⟩,⟨-8923165076484,-8922992714281⟩,⟨-2658500624909,-2658280382029⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨61208170219,61208275428⟩,⟨-455645309200,-455643595087⟩,⟨494728649378,494730509734⟩,⟨5840897232371,5840942161342⟩,⟨-2873627673171,-2873567797087⟩,⟨-1071177528287,-1071098586746⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380364459349,380364481820⟩,⟨10567477114,10567773790⟩,⟨-11474276130,-11473954105⟩,⟨-219818153385,-219808899910⟩,⟨158223183092,158233970495⟩,⟨-74601908406,-74588891988⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178335195310,3178335383079⟩,⟨-88304594532,-88302105066⟩,⟨95876649646,95879351824⟩,⟨1841635213737,1841713029407⟩,⟨-1327534887714,-1327444291646⟩,⟨629051030198,629160195088⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨176933173540,176933488120⟩,⟨-1322040207296,-1322035027496⟩,⟨1435439037538,1435444659320⟩,⟨17059865917588,17060003637048⟩,⟨-8460103878367,-8459922595879⟩,⟨-2975132271250,-2974895000251⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨354763609060,354764192184⟩,⟨-2664318829039,-2664308851660⟩,⟨2892852953196,2892863782041⟩,⟨34688100317370,34688372821768⟩,⟨-17383268954851,-17382915310160⟩,⟨-5633632896159,-5633175382280⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523307497755,523307723369⟩,⟨74396095334,74399497340⟩,⟨-80781476694,-80777784388⟩,⟨-1526064337180,-1525972810681⟩,⟨1090546002974,1090665812794⟩,⟨-499890027377,-499733809930⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361023541795,361023775269⟩,⟨76987455602,76990992705⟩,⟨-83595270198,-83591431261⟩,⟨-1573747991130,-1573652436048⟩,⟨1122589397865,1122714167093⟩,⟨-510850688606,-510688328941⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722047083590,722047550538⟩,⟨153974911204,153981985410⟩,⟨-167190540396,-167182862522⟩,⟨-3147495982260,-3147304872096⟩,⟨2245178795730,2245428334186⟩,⟨-1021701377212,-1021376657882⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524270154720,1524270236534⟩,⟨-705732680,-704743924⟩,⟨765196942,766270180⟩,⟨25146749435,25177510633⟩,⟨-21970241990,-21934310860⟩,⟨17326503038,17369947843⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000985157423,1000985858489⟩,⟨212994372459,213004840615⟩,⟨-231276368446,-231265006929⟩,⟨-4347106958920,-4346821288185⟩,⟨3098312948318,3098682970191⟩,⟨-1405255420809,-1404776306729⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67827492966,67827495641⟩,⟨13363129422,13363190750⟩,⟨-14509483668,-14509417100⟩,⟨-273295995706,-273294083219⟩,⟨195017064350,195019296552⟩,⟨-88827513446,-88824816711⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50296910957,50296913660⟩,⟨265305199871,265305261291⟩,⟨37274477334,37274529709⟩,⟨-1281837244839,-1281835313063⟩,⟨-215718193242,-215716225547⟩,⟨-173492142039,-173490043217⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133015914463,2133016082406⟩,⟨-301718105666,-301716709154⟩,⟨327597933146,327599448984⟩,⟨6251297508023,6251341130957⟩,⟨-4490916000670,-4490865211698⟩,⟨2100748992952,2100810194506⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2970921866943,2970922217817⟩,⟨-630361649194,-630358706728⟩,⟨684430802801,684433996696⟩,⟨13105045012925,13105137076827⟩,⟨-9431010116382,-9430903190514⟩,⟨4441528389044,4441656910911⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135904149466,135904172822⟩,⟨688028898608,688029285385⟩,⟨132026175319,132026476522⟩,⟨-3168290270252,-3168278907378⟩,⟨-870519268327,-870508029532⟩,⟨-219199956167,-219188057823⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8895428260308,8895429789045⟩,⟨-45034064265129,-45034023470361⟩,⟨-8641621737167,-8641599052084⟩,⟨663354295851544,663355858619578⟩,⟨144475927964889,144476977085289⟩,⟨31136690647438,31137559634942⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8098315136057,8098322199672⟩,⟨-39275423950696,-39275273109935⟩,⟨-9738363451737,-9738245049259⟩,⟨551293371390383,551298407624792⟩,⟨164394047302854,164398653043391⟩,⟨20612799914661,20617677173378⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16196630272114,16196644399344⟩,⟨-78550847901392,-78550546219870⟩,⟨-19476726903474,-19476490098518⟩,⟨1102586742780766,1102596815249584⟩,⟨328788094605708,328797306086782⟩,⟨41225599829322,41235354346756⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10846819911700,10846819911799⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738054,2111240126795878⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9747308283924,9747308284023⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738069,2111240126795861⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2399271880896,2399271938752⟩,⟨-12070358171930,-12070358171514⟩,⟨0,0⟩,⟨105643681588589,105643681622780⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7596770899508,7596770899605⟩,⟨-46777686599849,-46777686598605⟩,⟨-20923352695656,-20923352695073⟩,⟨576074227448169,576074227471420⟩,⟨310162010432830,310162010444897⟩,⟨115255993314418,115255993319362⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6497259271732,6497259271829⟩,⟨-46777686599849,-46777686598605⟩,⟨-20923352695657,-20923352695072⟩,⟨576074227448176,576074227471415⟩,⟨310162010432834,310162010444895⟩,⟨115255993314419,115255993319362⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1953298161472,1953298200064⟩,⟨-7916047087884,-7916047087502⟩,⟨-3540795990877,-3540795990701⟩,⟨40494911890199,40494911902894⟩,⟨26995458307178,26995458313364⟩,⟨8101874848197,8101874850839⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100156582133,100156582135⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136104282999,136104283002⟩,⟨696247873188,696247873195⟩,⟨311427111368,311427111373⟩,⟨-1746589471214,-1746589471210⟩,⟨-1562476051172,-1562476051164⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4352570042368,4352570138816⟩,⟨-19986405259814,-19986405259016⟩,⟨-3540795990877,-3540795990701⟩,⟨146138593478788,146138593525674⟩,⟨26995458307178,26995458313364⟩,⟨8101874848197,8101874850839⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨709527218120,709528384368⟩,⟨-5328637658078,-5328617703320⟩,⟨5785705906392,5785727564082⟩,⟨69376200634740,69376745643536⟩,⟨-34766537909702,-34765830620320⟩,⟨-11267265792318,-11266350764560⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5062097260488,5062098523184⟩,⟨-25315042917892,-25315022962336⟩,⟨2244909915515,2244931573381⟩,⟨215514794113528,215515339169210⟩,⟨-7771079602524,-7770372306956⟩,⟨-3165390944121,-3164475913721⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461115960238,461116075270⟩,⟨1729841264275,1729844088826⟩,⟨204493066425,204495039286⟩,⟨-30858176138538,-30858092142755⟩,⟨1081907250021,1081988945997⟩,⟨-288341414566,-288258062719⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨222908802662,222908802664⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-222908802664,-222908802662⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨876602825112,876602825114⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1912856995663,1912857041795⟩,⟨-14421825529427,-14421825413360⟩,⟨0,0⟩,⟨132507508514929,132507508544046⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨813345367887,813345414019⟩,⟨-14421825529427,-14421825413360⟩,⟨0,0⟩,⟨132507508514929,132507508544046⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35272259062,35272261066⟩,⟨-713912805766,-713912795671⟩,⟨324226151534,324226169925⟩,⟨8884312272116,8884312299022⟩,⟨-6562358286202,-6562358193788⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨496388219300,496388336336⟩,⟨1015928458509,1015931293155⟩,⟨528719217959,528721209211⟩,⟨-21973863866422,-21973779843733⟩,⟨-5480451036181,-5480369247791⟩,⟨-288341414566,-288258062719⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503871945521,503871957673⟩,⟨2534900173993,2534900296365⟩,⟨0,0⟩,⟨3319096918590,3319099843609⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227479265770,227479324891⟩,⟨1609980638359,1609982273689⟩,⟨242295555824,242296474197⟩,⟨-3887088262159,-3887034543912⟩,⟨-1292569463599,-1292527272320⟩,⟨-132137895922,-132099695178⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-709528384368,-709527218120⟩,⟨5328617703320,5328637658078⟩,⟨-5785727564082,-5785705906392⟩,⟨-69376745643536,-69376200634740⟩,⟨34765830620320,34766537909702⟩,⟨11266350764560,11267265792318⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3643041658000,3643042920696⟩,⟨-14657787556494,-14657767600938⟩,⟨-9326523554959,-9326501897093⟩,⟨76761847835252,76762392890934⟩,⟨61761288927498,61761996223066⟩,⟨19368225612757,19369140643157⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450958007420,450958163735⟩,⟨492466224881,492469494749⟩,⟨-122634320365,-122631281730⟩,⟨-14848584188331,-14848489438715⟩,⟨-7589365848335,-7589257133533⟩,⟨-4043614072226,-4043488133903⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨318273602190,318273602194⟩,⟨1959793577164,1959793577166⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-318273602194,-318273602190⟩,⟨-1959793577166,-1959793577164⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨781238025582,781238025586⟩,⟨-1959793577166,-1959793577164⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1387880546682,1387880574111⟩,⟨-9106204983401,-9106204914308⟩,⟨-4073145818787,-4073145787875⟩,⟨56992395446690,56992395457250⟩,⟨35710113580473,35710113662792⟩,⟨11402549941617,11402549943819⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1387880574111,-1387880546682⟩,⟨9106204914308,9106204983401⟩,⟨4073145787875,4073145818787⟩,⟨-56992395457250,-56992395446690⟩,⟨-35710113662792,-35710113580473⟩,⟨-11402549943819,-11402549941617⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-288368946335,-288368918906⟩,⟨9106204914308,9106204983401⟩,⟨4073145787875,4073145818787⟩,⟨-56992395457250,-56992395446690⟩,⟨-35710113662792,-35710113580473⟩,⟨-11402549943819,-11402549941617⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12505664363,-12505663171⟩,⟨426279170742,426279176750⟩,⟨61686341026,61686353314⟩,⟨-4452893948228,-4452893932562⟩,⟨1926650710542,1926650772559⟩,⟨2752885993660,2752886018440⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438452343057,438452500564⟩,⟨918745395623,918748671499⟩,⟨-60947979339,-60944928416⟩,⟨-19301478136559,-19301383371277⟩,⟨-5662715137793,-5662606360974⟩,⟨-1290728078566,-1290602115463⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100156582135,-100156582133⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4343479475,4343479476⟩,⟨27119597574,27119597578⟩,⟨39925700025,39925700027⟩,⟨-286094398591,-286094398582⟩,⟨249286067484,249286067488⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9478015426,9478015658⟩,⟨11495953815,11495955265⟩,⟨87122870713,87122872820⟩,⟨-802395890988,-802395875573⟩,⟨105671963339,105671976504⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1482737502449,1482737523614⟩,⟨-7528992539656,-7528992155891⟩,⟨-1416023618998,-1416023550182⟩,⟨111241372760332,111241380458254⟩,⟨23671326470045,23671328033443⟩,⟨5271486506533,5271486804280⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12781500955,12781501451⟩,⟨-49398683890,-49398676814⟩,⟨105282427916,105282433328⟩,⟨-280579999693,-280579845744⟩,⟨-264831235871,-264831150183⟩,⟨-178963874451,-178963854437⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12781501451,-12781500955⟩,⟨49398676814,49398683890⟩,⟨-105282433328,-105282427916⟩,⟨280579845744,280579999693⟩,⟨264831150183,264831235871⟩,⟨178963854437,178963874451⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112938083586,-112938083088⟩,⟨-827204148300,-827204141222⟩,⟨-105282433328,-105282427916⟩,⟨2479603101296,2479603255245⟩,⟨264831150183,264831235871⟩,⟨178963854437,178963874451⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨84708466412,84708468092⟩,⟨-555791822908,-555791818668⟩,⟨625095429667,625095445072⟩,⟨3478497070270,3478497071031⟩,⟨-3552985368644,-3552985329525⟩,⟨-2471601813718,-2471601813432⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨114232916461,114232920358⟩,⟨-1329556485376,-1329556427887⟩,⟨733874225833,733874266108⟩,⟨20872802117501,20872803394569⟩,⟨-6532270710536,-6532270068858⟩,⟨-4537011631013,-4537011434128⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-114232920358,-114232916461⟩,⟨1329556427887,1329556485376⟩,⟨-733874266108,-733874225833⟩,⟨-20872803394569,-20872802117501⟩,⟨6532270068858,6532270710536⟩,⟨4537011434128,4537011631013⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨985278707418,985278711315⟩,⟨1329556427887,1329556485376⟩,⟨-733874266108,-733874225833⟩,⟨-20872803394569,-20872802117501⟩,⟨6532270068858,6532270710536⟩,⟨4537011434128,4537011631013⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121963832523,121963833009⟩,⟨788492369666,788492379262⟩,⟨188228178504,188228184601⟩,⟨-2465052323947,-2465052086785⟩,⟨-679668060289,-679667933494⟩,⟨-167245526344,-167245477895⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11600614572,11600614675⟩,⟨169935174256,169935176462⟩,⟨21628503584,21628504794⟩,⟨735281085423,735281140599⟩,⟨104010774732,104010802078⟩,⟨-16602730075,-16602723725⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170885746367,170885896937⟩,⟨1674506228257,1674511634500⟩,⟨113111011115,113113807120⟩,⟨-1816574401215,-1816364198144⟩,⟨445697524245,445839141151⟩,⟨-575865836592,-575753249648⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170885896937,-170885746367⟩,⟨-1674511634500,-1674506228257⟩,⟨-113113807120,-113111011115⟩,⟨1816364198144,1816574401215⟩,⟨-445839141151,-445697524245⟩,⟨575753249648,575865836592⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56593368833,56593578524⟩,⟨-64530996141,-64523954568⟩,⟨129181748704,129185463082⟩,⟨-2070724064015,-2070460142697⟩,⟨-1738408604750,-1738224796565⟩,⟨443615353726,443766141414⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28773545757359,28773571423077⟩,⟨-256156117348120,-256155476933425⟩,⟨-86759309086621,-86758842218596⟩,⟨3686347025518846,3686369822624798⟩,⟨1374942175768105,1374961575019435⟩,⟨318026210049447,318045169862673⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13528894163,13528894272⟩,⟨174927756814,174927759642⟩,⟨41758594378,41758595898⟩,⟨584028361162,584028443485⟩,⟨119183024614,119183065380⟩,⟨27342942733,27342957807⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354042872682,354043191338⟩,⟨1425890137570,1425902200239⟩,⟨25270588915,25277356617⟩,⟨-20864596010849,-20864094259796⟩,⟨-3494793390301,-3494451531341⟩,⟨-1961414005918,-1961143948984⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354043191338,-354042872682⟩,⟨-1425902200239,-1425890137570⟩,⟨-25277356617,-25270588915⟩,⟨20864094259796,20864596010849⟩,⟨3494451531341,3494793390301⟩,⟨1961143948984,1961414005918⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84409151719,84409627882⟩,⟨-507156804616,-507141466071⟩,⟨-86225335956,-86215517331⟩,⟨1562616123237,1563212639572⟩,⟨-2168263606452,-2167812970673⟩,⟨670415870418,670811890455⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236260865132,236260865137⟩,⟨1572850698300,1572850698309⟩,⟨311427111368,311427111373⟩,⟨-3945612726766,-3945612726762⟩,⟨-1562476051172,-1562476051164⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1663664060276,-1663662601838⟩,⟨-4116903546756,-4116861790767⟩,⟨449668116649,449693881729⟩,⟨41464516132342,41466040312832⟩,⟨-7697362823374,-7696204281078⟩,⟨2130613044013,2131663149396⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-184542701055,-184542538541⟩,⟨-1649732230245,-1649726536212⟩,⟨-234927228105,-234924111002⟩,⟨2424614762304,2424847440427⟩,⟨-207746009712,-207590749107⟩,⟨643356725437,643482331520⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51718164077,51718326596⟩,⟨-76881531945,-76875837903⟩,⟨76499883263,76503000371⟩,⟨-1520997964462,-1520765286335⟩,⟨-1770222060884,-1770066800271⟩,⟨293914075816,294039681901⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4344654604,4344695212⟩,⟨-31058203438,-31056748693⟩,⟨5479088489,5479951411⟩,⟨-19017344359,-18956888598⟩,⟨-299589865467,-299546749546⟩,⟨48301597791,48336767280⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2432687775,2432703065⟩,⟨-7232636888,-7232078492⟩,⟨7196710638,7197026496⟩,⟨-132337982042,-132314050728⟩,⟨-177232487768,-177216130082⟩,⟨38295053920,38307824739⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4321704689,4321731939⟩,⟨-30363379328,-30362276991⟩,⟨4950940271,4951550892⟩,⟨-41368473151,-41317350559⟩,⟨-283654175341,-283620661757⟩,⟨39603569516,39628405419⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4321731939,-4321704689⟩,⟨30362276991,30363379328⟩,⟨-4951550892,-4950940271⟩,⟨41317350559,41368473151⟩,⟨283620661757,283654175341⟩,⟨-39628405419,-39603569516⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨22922665,22990523⟩,⟨-695926447,-693369365⟩,⟨527537597,529011140⟩,⟨22300006200,22411584553⟩,⟨-15969203710,-15892574205⟩,⟨8673192372,8733197764⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56593368833,56593578524⟩,⟨-64530996141,-64523954568⟩,⟨129181748704,129185463082⟩,⟨-2070724064015,-2070460142697⟩,⟨-1738408604750,-1738224796565⟩,⟨443615353726,443766141414⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨22922665,22990523⟩,⟨-695926447,-693369365⟩,⟨527537597,529011140⟩,⟨22300006200,22411584553⟩,⟨-15969203710,-15892574205⟩,⟨8673192372,8733197764⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111239652966,111669149696⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨117682103910,121547574477⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111669149696,-111239652966⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438086664192,438516160922⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46888963276,48476591228⟩,⟨-121547574477,-117682103910⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158128616242,160145740924⟩,⟨977964053299,981829523866⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46459466546,48906087958⟩,⟨-121547574477,-117682103910⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2518909148928,-2514672046784⟩,⟨10825960642717,10867759718598⟩,⟨0,0⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-255826710438,-254414085982⟩,⟨-1423626412033,-1410915200363⟩,⟨0,0⟩,⟨10742201104562,10951197104683⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨254414085982,255826710438⟩,⟨1410915200363,1423626412033⟩,⟨0,0⟩,⟨-10951197104683,-10742201104562⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨987842478080,988271974810⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117755645376,-117277700672⟩,⟨-1223804246569,-1223272389007⟩,⟨0,0⟩,⟨-1362147335313,-1360963631402⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105842085942,-105366684197⟩,⟨-982711975640,-981278141622⟩,⟨0,0⟩,⟨1222208442640,1224867730551⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105366684197,105842085942⟩,⟨981278141622,982711975640⟩,⟨0,0⟩,⟨-1224867730551,-1222208442640⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨359780770179,361668796380⟩,⟨2392193341985,2406338387673⟩,⟨0,0⟩,⟨-12176064835234,-11964409547202⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2132186901504,-2118249944832⟩,⟨6714401781434,6826929898207⟩,⟨3007768913950,3049123108519⟩,⟨-42388793949640,-41002923610472⟩,⟨-26577383710414,-25916491279387⟩,⟨-8455710240833,-8227901925896⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310556653067,-304640646055⟩,⟨-938330220113,-889730067831⟩,⟨-417807385091,-399880239341⟩,⟨5770291272126,6295546964291⟩,⟨3597747668845,3850494582940⟩,⟨1165227257649,1248838792286⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨304640646055,310556653067⟩,⟨889730067831,938330220113⟩,⟨399880239341,417807385091⟩,⟨-6295546964291,-5770291272126⟩,⟨-3850494582940,-3597747668845⟩,⟨-1248838792286,-1165227257649⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160145740924,-158128616242⟩,⟨-981829523866,-977964053299⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939365886852,941383011534⟩,⟨-981829523866,-977964053299⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173081081152,-170722602624⟩,⟨-1149214585174,-1142237362448⟩,⟨-513275630562,-511674180807⟩,⟨-1201164343708,-1186623369151⟩,⟨747723827529,755402224998⟩,⟨-239608082601,-238115232882⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148189055303,-145856564831⟩,⟨-832088079404,-821312548826⟩,⟨-371435511043,-368118361982⟩,⟨1003516858318,1038635768457⟩,⟨1375955895812,1392718032288⟩,⟨202592029071,205984170961⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145856564831,148189055303⟩,⟨821312548826,832088079404⟩,⟨368118361982,371435511043⟩,⟨-1038635768457,-1003516858318⟩,⟨-1392718032288,-1375955895812⟩,⟨-205984170961,-202592029071⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨450497210886,458745708370⟩,⟨1711042616657,1770418299517⟩,⟨767998601323,789242896134⟩,⟨-7334182732748,-6773808130444⟩,⟨-5243212615228,-4973703564657⟩,⟨-1454822963247,-1367819286720⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨810277981065,820414504750⟩,⟨4103235958642,4176756687190⟩,⟨767998601323,789242896134⟩,⟨-19510247567982,-18738217677646⟩,⟨-5243212615228,-4973703564657⟩,⟨-1454822963247,-1367819286720⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92918933092,97812175916⟩,⟨-243095148954,-235364207820⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12359665944379,13010543485446⟩,⟨29740908600343,34038272947406⟩,⟨-122802391092848,-110714331286327⟩,⟨143130348078099,178102325477508⟩,⟨-364681649928400,-224912951692962⟩,⟨1983494247715209,2318185596933742⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9108375859840,9707981544253⟩,⟨68042053604133,74821734733182⟩,⟨-82997445781487,-72251082937250⟩,⟨96592317548155,180861014605076⟩,⟨-779875238498900,-610396352503192⟩,⟨1268210187362610,1559701919015626⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨85936154112,91538778880⟩,⟨-744899217546,-596665058590⟩,⟨633574302221,826293758643⟩,⟨6434590049239,11232052030103⟩,⟨-8046343028769,-980434276173⟩,⟨-6242315099566,3742024256487⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1185447781888,1191050406656⟩,⟨-744899217546,-596665058590⟩,⟨633574302221,826293758643⟩,⟨6434590049239,11232052030103⟩,⟨-8046343028769,-980434276173⟩,⟨-6242315099566,3742024256487⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨82743166720,87927401728⟩,⟨-690899560257,-550808064999⟩,⟨584880630121,766393602037⟩,⟨5505916186215,10141880567824⟩,⟨-7170042902782,-423504149601⟩,⟨-6323993684740,3159630493338⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨89210246601,95247712657⟩,⟨-807988958470,-638760098188⟩,⟨678273308734,896277265044⟩,⟨7018288979613,12820598575966⟩,⟨-9448875553073,-1165173637139⟩,⟨-6675632105862,4873834908817⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-91538778880,-85936154112⟩,⟨596665058590,744899217546⟩,⟨-826293758643,-633574302221⟩,⟨-11232052030103,-6434590049239⟩,⟨980434276173,8046343028769⟩,⟨-3742024256487,6242315099566⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1007972848896,1013575473664⟩,⟨596665058590,744899217546⟩,⟨-826293758643,-633574302221⟩,⟨-11232052030103,-6434590049239⟩,⟨980434276173,8046343028769⟩,⟨-3742024256487,6242315099566⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-95574908416,-89480404672⟩,⟨647253398343,812547036471⟩,⟨-901333400580,-687291997934⟩,⟨-12852565896758,-7361168713938⟩,⟨1468151159732,9443161367370⟩,⟨-4820730389821,6379590963434⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-88104919149,-82030799983⟩,⟨528616671899,700481829399⟩,⟨-779325040158,-558246686408⟩,⟨-10621887551144,-4671005219567⟩,⟨-574779806497,7879371750826⟩,⟨-4194481958793,7560968592645⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1105327452,13216912674⟩,⟨-279372286571,61721731211⟩,⟨-101051731424,338030578636⟩,⟨-3603598571531,8149593356399⟩,⟨-10023655359570,6714198113687⟩,⟨-10870114064655,12434803501462⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨552663726,6608456337⟩,⟨-139686143286,30860865606⟩,⟨-50525865712,169015289318⟩,⟨-1801799285766,4074796678200⟩,⟨-5011827679785,3357099056844⟩,⟨-5435057032328,6217401750731⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6608456337,-552663726⟩,⟨-30860865606,139686143286⟩,⟨-169015289318,50525865712⟩,⟨-4074796678200,1801799285766⟩,⟨-3357099056844,5011827679785⟩,⟨-6217401750731,5435057032328⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755514927279,761570739154⟩,⟨-30860865606,139686143286⟩,⟨-169015289318,50525865712⟩,⟨-4074796678200,1801799285766⟩,⟨-3357099056844,5011827679785⟩,⟨-6217401750731,5435057032328⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6716638912,7620972646⟩,⟨-124031730162,-93268864344⟩,⟨99038404872,137584578012⟩,⟨1653412462947,2879538754230⟩,⟨-2459379156028,-840894061564⟩,⟨-309223660524,1865012939655⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7620972646,-6716638912⟩,⟨93268864344,124031730162⟩,⟨-137584578012,-99038404872⟩,⟨-2879538754230,-1653412462947⟩,⟨840894061564,2459379156028⟩,⟨-1865012939655,309223660524⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091890655130,1092794988864⟩,⟨93268864344,124031730162⟩,⟨-137584578012,-99038404872⟩,⟨-2879538754230,-1653412462947⟩,⟨840894061564,2459379156028⟩,⟨-1865012939655,309223660524⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7647506752,-6737237952⟩,⟨93842122173,124897423461⟩,⟨-138544864925,-99647123991⟩,⟨-2913824357307,-1671584144598⟩,⟨854567217111,2492282469568⟩,⟨-1895487464937,302351049065⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3823753376,-3368618976⟩,⟨46921061086,62448711731⟩,⟨-69272432463,-49823561995⟩,⟨-1456912178654,-835792072299⟩,⟨427283608555,1246141234784⟩,⟨-947743732469,151175524533⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3368618976,3823753376⟩,⟨-62448711731,-46921061086⟩,⟨49823561995,69272432463⟩,⟨835792072299,1456912178654⟩,⟨-1246141234784,-427283608555⟩,⟨-151175524533,947743732469⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765492002592,765947156256⟩,⟨-62448711731,-46921061086⟩,⟨49823561995,69272432463⟩,⟨835792072299,1456912178654⟩,⟨-1246141234784,-427283608555⟩,⟨-151175524533,947743732469⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272972663782,273198747216⟩,⟨23317216086,31007932541⟩,⟨-34396144503,-24759601218⟩,⟨-719884688558,-413353115736⟩,⟨210223515391,614844789007⟩,⟨-466253234914,77305915131⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530984005184,1531894312512⟩,⟨-124897423462,-93842122172⟩,⟨99647123990,138544864926⟩,⟨1671584144598,2913824357308⟩,⟨-2492282469568,-854567217110⟩,⟨-302351049066,1895487464938⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1192733892074,1199363475851⟩,⟨-886338273590,-702130878348⟩,⟨745564156829,983187747098⟩,⟨8398612415002,14674778544820⟩,⟨-11027322335210,-2031522472946⟩,⟨-6495498659057,6064499677431⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1285956156372,1299215323926⟩,⟨-1772676547179,-1404261756695⟩,⟨1491128313658,1966375494195⟩,⟨16797224830010,29349557089623⟩,⟨-22054644670408,-4063044945891⟩,⟨-12986247814871,12128999354857⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨172223571392,183502310080⟩,⟨-1515664796388,-1188411267549⟩,⟨1261925478540,1681280275172⟩,⟨12125979077339,23809808778230⟩,⟨-17493092119614,-1120883677824⟩,⟨-13674306638283,8922144514295⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59049895957,63403836515⟩,⟨-518519676603,-398361098056⟩,⟨421281028749,576534352674⟩,⟨3892930838757,7971642064581⟩,⟨-5910170306945,-36957317175⟩,⟨-5095362617646,3120324506931⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380093099104,380634089239⟩,⟨1433786794,19903874489⟩,⟨-23183308498,-51177182⟩,⟨-595024271337,144464030436⟩,⟨-322318211851,652285712364⟩,⟨-733401452607,574195697840⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176083944639,3180604495227⟩,⟨-166554859379,-11963792380⟩,⟨427032235,193997037560⟩,⟨-1208779342198,4996583865097⟩,⟨-5478619472968,2697143234429⟩,⟨-4804847492231,6160740483918⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨170573390716,183411000248⟩,⟨-1509548593589,-1151360946459⟩,⟨1216948592445,1678952603672⟩,⟨11184207056165,23505133062926⟩,⟨-17591351587211,44037237956⟩,⟨-15016320694683,9585005180913⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨342796962108,366913310328⟩,⟨-3025213389977,-2339772214008⟩,⟨2478874070985,3360232878844⟩,⟨23310186133504,47314941841156⟩,⟨-35084443706825,-1076846439868⟩,⟨-28690627332966,18507149695208⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519142127215,527497823656⟩,⟨-42751220882,193505692354⟩,⟨-234135038800,69992931270⟩,⟨-5652612805378,2531505438119⟩,⟨-4693497438084,6955668275486⟩,⟨-8628432425637,7581086846545⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356721672224,365368493898⟩,⟨-44417100372,201045995469⟩,⟨-243258538687,72720333815⟩,⟨-5881024115541,2667025726011⟩,⟨-4921006257591,7240046860490⟩,⟨-8980793885256,7930484091012⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713443344448,730736987796⟩,⟨-88834200744,402091990938⟩,⟨-486517077374,145440667630⟩,⟨-11762048231082,5334051452022⟩,⟨-9842012515182,14480093720980⟩,⟨-17961587770512,15860968182024⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523363032538,1525177673600⟩,⟨-31628559118,30189607990⟩,⟨-37937454022,39506460054⟩,⟨-1207954609632,1260411894361⟩,⟨-1651388408004,1604811938918⟩,⟨-2167363988721,2204711125462⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988469052338,1013635245782⟩,⟨-144245948510,577822348094⟩,⟨-700081077515,228002764491⟩,⟨-17141561012344,8258833781557⟩,⟨-14777006480163,21180934856985⟩,⟨-26390650252811,23500227105790⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67770156576,67882461263⟩,⟨11577799498,15409256456⟩,⟨-17093013572,-12293993310⟩,⟨-356754576366,-203495090689⟩,⟨102443154276,304494280714⟩,⟨-230587396459,40568873234⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49942778466,50651356868⟩,⟨261441691134,269365501961⟩,⟨34582653094,39666882228⟩,⟨-1384321301347,-1187852928809⟩,⟨-305059411356,-114178559723⟩,⟨-286413785204,-71211229186⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131775567367,2134311384641⟩,⟨-348026610754,-261335641076⟩,⟨277501663714,386055199866⟩,⟨4671119190956,8147745260443⟩,⟨-6976219514344,-2396845663194⟩,⟨-824439308648,5316689833443⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2968330860568,2973628826350⟩,⟨-727331988332,-545834181782⟩,⟨579599066293,806806972365⟩,⟨9789709645909,17087066568707⟩,⟨-14645204323602,-5041657075171⟩,⟨-1685257928991,11184183062272⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134829579640,136986577560⟩,⟨672303110995,703705651027⟩,⟨119689088192,144446359924⟩,⟨-3655594554206,-2679248630491⟩,⟨-1388118618897,-356762515279⟩,⟨-815781042399,381189777419⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8825140690044,8966324918038⟩,⟨-46797249762368,-43312050323225⟩,⟨-9605852067215,-7710777662832⟩,⟨597740303597105,731591888260733⟩,⟨98669805851427,192581682716780⟩,⟨-11875312863523,74832382072397⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7933866486052,8266018050615⟩,⟨-44318492479990,-34225812141720⟩,⟨-14564634176229,-5072723270614⟩,⟨348400128421183,754079645010334⟩,⟨-46551367855572,381324025120485⟩,⟨-230142816045731,272860381668522⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15867732972104,16532036101230⟩,⟨-88636984959980,-68451624283440⟩,⟨-29129268352458,-10145446541228⟩,⟨696800256842366,1508159290020668⟩,⟨-93102735711144,762648050240970⟩,⟨-460285632091462,545720763337044⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10825960642717,10867759718598⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790014,2123491006166466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9726449014941,9768248090822⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790024,2123491006166451⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2396916401408,2401631448192⟩,⟨-12142992897062,-11998203029636⟩,⟨0,0⟩,⟨102165241571294,109118793444233⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7548910215404,7645205835259⟩,⟨-47469515534135,-46099026984115⟩,⟨-21201389046534,-20650420519897⟩,⟨563027040524548,589481814774212⟩,⟨304040882922493,316440460477738⟩,⟨112980511220929,117589743739646⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6449398587628,6545694207483⟩,⟨-47469515534135,-46099026984115⟩,⟨-21201389046535,-20650420519897⟩,⟨563027040524547,589481814774203⟩,⟨304040882922491,316440460477734⟩,⟨112980511220927,117589743739645⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1945168863744,1961464298368⟩,⟨-8092736646021,-7743474502673⟩,⟨-3614472491510,-3468750106600⟩,⟨35009371975744,45961946089445⟩,⟨24467598426180,29518470970306⟩,⟨7095865012034,9103783573594⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99941875711,100371372442⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135096914011,137114038694⟩,⟨692516781487,699977619214⟩,⟨310407969962,312445650865⟩,⟨-1753486165281,-1739706366688⟩,⟨-1566416851440,-1558535250900⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4342085265152,4363095746560⟩,⟨-20235729543083,-19741677532309⟩,⟨-3614472491510,-3468750106600⟩,⟨137174613547038,155080739533678⟩,⟨24467598426180,29518470970306⟩,⟨7095865012034,9103783573594⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨685593924216,733826620656⟩,⟨-6050426779954,-4679544428016⟩,⟨4957748141970,6720465757688⟩,⟨46620372267008,94629883682312⟩,⟨-70168887413650,-2153692879736⟩,⟨-57381254665932,37014299390416⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5027679189368,5096922367216⟩,⟨-26286156323037,-24421221960325⟩,⟨1343275650460,3251715651088⟩,⟨183794985814046,249710623215990⟩,⟨-45701288987470,27364778090570⟩,⟨-50285389653898,46118082964010⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨456998976604,465283931797⟩,⟨1606841417948,1845785780560⟩,⟨122099198146,296840119237⟩,⟨-35422138001573,-26181289422040⟩,⟨-3101521361205,5091806143330⟩,⟨-4590414003672,4209992113367⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨222479305932,223338299392⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-223338299392,-222479305932⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨876173328384,877032321844⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1910042757372,1915676334849⟩,⟨-14489197074440,-14354900842057⟩,⟨0,0⟩,⟨129405738995668,135611259171579⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨810531129596,816164707073⟩,⟨-14489197074440,-14354900842057⟩,⟨0,0⟩,⟨129405738995668,135611259171579⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34248700012,36302865695⟩,⟨-734701449876,-693313308200⟩,⟨322945996948,325509439814⟩,⟨8540838704679,9235436382529⟩,⟨-6594864009033,-6530061933853⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨491247676616,501586797492⟩,⟨872139968072,1152472472360⟩,⟨445045195094,622349559051⟩,⟨-26881299296894,-16945853039511⟩,⟨-9696385370238,-1438255790523⟩,⟨-4590414003672,4209992113367⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503376910943,504367118897⟩,⟨2514798172912,2555168940688⟩,⟨0,0⟩,⟨2165995870996,4475808627517⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨224902340017,230087505705⟩,⟨1522861459888,1694305161895⟩,⟨203749983062,285483705780⟩,⟨-7373720148221,-359815119659⟩,⟨-3430012938604,787825689767⟩,⟨-2105711142192,1931204308492⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-733826620656,-685593924216⟩,⟨4679544428016,6050426779954⟩,⟨-6720465757688,-4957748141970⟩,⟨-94629883682312,-46620372267008⟩,⟨2153692879736,70168887413650⟩,⟨-37014299390416,57381254665932⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3608258644496,3677501822344⟩,⟨-15556185115067,-13691250752355⟩,⟨-10334938249198,-8426498248570⟩,⟨42544729864726,108460367266670⟩,⟨26621291305916,99687358383956⟩,⟨-29918434378382,66485038239526⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443346478118,458600995595⟩,⟨332700706586,658950052336⟩,⟨-270149832491,9663873370⟩,⟨-20444303752734,-9430289859140⟩,⟨-12968243369830,-1855757341795⟩,⟨-10774589041165,2387499500433⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨316257232484,320291481848⟩,⟨1955928106598,1963659047732⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-320291481848,-316257232484⟩,⟨-1963659047732,-1955928106598⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨779220145928,783254395292⟩,⟨-1963659047732,-1955928106598⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1378534548949,1397279932376⟩,⟨-9268040834497,-8948047056617⟩,⟨-4139400565191,-4008347825100⟩,⟨52360853064594,61647958648315⟩,⟨33571603889895,37861319431889⟩,⟨10557135849581,12251436510948⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1397279932376,-1378534548949⟩,⟨8948047056617,9268040834497⟩,⟨4008347825100,4139400565191⟩,⟨-61647958648315,-52360853064594⟩,⟨-37861319431889,-33571603889895⟩,⟨-12251436510948,-10557135849581⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-297768304600,-279022921173⟩,⟨8948047056617,9268040834497⟩,⟨4008347825100,4139400565191⟩,⟨-61647958648315,-52360853064594⟩,⟨-37861319431889,-33571603889895⟩,⟨-12251436510948,-10557135849581⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13244682938,-11790012715⟩,⟨407960667217,445158216673⟩,⟨50612914407,72946629522⟩,⟨-4791196493225,-4127930249788⟩,⟨1702597651712,2146549182931⟩,⟨2649210385808,2855730771360⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430101795180,446810982880⟩,⟨740661373803,1104108269009⟩,⟨-219536918084,82610502892⟩,⟨-25235500245959,-13558220108928⟩,⟨-11265645718118,290791841136⟩,⟨-8125378655357,5243230271793⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100371372442,-99941875711⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4223007846,4464501371⟩,⟨25926645840,28313342839⟩,⟨39820591103,40030926275⟩,⟨-291718540825,-280474786198⟩,⟨248728938086,249843280775⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9206084332,9751681222⟩,⟨7213742910,15761278550⟩,⟨86808202403,87438394478⟩,⟨-870180198850,-734198632577⟩,⟨100123741306,111191132797⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1473554907446,1491988981394⟩,⟨-7690786496587,-7369864194569⟩,⟨-1453256452963,-1379410165639⟩,⟨107375449425306,115212512787022⟩,⟨22731333947215,24636745822748⟩,⟨5039314827115,5509867723054⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12337905669,13232603063⟩,⟨-58542584153,-40319662148⟩,⟨103450437558,107100417881⟩,⟨-502245786629,-58839679469⟩,⟨-307928344815,-221525384779⟩,⟨-188946127992,-168945698624⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13232603063,-12337905669⟩,⟨40319662148,58542584153⟩,⟨-107100417881,-103450437558⟩,⟨58839679469,502245786629⟩,⟨221525384779,307928344815⟩,⟨168945698624,188946127992⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113603975505,-112279781380⟩,⟨-836712659696,-817630744231⟩,⟨-107100417881,-103450437558⟩,⟨2257862935021,2701269042181⟩,⟨221525384779,307928344815⟩,⟨168945698624,188946127992⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨82192407491,87245594389⟩,⟨-576797281722,-535391572112⟩,⟨614257104840,635716345981⟩,⟨3136895873648,3833632944027⟩,⟨-3783941090538,-3317914339084⟩,⟨-2583273361169,-2359225514765⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨110153473918,118388439209⟩,⟨-1392947913739,-1268450213978⟩,⟨707906427333,759523337424⟩,⟨19408036093608,22413197949776⟩,⟨-7210373462736,-5846630752085⟩,⟨-4809171275293,-4265859060992⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-118388439209,-110153473918⟩,⟨1268450213978,1392947913739⟩,⟨-759523337424,-707906427333⟩,⟨-22413197949776,-19408036093608⟩,⟨5846630752085,7210373462736⟩,⟨4265859060992,4809171275293⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨981123188567,989358153858⟩,⟨1268450213978,1392947913739⟩,⟨-759523337424,-707906427333⟩,⟨-22413197949776,-19408036093608⟩,⟨5846630752085,7210373462736⟩,⟨4265859060992,4809171275293⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120550535066,123377405717⟩,⟨773805352103,803557922365⟩,⟨182269236546,194163184079⟩,⟨-2774999126742,-2163476267213⟩,⟨-816542336811,-541593373790⟩,⟨-222260431603,-111490505814⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11465771701,11737814249⟩,⟨166989414012,172902008666⟩,⟨21128275898,22131704554⟩,⟨657828662607,812316499224⟩,⟨90226192896,117760380322⟩,⟨-19577852556,-13640031457⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165469649501,176487418607⟩,⟨1463685262622,1885902340878⟩,⟨-6053688613,226970555398⟩,⟨-11117138690281,7521835905610⟩,⟨-6056629040080,7056035459331⟩,⟨-6380805405858,5239072368313⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176487418607,-165469649501⟩,⟨-1885902340878,-1463685262622⟩,⟨-226970555398,6053688613⟩,⟨-7521835905610,11117138690281⟩,⟨-7056035459331,6056629040080⟩,⟨-5239072368313,6380805405858⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48414921410,64617856204⟩,⟨-363040880990,230619899273⟩,⟨-23220572336,291537394393⟩,⟨-14895556053831,10757323570622⟩,⟨-10486048397935,6844454729847⟩,⟨-7344783510505,8312009714350⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28071936063079,29492183413726⟩,⟨-279803949437109,-232850064925114⟩,⟨-106311390143195,-68008200432142⟩,⟨2702127262183691,4686332166254895⟩,⟨474419913878457,2310133633580143⟩,⟨-654703858926336,1301932344336575⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13217169457,13844314019⟩,⟨169680150488,180336231652⟩,⟨39968024778,43574527696⟩,⟨466393484782,700123769969⟩,⟨73301699720,165040535286⟩,⟨10550428024,44127049335⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337451216120,371345821155⟩,⟨809047010905,2038077995015⟩,⟨-318167106165,351276006223⟩,⟨-47394257928294,5918231752678⟩,⟨-20951039369672,14555027826885⟩,⟨-16400637923554,12632386969040⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371345821155,-337451216120⟩,⟨-2038077995015,-809047010905⟩,⟨-351276006223,318167106165⟩,⟨-5918231752678,47394257928294⟩,⟨-14555027826885,20951039369672⟩,⟨-12632386969040,16400637923554⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58755974025,109359766760⟩,⟨-1297416621212,295061258104⟩,⟨-570812924307,400777609057⟩,⟨-31153731998637,33836037819366⟩,⟨-25820673545003,21241831210808⟩,⟨-20757765624397,21643868195347⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235038789722,237485411136⟩,⟨1568690109871,1577009941058⟩,⟨310407969962,312445650865⟩,⟨-3952509420833,-3938729622240⟩,⟨-1566416851440,-1558535250900⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1708126568967,-1620379033833⟩,⟨-5590509760442,-2641565925850⟩,⟨-574309028903,1516743186016⟩,⟨-21436262511309,104362945137185⟩,⟨-61616597373867,45050373180277⟩,⟨-52037795494779,56073491131253⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-191670755808,-177658475457⟩,⟨-1875670230016,-1429998660194⟩,⟨-366082578246,-98419523038⟩,⟨-7388458188372,12303611091329⟩,⟨-7522859169621,6994260391808⟩,⟨-5877746542575,7173041182409⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43368033914,59826935679⟩,⟨-306980120145,147011280864⟩,⟨-55674608284,214026127827⟩,⟨-11340967609205,8364881469089⟩,⟨-9089276021061,5435725140908⟩,⟨-6227531699061,6823940871881⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2587208532,6427029515⟩,⟨-112357471823,40278577529⟩,⟨-35856013563,52550468686⟩,⟨-3856695995012,3915248425368⟩,⟨-3036777793313,2195847068690⟩,⟨-2253157391464,2311265349059⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1710565234,3255320037⟩,⟨-33406977132,15998438256⟩,⟨-6058764864,23291299628⟩,⟨-1316265989510,1081720292457⟩,⟨-1108647299254,648773554648⟩,⟨-699383161608,825935158014⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3026196493,5807300143⟩,⟨-83556224781,16493365543⟩,⟨-21509836823,36153805328⟩,⟨-2529182189502,2557575785121⟩,⟨-2163719675773,1399183769075⟩,⟨-1389752183946,1540207933576⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5807300143,-3026196493⟩,⟨-16493365543,83556224781⟩,⟨-36153805328,21509836823⟩,⟨-2557575785121,2529182189502⟩,⟨-1399183769075,2163719675773⟩,⟨-1540207933576,1389752183946⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3220091611,3400833022⟩,⟨-128850837366,123834802310⟩,⟨-72009818891,74060305509⟩,⟨-6414271780133,6444430614870⟩,⟨-4435961562388,4359566744463⟩,⟨-3793365325040,3701017533005⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48414921410,64617856204⟩,⟨-363040880990,230619899273⟩,⟨-23220572336,291537394393⟩,⟨-14895556053831,10757323570622⟩,⟨-10486048397935,6844454729847⟩,⟨-7344783510505,8312009714350⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3220091611,3400833022⟩,⟨-128850837366,123834802310⟩,⟨-72009818891,74060305509⟩,⟨-6414271780133,6444430614870⟩,⟨-4435961562388,4359566744463⟩,⟨-3793365325040,3701017533005⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (519/5120) u, BivariateJet2.affineZ (557/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000014

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000015Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2516788585792,-2516788527936⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2516788585792,-2516788527936⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-117516647104,-117516647040⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-117516647104,-117516647040⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2114603737344,-2114603698432⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2114603737280,-2114603698368⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-173703911744,-173703911680⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-173703911744,-173703911680⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨87668624896,87668624960⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-95269208640,-95269208576⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨87668748032,87668748096⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-95269354112,-95269354048⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7600606016,-7600605952⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7600583744,-7600583680⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨182937833472,182937833536⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨182938102080,182938102144⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1940899786688,1940899825280⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1940899786688,1940899825280⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2518909148928,-2518909091072⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2121529643200,-2121529604224⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2107716051264,-2107716012416⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-174887048192,-174887048128⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-172522930368,-172522930304⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨85088707584,85088707648⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-92230043072,-92230043008⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨90270968064,90270968128⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-98350589440,-98350589376⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8079621376,-8079621312⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7141335488,-7141335424⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨177318750592,177318750656⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨188621557440,188621557504⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1932828964288,1932829002880⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1949006673920,1949006712512⟩



end LaneCBRB2Cell000015Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000015
open Set LaneCBRB2Cell000015Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111454401331,111454401332⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨123480309760,123480309760⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111454401332,-111454401331⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438301412556,438301412557⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49223303167,49223303169⟩,⟨-123480309760,-123480309760⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160677704498,160677704501⟩,⟨976031318016,976031318016⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49223303166,49223303170⟩,⟨-123480309760,-123480309760⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2516788585792,-2516788527936⟩,⟨10846819911700,10846819911799⟩,⟨0,0⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-255119780476,-255119774608⟩,⟨-1417276958026,-1417276900150⟩,⟨0,0⟩,⟨10846819911502,10846819911997⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨255119774608,255119780476⟩,⟨1417276900150,1417276958026⟩,⟨0,0⟩,⟨-10846819911997,-10846819911502⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988057226444,988057226445⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117516647104,-117516647040⟩,⟨-1223538259991,-1223538259989⟩,⟨0,0⟩,⟨-1361555290407,-1361555290401⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105604315103,-105604315045⟩,⟨-981994980738,-981994980670⟩,⟨0,0⟩,⟨1223538259985,1223538259996⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105604315045,105604315103⟩,⟨981994980670,981994980738⟩,⟨0,0⟩,⟨-1223538259996,-1223538259985⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨360724089653,360724095579⟩,⟨2399271880820,2399271938764⟩,⟨0,0⟩,⟨-12070358171993,-12070358171487⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2114603737344,-2114603698368⟩,⟨6678946444778,6678946444904⟩,⟨2999280460674,2999280460738⟩,⟨-40571035800795,-40571035799271⟩,⟨-25742946065427,-25742946064560⟩,⟨-8181526283957,-8181526283611⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309018718732,-309018713029⟩,⟨-901092507439,-901092472801⟩,⟨-404649022594,-404649007035⟩,⟨5928869451244,5928869451803⟩,⟨3677539276277,3677539315566⟩,⟨1195611605461,1195611605592⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309018713029,309018718732⟩,⟨901092472801,901092507439⟩,⟨404649007035,404649022594⟩,⟨-5928869451803,-5928869451244⟩,⟨-3677539315566,-3677539276277⟩,⟨-1195611605592,-1195611605461⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160677704501,-160677704498⟩,⟨-976031318016,-976031318016⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938833923275,938833923278⟩,⟨-976031318016,-976031318016⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173703911744,-173703911680⟩,⟨-1143075209180,-1143075209174⟩,⟨-513314961923,-513314961918⟩,⟨-1188364816555,-1188364816542⟩,⟨754035749259,754035749272⟩,⟨-239644805455,-239644805450⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148319600114,-148319600057⟩,⟨-821835169859,-821835169792⟩,⟨-369057333705,-369057333672⟩,⟨1014702505008,1014702505036⟩,⟨1381475001553,1381475001641⟩,⟨204624186963,204624186975⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148319600057,148319600114⟩,⟨821835169792,821835169859⟩,⟨369057333672,369057333705⟩,⟨-1014702505036,-1014702505008⟩,⟨-1381475001641,-1381475001553⟩,⟨-204624186975,-204624186963⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨457338313086,457338318846⟩,⟨1722927642593,1722927677298⟩,⟨773706340707,773706356299⟩,⟨-6943571956839,-6943571956252⟩,⟨-5059014317207,-5059014277830⟩,⟨-1400235792567,-1400235792424⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨818062402739,818062414425⟩,⟨4122199523413,4122199616062⟩,⟨773706340707,773706356299⟩,⟨-19013930128832,-19013930127739⟩,⟨-5059014317207,-5059014277830⟩,⟨-1400235792567,-1400235792424⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98446606332,98446606340⟩,⟨-246960619520,-246960619520⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12280015173295,12280015174294⟩,⟨30805329585847,30805329590860⟩,⟨-109345526426040,-109345526407998⟩,⟨154554911781601,154554911819324⟩,⟨-274301369641472,-274301369461692⟩,⟨1947301200644068,1947301201128222⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9136618899298,9136619030559⟩,⟨68959120319982,68959121689630⟩,⟨-72714410408574,-72714409058142⟩,⟨133618997876387,133619004805740⟩,⟨-648861006570444,-648860993355044⟩,⟨1279310094667141,1279310118853458⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨91258490880,91258624256⟩,⟨-681952672202,-681950638072⟩,⟨719087445201,719089589175⟩,⟨8819939674583,8819989993177⟩,⟨-4276924260454,-4276856273040⟩,⟨-1375462358767,-1375373144579⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1190770118656,1190770252032⟩,⟨-681952672202,-681950638072⟩,⟨719087445201,719089589175⟩,⟨8819939674583,8819989993177⟩,⟨-4276924260454,-4276856273040⟩,⟨-1375462358767,-1375373144579⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨87668624896,87668748096⟩,⟨-629689039834,-629687091064⟩,⟨663977795915,663979849951⟩,⟨7783372183837,7783421790421⟩,⟨-3568890298837,-3568824726346⟩,⟨-1671017624125,-1670932624099⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨94945043083,94945187144⟩,⟨-736327741559,-736325316055⟩,⟨776423190770,776425747356⟩,⟨9913737839178,9913802254883⟩,⟨-5029766418523,-5029684065781⟩,⟨-1050891066013,-1050786264680⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-91258624256,-91258490880⟩,⟨681950638072,681952672202⟩,⟨-719089589175,-719087445201⟩,⟨-8819989993177,-8819939674583⟩,⟨4276856273040,4276924260454⟩,⟨1375373144579,1375462358767⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1008253003520,1008253136896⟩,⟨681950638072,681952672202⟩,⟨-719089589175,-719087445201⟩,⟨-8819989993177,-8819939674583⟩,⟨4276856273040,4276924260454⟩,⟨1375373144579,1375462358767⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-95269354112,-95269208576⟩,⟨743675004510,743677321131⟩,⟨-784175561046,-784173119282⟩,⟨-10121303140327,-10121243861178⟩,⟨5194350872743,5194428934539⟩,⟨940583444436,940684414901⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-87362082135,-87361937121⟩,⟨622861413215,622863894289⟩,⟨-656783029173,-656780413997⟩,⟨-7594524213836,-7594457474318⟩,⟨3419899092693,3419983692949⟩,⟨1769044285781,1769151154114⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7582960948,7583250023⟩,⟨-113466328344,-113461421766⟩,⟨119640161597,119645333359⟩,⟨2319213625342,2319344780565⟩,⟨-1609867325830,-1609700372832⟩,⟨718153219768,718364889434⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3791480474,3791625012⟩,⟨-56733164172,-56730710883⟩,⟨59820080798,59822666680⟩,⟨1159606812671,1159672390283⟩,⟨-804933662915,-804850186416⟩,⟨359076609884,359182444717⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3791625012,-3791480474⟩,⟨56730710883,56733164172⟩,⟨-59822666680,-59820080798⟩,⟨-1159672390283,-1159606812671⟩,⟨804850186416,804933662915⟩,⟨-359182444717,-359076609884⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758331758604,758331922406⟩,⟨56730710883,56733164172⟩,⟨-59822666680,-59820080798⟩,⟨-1159672390283,-1159606812671⟩,⟨804850186416,804933662915⟩,⟨-359182444717,-359076609884⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7574373883,7574396024⟩,⟨-113203100542,-113202597430⟩,⟨119367241604,119367771960⟩,⟨2310027515925,2310043055065⟩,⟨-1601968126030,-1601950482420⟩,⟨712250678167,712271429965⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7574396024,-7574373883⟩,⟨113202597430,113203100542⟩,⟨-119367771960,-119367241604⟩,⟨-2310043055065,-2310027515925⟩,⟨1601950482420,1601968126030⟩,⟨-712271429965,-712250678167⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091937231752,1091937253893⟩,⟨113202597430,113203100542⟩,⟨-119367771960,-119367241604⟩,⟨-2310043055065,-2310027515925⟩,⟨1601950482420,1601968126030⟩,⟨-712271429965,-712250678167⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7600606016,-7600583680⟩,⟨113987842913,113988351828⟩,⟨-120195785468,-120195248995⟩,⟨-2337884413433,-2337868613815⟩,⟨1625523436074,1625541346032⟩,⟨-730351708231,-730330680648⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3800303008,-3800291840⟩,⟨56993921456,56994175914⟩,⟨-60097892734,-60097624497⟩,⟨-1168942206717,-1168934306907⟩,⟨812761718037,812770673016⟩,⟨-365175854116,-365165340324⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3800291840,3800303008⟩,⟨-56994175914,-56993921456⟩,⟨60097624497,60097892734⟩,⟨1168934306907,1168942206717⟩,⟨-812770673016,-812761718037⟩,⟨365165340324,365175854116⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765923675456,765923705888⟩,⟨-56994175914,-56993921456⟩,⟨60097624497,60097892734⟩,⟨1168934306907,1168942206717⟩,⟨-812770673016,-812761718037⟩,⟨365165340324,365175854116⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272984307938,272984313474⟩,⟨28300649357,28300775136⟩,⟨-29841942990,-29841810401⟩,⟨-577510763767,-577506878981⟩,⟨400487620605,400492031508⟩,⟨-178067857492,-178062669541⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531847350912,1531847411776⟩,⟨-113988351828,-113987842912⟩,⟨120195248994,120195785468⟩,⟨2337868613814,2337884413434⟩,⟨-1625541346032,-1625523436074⟩,⟨730330680648,730351708232⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1199030060383,1199030218997⟩,⟨-810988768734,-810986135150⟩,⟨855149794518,855152570414⟩,⟨11585858151856,11585927746533⟩,⟨-6242985214767,-6242895658842⟩,⟨-415933433847,-415819148460⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1298548492990,1298548810218⟩,⟨-1621977537468,-1621972270300⟩,⟨1710299589037,1710305140829⟩,⟨23171716303724,23171855493059⟩,⟨-12485970429531,-12485791317689⟩,⟨-831866719726,-831638444889⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨182937833472,182938102144⟩,⟨-1373366625942,-1373361830599⟩,⟨1448150635793,1448155690404⟩,⟨17904603174202,17904737801601⟩,⟨-8763330851427,-8763163981070⟩,⟨-2611712440029,-2611505667582⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62940864042,62940969627⟩,⟨-465633385684,-465631670647⟩,⟨490988452518,490990260227⟩,⟨5916473666241,5916518521572⟩,⟨-2808783482395,-2808725498668⟩,⟨-1056715722458,-1056641543198⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380323662243,380323685068⟩,⟨11127888481,11128192212⟩,⟨-11734197204,-11733877026⟩,⟨-230019250544,-230009819517⟩,⟨160563849493,160574526912⟩,⟨-73285011926,-73272491707⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178676130566,3178676321334⟩,⟨-93007416039,-93004866346⟩,⟨98069608299,98072296061⟩,⟨1927822661175,1927902012821⟩,⟨-1347791978560,-1347702263277⟩,⟨618449502616,618554549184⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨181961351852,181961668018⟩,⟨-1351465284138,-1351460090307⟩,⟨1425056198317,1425061672851⟩,⟨17293591069215,17293728949278⟩,⟨-8280382054992,-8280206089515⟩,⟨-2931964817311,-2931741386878⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨364899185324,364899770162⟩,⟨-2724831910080,-2724821920906⟩,⟨2873206834110,2873217363255⟩,⟨35198194243417,35198466750879⟩,⟨-17043712906419,-17043370070585⟩,⟨-5543677257340,-5543247054460⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523020440693,523020666642⟩,⟨78254196978,78257597946⟩,⟨-82519250696,-82515665910⟩,⟨-1593795276727,-1593703967273⟩,⟨1104034760112,1104150681022⟩,⟨-488946301140,-488799643058⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360726526720,360726760476⟩,⟨80957728841,80961264793⟩,⟨-85370150395,-85366423320⟩,⟨-1642801753703,-1642706407514⟩,⟨1135790229446,1135910956487⟩,⟨-499104537609,-498952118878⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721453053440,721453520952⟩,⟨161915457682,161922529586⟩,⟨-170740300790,-170732846640⟩,⟨-3285603507406,-3285412815028⟩,⟨2271580458892,2271821912974⟩,⟨-998209075218,-997904237756⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524272954888,1524273037893⟩,⟨-785754398,-784742370⟩,⟨827477034,828543864⟩,⟨27825558749,27856897509⟩,⟨-23590863612,-23555310044⟩,⟨18059250683,18101030065⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000163481494,1000164184080⟩,⟨223950762889,223961243408⟩,⟨-236157439890,-236146392813⟩,⟨-4536865588219,-4536580096681⟩,⟨3133897652648,3134256220025⟩,⟨-1372243068223,-1371792627036⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67775938423,67775941173⟩,⟨14052844888,14052907630⟩,⟨-14818183118,-14818116978⟩,⟨-285309311252,-285307363473⟩,⟨197328128396,197330336344⟩,⟨-86800715839,-86798123542⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50426885567,50426888335⟩,⟨264555678877,264555741731⟩,⟨36667620084,36667672350⟩,⟨-1278959255525,-1278957282851⟩,⟨-210696696267,-210694742756⟩,⟨-171749476808,-171747450139⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134180528170,2134180697763⟩,⟨-317618763294,-317617332622⟩,⟨334913736448,334915244596⟩,⟨6537904612163,6537949106320⟩,⟨-4554353332674,-4554303025644⟩,⟨2061282459763,2061341366765⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2973355356921,2973355711339⟩,⟨-663763076523,-663760060316⟩,⟨699906267930,699909447484⟩,⟨13712373914050,13712467884278⟩,⟨-9569818032611,-9569712055229⟩,⟨4362607499497,4362731267551⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136366952877,136366976618⟩,⟨684982786379,684983181636⟩,⟨131258237054,131258537801⟩,⟨-3149155566332,-3149143947826⟩,⟨-862407286759,-862396114335⟩,⟨-217689179757,-217677677804⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8865238854720,8865240398127⟩,⟨-44530881168509,-44530839967450⟩,⟨-8533141405324,-8533118882533⟩,⟨652090653999553,652092230546223⟩,⟨141789655514970,141790692016070⟩,⟨30578142836891,30578979364614⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8064205901257,8064212970081⟩,⟨-38701560175067,-38701409424012⟩,⟨-9666232370116,-9666117026903⟩,⟨538448577233096,538453601987321⟩,⟨162072220523068,162076691648940⟩,⟨20416343977571,20420939386343⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16128411802514,16128425940162⟩,⟨-77403120350134,-77402818848024⟩,⟨-19332464740232,-19332234053806⟩,⟨1076897154466192,1076907203974642⟩,⟨324144441046136,324153383297880⟩,⟨40832687955142,40841878772686⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10846819911700,10846819911799⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738054,2111240126795878⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9747308283924,9747308284023⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738069,2111240126795861⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2399271880896,2399271938752⟩,⟨-12070358171930,-12070358171514⟩,⟨0,0⟩,⟨105643681588589,105643681622780⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7523917667165,7523917667306⟩,⟨-45703785104525,-45703785102810⟩,⟨-20523965984242,-20523965983424⟩,⟨555252214372248,555252214403482⟩,⟨300830175854363,300830175870889⟩,⟨111971767454895,111971767461705⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6424406039389,6424406039530⟩,⟨-45703785104526,-45703785102810⟩,⟨-20523965984242,-20523965983423⟩,⟨555252214372248,555252214403480⟩,⟨300830175854361,300830175870889⟩,⟨111971767454894,111971767461705⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1940899786688,1940899825280⟩,⟨-7822021654254,-7822021653752⟩,⟨-3512595422737,-3512595422503⟩,⟨39382670975083,39382670992360⟩,⟨26496981810109,26496981818590⟩,⟨7941881476564,7941881480201⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100156582133,100156582135⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137196984448,137196984452⟩,⟨690765627798,690765627804⟩,⟨310198602052,310198602058⟩,⟨-1732836851712,-1732836851712⟩,⟨-1556312437558,-1556312437550⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4340171667584,4340171764032⟩,⟨-19892379826184,-19892379825266⟩,⟨-3512595422737,-3512595422503⟩,⟨145026352563672,145026352615140⟩,⟨26496981810109,26496981818590⟩,⟨7941881476564,7941881480201⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨729798370648,729799540324⟩,⟨-5449663820160,-5449643841812⟩,⟨5746413668220,5746434726510⟩,⟨70396388486834,70396933501758⟩,⟨-34087425812838,-34086740141170⟩,⟨-11087354514680,-11086494108920⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5069970038232,5069971304356⟩,⟨-25342043646344,-25342023667078⟩,⟨2233818245483,2233839304007⟩,⟨215422741050506,215423286116898⟩,⟨-7590444002729,-7589758322580⟩,⟨-3145473038116,-3144612628719⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461833106370,461833221714⟩,⟨1733658412206,1733661241650⟩,⟨203482705341,203484623606⟩,⟨-30925360492815,-30925276451394⟩,⟨1089518679306,1089597928457⟩,⟨-286527055047,-286448678730⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨222908802662,222908802664⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-222908802664,-222908802662⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨876602825112,876602825114⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1912856995663,1912857041795⟩,⟨-14421825529427,-14421825413360⟩,⟨0,0⟩,⟨132507508514929,132507508544046⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨813345367887,813345414019⟩,⟨-14421825529427,-14421825413360⟩,⟨0,0⟩,⟨132507508514929,132507508544046⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36412116625,36412118695⟩,⟨-736983596621,-736983586191⟩,⟨324226151534,324226169925⟩,⟨9171417516057,9171417543914⟩,⟨-6562358286202,-6562358193788⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨498245222995,498245340409⟩,⟨996674815585,996677655459⟩,⟨527708856875,527710793531⟩,⟨-21753942976758,-21753858907480⟩,⟨-5472839606896,-5472760265331⟩,⟨-286527055047,-286448678730⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503871945521,503871957673⟩,⟨2534900173993,2534900296365⟩,⟨0,0⟩,⟨3319096918590,3319099843609⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228330272745,228330332060⟩,⟨1605438574953,1605440213545⟩,⟨241832538797,241833432139⟩,⟨-3869477335302,-3869423572235⟩,⟨-1291410747988,-1291369804080⟩,⟨-131306431425,-131270510831⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-729799540324,-729798370648⟩,⟨5449643841812,5449663820160⟩,⟨-5746434726510,-5746413668220⟩,⟨-70396933501758,-70396388486834⟩,⟨34086740141170,34087425812838⟩,⟨11086494108920,11087354514680⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3610372127260,3610373393384⟩,⟨-14442735984372,-14442716005106⟩,⟨-9259030149247,-9259009090723⟩,⟨74629419061914,74629964128306⟩,⟨60583721951279,60584407631428⟩,⟨19028375585484,19029235994881⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450501982955,450502140956⟩,⟨466044316252,466047604777⟩,⟨-136768566030,-136765581089⟩,⟨-14524946888743,-14524851775691⟩,⟨-7442305417634,-7442199199388⟩,⟨-3997464876059,-3997345229430⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨321355408996,321355409002⟩,⟨1952062636032,1952062636032⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-321355409002,-321355408996⟩,⟨-1952062636032,-1952062636032⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨778156218774,778156218780⟩,⟨-1952062636032,-1952062636032⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1373630983860,1373631011185⟩,⟨-8981726589719,-8981726520803⟩,⟨-4033378211139,-4033378180181⟩,⟨55646544522674,55646544536901⟩,⟨35106938868403,35106938952567⟩,⟨11221642672750,11221642675756⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1373631011185,-1373630983860⟩,⟨8981726520803,8981726589719⟩,⟨4033378180181,4033378211139⟩,⟨-55646544536901,-55646544522674⟩,⟨-35106938952567,-35106938868403⟩,⟨-11221642675756,-11221642672750⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-274119383409,-274119356084⟩,⟨8981726520803,8981726589719⟩,⟨4033378180181,4033378211139⟩,⟨-55646544536901,-55646544522674⟩,⟨-35106938952567,-35106938868403⟩,⟨-11221642675756,-11221642672750⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12271867958,-12271866733⟩,⟨432881816311,432881822500⟩,⟨71294638462,71294650758⟩,⟨-4508583056177,-4508583039856⟩,⟨1829883831622,1829883893802⟩,⟨2713299534659,2713299559525⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438230114997,438230274223⟩,⟨898926132563,898929427277⟩,⟨-65473927568,-65470930331⟩,⟨-19033529944920,-19033434815547⟩,⟨-5612421586012,-5612315305586⟩,⟨-1284165341400,-1284045669905⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100156582135,-100156582133⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4483843264,4483843265⟩,⟨27995993905,27995993910⟩,⟨39925700025,39925700027⟩,⟨-295339819013,-295339819003⟩,⟨249286067484,249286067488⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9784306768,9784307007⟩,⟨11867456812,11867458311⟩,⟨87122870713,87122872820⟩,⟨-828326099351,-828326083418⟩,⟨105671963339,105671976504⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1477791667600,1477791688711⟩,⟨-7446561914384,-7446561534258⟩,⟨-1397664553479,-1397664485379⟩,⟨109393917564488,109393925137519⟩,⟨23224478428616,23224479964972⟩,⟨5173224513349,5173224805741⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13150535792,13150536302⟩,⟨-50314901387,-50314894142⟩,⟨104659441888,104659447304⟩,⟨-300581908340,-300581751339⟩,⟨-256437510000,-256437424522⟩,⟨-175460342378,-175460322500⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13150536302,-13150535792⟩,⟨50314894142,50314901387⟩,⟨-104659447304,-104659441888⟩,⟨300581751339,300581908340⟩,⟨256437424522,256437510000⟩,⟨175460322500,175460342378⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113307118437,-113307117925⟩,⟨-826287930972,-826287923725⟩,⟨-104659447304,-104659441888⟩,⟨2499605006891,2499605163892⟩,⟨256437424522,256437510000⟩,⟨175460322500,175460342378⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86890848810,86890850546⟩,⟨-568151021916,-568151017529⟩,⟨616453297632,616453313043⟩,⟨3519995940589,3519995941620⟩,⟨-3478307668866,-3478307629562⟩,⟨-2444926787052,-2444926786666⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨116785097236,116785101238⟩,⟨-1352097530348,-1352097471744⟩,⟨718087253403,718087293542⟩,⟨21071804483998,21071805776432⟩,⟨-6292423480199,-6292422844242⟩,⟨-4444497340405,-4444497146122⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-116785101238,-116785097236⟩,⟨1352097471744,1352097530348⟩,⟨-718087293542,-718087253403⟩,⟨-21071805776432,-21071804483998⟩,⟨6292422844242,6292423480199⟩,⟨4444497146122,4444497340405⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨982726526538,982726530540⟩,⟨1352097471744,1352097530348⟩,⟨-718087293542,-718087253403⟩,⟨-21071805776432,-21071804483998⟩,⟨6292422844242,6292423480199⟩,⟨4444497146122,4444497340405⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122624547637,122624548141⟩,⟨786110287536,786110297375⟩,⟨187647841342,187647847490⟩,⟨-2479217108825,-2479216867518⟩,⟨-675517510597,-675517383781⟩,⟨-162921702281,-162921654090⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11676550432,11676550538⟩,⟨170301615458,170301617724⟩,⟨21570776378,21570777592⟩,⟨726738425404,726738481879⟩,⟨104451169350,104451196730⟩,⟨-16238676870,-16238670545⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171279874666,171280026361⟩,⟨1676101545101,1676106977442⟩,⟨111109204918,111111951785⟩,⟨-1880992106817,-1880781389304⟩,⟨461591181923,461729693408⟩,⟨-563115419498,-563008415557⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171280026361,-171279874666⟩,⟨-1676106977442,-1676101545101⟩,⟨-111111951785,-111109204918⟩,⟨1880781389304,1880992106817⟩,⟨-461729693408,-461591181923⟩,⟨563008415557,563115419498⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57050246384,57050457394⟩,⟨-70668402489,-70661331556⟩,⟨130720587012,130724227221⟩,⟨-1988695945998,-1988431465418⟩,⟨-1753140441396,-1752960986003⟩,⟨431701984132,431844908667⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28470486565416,28470512087826⟩,⟨-251373967072761,-251373331549141⟩,⟨-85651674971736,-85651221907927⟩,⟨3579973456852506,3579996030961734⟩,⟨1345677493371455,1345696235131403⟩,⟨312097403340089,312115204875688⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13675871453,13675871566⟩,⟨175344063612,175344066530⟩,⟨41855367560,41855369106⟩,⟨571083558418,571083642655⟩,⟨117646539390,117646580450⟩,⟨27709597334,27709612432⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354119687902,354120008280⟩,⟨1413693752208,1413705828502⟩,⟨18445801725,18452457396⟩,⟨-20859791797100,-20859291178051⟩,⟨-3444344233147,-3444010162763⟩,⟨-1921630658630,-1921373439897⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354120008280,-354119687902⟩,⟨-1413705828502,-1413693752208⟩,⟨-18452457396,-18445801725⟩,⟨20859291178051,20859791797100⟩,⟨3444010162763,3444344233147⟩,⟨1921373439897,1921630658630⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84110106717,84110586321⟩,⟨-514779695939,-514764324931⟩,⟨-83926384964,-83916732056⟩,⟨1825761233131,1826356981553⟩,⟨-2168411423249,-2167971072439⟩,⟨637208098497,637584988725⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237353566581,237353566587⟩,⟨1567368452910,1567368452918⟩,⟨310198602052,310198602058⟩,⟨-3931860107264,-3931860107264⟩,⟨-1556312437558,-1556312437550⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1662070161005,-1662068696578⟩,⟨-4144052015356,-4144010178037⟩,⟨457009790722,457034997645⟩,⟨42025417989081,42026942738686⟩,⟨-7747103200331,-7745974409578⟩,⟨2045292052602,2046285860729⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185364663114,-185364499029⟩,⟨-1650490025334,-1650484295583⟩,⟨-232688097857,-232685027188⟩,⟨2508943628924,2509177263250⟩,⟨-223363780919,-223211606570⟩,⟨630374229689,630493965268⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51988903467,51989067558⟩,⟨-83121572424,-83115842665⟩,⟨77510504195,77513574870⟩,⟨-1422916478340,-1422682844014⟩,⟨-1779676218477,-1779524044120⟩,⟨280931580068,281051315649⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4364212428,4364253456⟩,⟨-32116420588,-32114952504⟩,⟨5645127997,5645980454⟩,⟨8765356533,8826314934⟩,⟨-302435222565,-302392773494⟩,⟨46130440147,46164090923⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2458224192,2458239711⟩,⟨-7860604536,-7860037878⟩,⟨7329956352,7330269874⟩,⟨-121995722331,-121971470868⟩,⟨-180019482982,-180003288946⟩,⟨37495197933,37507470781⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4339350934,4339378416⟩,⟨-31363970468,-31362859498⟩,⟨5085811756,5086415035⟩,⟨-15468020737,-15416588428⟩,⟨-285574658832,-285541651447⟩,⟨37108113275,37131894408⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4339378416,-4339350934⟩,⟨31362859498,31363970468⟩,⟨-5086415035,-5085811756⟩,⟨15416588428,15468020737⟩,⟨285541651447,285574658832⟩,⟨-37131894408,-37108113275⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨24834012,24902522⟩,⟨-753561090,-750982036⟩,⟨558712962,560168698⟩,⟨24181944961,24294335671⟩,⟨-16893571118,-16818114662⟩,⟨8998545739,9055977648⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57050246384,57050457394⟩,⟨-70668402489,-70661331556⟩,⟨130720587012,130724227221⟩,⟨-1988695945998,-1988431465418⟩,⟨-1753140441396,-1752960986003⟩,⟨431701984132,431844908667⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨24834012,24902522⟩,⟨-753561090,-750982036⟩,⟨558712962,560168698⟩,⟨24181944961,24294335671⟩,⟨-16893571118,-16818114662⟩,⟨8998545739,9055977648⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111239652966,111669149696⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121547574476,125413045044⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111669149696,-111239652966⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438086664192,438516160922⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨48429111705,50018249606⟩,⟨-125413045044,-121547574476⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159668764671,161687399302⟩,⟨974098582732,977964053300⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47999614975,50447746336⟩,⟨-125413045044,-121547574476⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2518909148928,-2514672046784⟩,⟨10825960642717,10867759718598⟩,⟨0,0⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-255826710438,-254414085982⟩,⟨-1423626412033,-1410915200363⟩,⟨0,0⟩,⟨10742201104562,10951197104683⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨254414085982,255826710438⟩,⟨1410915200363,1423626412033⟩,⟨0,0⟩,⟨-10951197104683,-10742201104562⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨987842478080,988271974810⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-117755645376,-117277700672⟩,⟨-1223804246569,-1223272389007⟩,⟨0,0⟩,⟨-1362147335313,-1360963631402⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105842085942,-105366684197⟩,⟨-982711975640,-981278141622⟩,⟨0,0⟩,⟨1222208442640,1224867730551⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨105366684197,105842085942⟩,⟨981278141622,982711975640⟩,⟨0,0⟩,⟨-1224867730551,-1222208442640⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨359780770179,361668796380⟩,⟨2392193341985,2406338387673⟩,⟨0,0⟩,⟨-12176064835234,-11964409547202⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2121529643200,-2107716012416⟩,⟨6624095154832,6734459619363⟩,⟨2979090413551,3019711581630⟩,⟨-41248264428603,-39907387527160⟩,⟨-26067059555188,-25424699679948⟩,⟨-8293371171228,-8071747008320⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311979065874,-306078083649⟩,⟨-925064012904,-876976554478⟩,⟨-413508449351,-395732936037⟩,⟨5671353213279,6184705475396⟩,⟨3553030816067,3801192067547⟩,⟨1154390654005,1236529702675⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306078083649,311979065874⟩,⟨876976554478,925064012904⟩,⟨395732936037,413508449351⟩,⟨-6184705475396,-5671353213279⟩,⟨-3801192067547,-3553030816067⟩,⟨-1236529702675,-1154390654005⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161687399302,-159668764671⟩,⟨-977964053300,-974098582732⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937824228474,939842863105⟩,⟨-977964053300,-974098582732⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-174887048192,-172522930304⟩,⟨-1146571836708,-1139587010082⟩,⟨-514119387475,-512512676492⟩,⟨-1195646270147,-1181123073864⟩,⟨750182108442,757882138945⟩,⟨-240396497773,-238896285341⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149490319103,-147152772120⟩,⟨-827224553968,-816452540665⟩,⟨-370720446944,-367395849430⟩,⟨997188698461,1032209407799⟩,⟨1373086304407,1389871351009⟩,⟨202921914799,206324871776⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147152772120,149490319103⟩,⟨816452540665,827224553968⟩,⟨367395849430,370720446944⟩,⟨-1032209407799,-997188698461⟩,⟨-1389871351009,-1373086304407⟩,⟨-206324871776,-202921914799⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨453230855769,461469384977⟩,⟨1693429095143,1752288566872⟩,⟨763128785467,784228896295⟩,⟨-7216914883195,-6668541911740⟩,⟨-5191063418556,-4926117120474⟩,⟨-1442854574451,-1357312568804⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨813011625948,823138181357⟩,⟨4085622437128,4158626954545⟩,⟨763128785467,784228896295⟩,⟨-19392979718429,-18632951458942⟩,⟨-5191063418556,-4926117120474⟩,⟨-1442854574451,-1357312568804⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95999229950,100895492672⟩,⟨-250826090088,-243095148952⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11981960616860,12593078301194⟩,⟨28869044828013,32903103432245⟩,⟨-115048180151157,-104050974292464⟩,⟨139112750564232,171937978876908⟩,⟨-340046554048841,-212930215086445⟩,⟨1807150865773488,2102120456892267⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8859818338494,9427679806806⟩,⟨65869822912841,72262733360059⟩,⟨-77813429675188,-67956348988342⟩,⟨95295950826992,174561946846610⟩,⟨-729131383289838,-574299258366787⟩,⟨1155618945996284,1414504146722300⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨88467718144,94080164096⟩,⟨-759723250505,-611976893127⟩,⟨631362185035,818079651530⟩,⟨6577502913703,11336938719807⟩,⟨-7825490107604,-1013607565289⟩,⟨-5917027308974,3435564451465⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1187979345920,1193591791872⟩,⟨-759723250505,-611976893127⟩,⟨631362185035,818079651530⟩,⟨6577502913703,11336938719807⟩,⟨-7825490107604,-1013607565289⟩,⟨-5917027308974,3435564451465⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨85088707584,90270968128⟩,⟨-703147365897,-563740228866⟩,⟨581597551617,757158019956⟩,⟨5609388264866,10203647240236⟩,⟨-6944537159486,-449504728121⟩,⟨-5997794424357,2872079380785⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨91935023356,97995040599⟩,⟨-825686472803,-656458788638⟩,⟨677253111734,889109687632⟩,⟨7197286878678,12979199556645⟩,⟨-9227567920005,-1211535542101⟩,⟨-6328861287212,4526603553904⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-94080164096,-88467718144⟩,⟨611976893127,759723250505⟩,⟨-818079651530,-631362185035⟩,⟨-11336938719807,-6577502913703⟩,⟨1013607565289,7825490107604⟩,⟨-3435564451465,5917027308974⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1005431463680,1011043909632⟩,⟨611976893127,759723250505⟩,⟨-818079651530,-631362185035⟩,⟨-11336938719807,-6577502913703⟩,⟨1013607565289,7825490107604⟩,⟨-3435564451465,5917027308974⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-98350589440,-92230043008⟩,⟨665525704188,830812022498⟩,⟨-894628944685,-686607235521⟩,⟨-13025535433485,-7555880823084⟩,⟨1517897543526,9233735079496⟩,⟨-4484960895467,6041932354547⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-90437210440,-84338341491⟩,⟨540622980569,712629826216⟩,⟨-769685888760,-554680720457⟩,⟨-10684900360153,-4747154243181⟩,⟨-548280182141,7641438988099⟩,⟨-3864843013538,7194379731088⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1497812916,13656699108⟩,⟨-285063492234,56171037578⟩,⟨-92432777026,334428967175⟩,⟨-3487613481475,8232045313464⟩,⟨-9775848102146,6429903445998⟩,⟨-10193704300750,11720983284992⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨748906458,6828349554⟩,⟨-142531746117,28085518789⟩,⟨-46216388513,167214483588⟩,⟨-1743806740738,4116022656732⟩,⟨-4887924051073,3214951722999⟩,⟨-5096852150375,5860491642496⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6828349554,-748906458⟩,⟨-28085518789,142531746117⟩,⟨-167214483588,46216388513⟩,⟨-4116022656732,1743806740738⟩,⟨-3214951722999,4887924051073⟩,⟨-5860491642496,5096852150375⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755295034062,761374496422⟩,⟨-28085518789,142531746117⟩,⟨-167214483588,46216388513⟩,⟨-4116022656732,1743806740738⟩,⟨-3214951722999,4887924051073⟩,⟨-5860491642496,5096852150375⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7118194074,8050007888⟩,⟨-130012064030,-98480448816⟩,⟨101599965696,139998642880⟩,⟨1739704005706,2989982881381⟩,⟨-2469710171660,-865931027564⟩,⟨-287503446993,1805297476684⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8050007888,-7118194074⟩,⟨98480448816,130012064030⟩,⟨-139998642880,-101599965696⟩,⟨-2989982881381,-1739704005706⟩,⟨865931027564,2469710171660⟩,⟨-1805297476684,287503446993⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091461619888,1092393433702⟩,⟨98480448816,130012064030⟩,⟨-139998642880,-101599965696⟩,⟨-2989982881381,-1739704005706⟩,⟨865931027564,2469710171660⟩,⟨-1805297476684,287503446993⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8079621376,-7141335424⟩,⟨99122161705,130970959993⟩,⟨-141031194240,-102262005810⟩,⟨-3027636235260,-1759976139382⟩,⟨880792590107,2504724635131⟩,⟨-1836702002598,280112853880⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4039810688,-3570667712⟩,⟨49561080852,65485479997⟩,⟨-70515597120,-51131002905⟩,⟨-1513818117630,-879988069691⟩,⟨440396295053,1252362317566⟩,⟨-918351001299,140056426940⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3570667712,4039810688⟩,⟨-65485479997,-49561080852⟩,⟨51131002905,70515597120⟩,⟨879988069691,1513818117630⟩,⟨-1252362317566,-440396295053⟩,⟨-140056426940,918351001299⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765694051328,766163213568⟩,⟨-65485479997,-49561080852⟩,⟨51131002905,70515597120⟩,⟨879988069691,1513818117630⟩,⟨-1252362317566,-440396295053⟩,⟨-140056426940,918351001299⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272865404972,273098358426⟩,⟨24620112204,32503016008⟩,⟨-34999660720,-25399991424⟩,⟨-747495720346,-434926001426⟩,⟨216482756891,617427542915⟩,⟨-451324369171,71875861749⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531388102656,1532326427136⟩,⟨-130970959994,-99122161704⟩,⟨102262005810,141031194240⟩,⟨1759976139382,3027636235260⟩,⟨-2504724635132,-880792590106⟩,⟨-280112853880,1836702002598⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1195720391663,1202395054547⟩,⟨-908552708197,-723760109097⟩,⟨746686303115,978341103058⟩,⟨8655116956476,14930879752774⟩,⟨-10837006762006,-2102678966309⟩,⟨-6143610526705,5700664650358⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1291929155550,1305278481318⟩,⟨-1817105416394,-1447520218195⟩,⟨1493372606230,1956682206117⟩,⟨17310233912958,29861759505539⟩,⟨-21674013524007,-4205357932619⟩,⟨-12282460810933,11401329300713⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨177318750592,188621557504⟩,⟨-1546469112210,-1219330077163⟩,⟨1257954198013,1665257594232⟩,⟨12406294863243,24061998882106⟩,⟨-17050887417395,-1200222530796⟩,⟨-12975238085273,8264007733581⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨60771734014,65147321550⟩,⟨-528485722944,-408193680664⟩,⟨419398163099,570446925970⟩,⟨3969171154821,8038467127639⟩,⟨-5746805647437,-56458713095⟩,⟨-4847624255513,2883899664867⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380044034318,380601551864⟩,⟨1759865643,20698481964⟩,⟨-23398698827,-347296954⟩,⟨-612712707939,141809490885⟩,⟨-316032732115,650225585908⟩,⟨-707538407878,551647350329⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176355465956,3181015120483⟩,⟨-173248829486,-14687167792⟩,⟨2898407987,195849975391⟩,⟨-1186826985414,5147351852325⟩,⟨-5463801105554,2645205876094⟩,⟨-4617350606367,5946299478211⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨175562153809,188478784285⟩,⟨-1539235902645,-1180033717355⟩,⟨1211750522134,1661973690959⟩,⟨11407037447357,23727753369332⟩,⟨-17133935075004,-13049200042⟩,⟨-14296113391445,8899003620959⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨352880904401,377100341789⟩,⟨-3085705014855,-2399363794518⟩,⟨2469704720147,3327231285191⟩,⟨23813332310600,47789752251438⟩,⟨-34184822492399,-1213271730838⟩,⟨-27271351476718,17163011354540⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518839977738,527226005763⟩,⟨-38896537672,197396796328⟩,⟨-231580712784,64006561900⟩,⟨-5707693627419,2452007316131⟩,⟨-4495842625042,6781425355238⟩,⟨-8130440478689,7109654548642⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356410290495,365086120509⟩,⟨-40401798901,205035875843⟩,⟨-240542679300,66483558614⟩,⟨-5936139613470,2585281179929⟩,⟨-4714858075198,7056306388086⟩,⟨-8459682498162,7437620253322⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712820580990,730172241018⟩,⟨-80803597802,410071751686⟩,⟨-481085358600,132967117228⟩,⟨-11872279226940,5170562359858⟩,⟨-9429716150396,14112612776172⟩,⟨-16919364996324,14875240506644⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523338094768,1525208233062⟩,⟨-32490511178,30889902326⟩,⟨-37736637070,39431228544⟩,⟨-1230006741999,1287932229554⟩,⟨-1638793607568,1588917581554⟩,⟨-2085410330564,2124205449591⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨987590052097,1012872156529⟩,⟨-133664781959,589352349402⟩,⟨-692407042699,210633634593⟩,⟨-17309923062456,8050784159298⟩,⟨-14196500813007,20660679228725⟩,⟨-24889416725759,22078151441908⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67716909352,67832582659⟩,⟨12219928770,16146296396⟩,⟨-17386537162,-12607013460⟩,⟨-370225651264,-213949194334⟩,⟨105379623336,305577664730⟩,⟨-223027718265,37933488976⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50071898455,50782172118⟩,⟨260661789415,268647490606⟩,⟨33983451620,39059726006⟩,⟨-1382769131581,-1183631157294⟩,⟨-299612222268,-109952350748⟩,⟨-280783963072,-72695964986⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132901064175,2135515641657⟩,⟨-365053462132,-276112585456⟩,⟨284858868418,393094207512⟩,⟨4920424041753,8470088518891⟩,⟨-7014981278208,-2471955166530⟩,⟨-761732391310,5155592252966⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2970681920323,2976145927527⟩,⟨-763131175529,-576850009149⟩,⟨595122603997,821749348495⟩,⟨10317009192349,17771642724342⟩,⟨-14734803413635,-5202889805070⟩,⟨-1552641675505,10853212373547⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135285230004,137456622488⟩,⟨669015031626,700902237464⟩,⟨118919109730,143679845985⟩,⟨-3645943282796,-2650662800873⟩,⟨-1377554317480,-351059938522⟩,⟨-794945594475,363241014129⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8794962350542,8936125692206⟩,⟨-46297371056265,-42805955134034⟩,⟨-9490623352756,-7608866520247⟩,⟨586280478412375,720555151238023⟩,⟨96528278181767,189333283565668⟩,⟨-10828051725013,72668364119687⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7899704838530,8231975608287⟩,⟨-43735565992020,-33658769816273⟩,⟨-14370220474883,-5122449010195⟩,⟨336285839879488,740464861442766⟩,⟨-42633885717888,372640011465611⟩,⟨-215896286455507,258332554869318⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15799409677060,16463951216574⟩,⟨-87471131984040,-67317539632546⟩,⟨-28740440949766,-10244898020390⟩,⟨672571679758976,1480929722885532⟩,⟨-85267771435776,745280022931222⟩,⟨-431792572911014,516665109738636⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10825960642717,10867759718598⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790014,2123491006166466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9726449014941,9768248090822⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790024,2123491006166451⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2396916401408,2401631448192⟩,⟨-12142992897062,-11998203029636⟩,⟨0,0⟩,⟨102165241571294,109118793444233⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7476932802639,7571460968623⟩,⟨-46374860314948,-45045375692070⟩,⟨-20794348872010,-20258502295392⟩,⟨542758889186101,568087896944428⟩,⟨294942781632306,306867538509656⟩,⟨109779484739397,114219685422085⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6377421174863,6471949340847⟩,⟨-46374860314948,-45045375692070⟩,⟨-20794348872011,-20258502295391⟩,⟨542758889186107,568087896944422⟩,⟨294942781632310,306867538509654⟩,⟨109779484739398,114219685422085⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1932828964288,1949006712512⟩,⟨-7995347453902,-7652704269213⟩,⟨-3585089921140,-3441692396209⟩,⟨34068672568950,44678751247404⟩,⟨24037679498044,28951588723558⟩,⟨6960686646384,8919076719531⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99941875711,100371372442⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136188860814,138207495446⟩,⟨687040289830,694489625399⟩,⟨309178858732,311217743465⟩,⟨-1739706366693,-1725980926276⟩,⟨-1560253237826,-1552371637286⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4329745365696,4350638160704⟩,⟨-20138340350964,-19650907298849⟩,⟨-3585089921140,-3441692396209⟩,⟨136233914140244,153797544691637⟩,⟨24037679498044,28951588723558⟩,⟨6960686646384,8919076719531⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨705761808802,754200683578⟩,⟨-6171410029710,-4798727589036⟩,⟨4939409440294,6654462570382⟩,⟨47626664621200,95579504502876⟩,⟨-68369644984798,-2426543461676⟩,⟨-54542702953436,34326022709080⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5035507174498,5104838844282⟩,⟨-26309750380674,-24449634887885⟩,⟨1354319519154,3212770174173⟩,⟨183860578761444,249377049194513⟩,⟨-44331965486754,26525045261882⟩,⟨-47582016307052,43245099428611⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457710513888,466006605071⟩,⟨1610925507399,1849517769276⟩,⟨123103048332,293284894472⟩,⟨-35469648674453,-26272679544502⟩,⟨-2967719027007,4984084155175⟩,⟨-4343630535274,3947725400431⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨222479305932,223338299392⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-223338299392,-222479305932⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨876173328384,877032321844⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1910042757372,1915676334849⟩,⟨-14489197074440,-14354900842057⟩,⟨0,0⟩,⟨129405738995668,135611259171579⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨810531129596,816164707073⟩,⟨-14489197074440,-14354900842057⟩,⟨0,0⟩,⟨129405738995668,135611259171579⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35384057033,37447234819⟩,⟨-757886518656,-716270557188⟩,⟨322945996948,325509439814⟩,⟨8823037574745,9527458181483⟩,⟨-6594864009033,-6530061933853⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨493094570921,503453839890⟩,⟨853038988743,1133247212088⟩,⟨446049045280,618794334286⟩,⟨-26646611099708,-16745221363019⟩,⟨-9562583036040,-1545977778678⟩,⟨-4343630535274,3947725400431⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503376910943,504367118897⟩,⟨2514798172912,2555168940688⟩,⟨0,0⟩,⟨2165995870996,4475808627517⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225747882644,230943953942⟩,⟨1518340884187,1689825008832⟩,⟨204209564382,283852855841⟩,⟨-7349801202033,-349717634653⟩,⟨-3366339234165,730246524677⟩,⟨-1992506821470,1810897525877⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-754200683578,-705761808802⟩,⟨4798727589036,6171410029710⟩,⟨-6654462570382,-4939409440294⟩,⟨-95579504502876,-47626664621200⟩,⟨2426543461676,68369644984798⟩,⟨-34326022709080,54542702953436⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3575544682118,3644876351902⟩,⟨-15339612761928,-13479497269139⟩,⟨-10239552491522,-8381101836503⟩,⟨40654409637368,106170880070437⟩,⟨26464222959720,97321233708356⟩,⟨-27365336062696,63461779672967⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442877860266,458157257351⟩,⟨306039322607,632618534682⟩,⟨-281670582062,-6423322730⟩,⟨-20109601520043,-9112796687671⟩,⟨-12703840544241,-1842436544956⟩,⟨-10395960130511,2128354812940⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨319337529342,323374798604⟩,⟨1948197165464,1955928106600⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-323374798604,-319337529342⟩,⟨-1955928106600,-1948197165464⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨776136829172,780174098434⟩,⟨-1955928106600,-1948197165464⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1364369148790,1382945406273⟩,⟨-9140312613881,-8826716598968⟩,⟨-4098488879568,-3969687359327⟩,⟨51168085549392,60148389900715⟩,⟨33030169042036,37196102311617⟩,⟨10398692599396,12047996382206⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1382945406273,-1364369148790⟩,⟨8826716598968,9140312613881⟩,⟨3969687359327,4098488879568⟩,⟨-60148389900715,-51168085549392⟩,⟨-37196102311617,-33030169042036⟩,⟨-12047996382206,-10398692599396⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-283433778497,-264857521014⟩,⟨8826716598968,9140312613881⟩,⟨3969687359327,4098488879568⟩,⟨-60148389900715,-51168085549392⟩,⟨-37196102311617,-33030169042036⟩,⟨-12047996382206,-10398692599396⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13004496724,-11562459832⟩,⟨414612975423,451704604901⟩,⟨60256909270,82517526144⟩,⟨-4844859714788,-4185294885029⟩,⟨1607638523726,2048065894723⟩,⟨2610558950362,2815226232165⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429873363542,446594797519⟩,⟨720652298030,1084323139583⟩,⟨-221413672792,76094203414⟩,⟨-24954461234831,-13298091572700⟩,⟨-11096202020515,205629349767⟩,⟨-7785401180149,4943581045105⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100371372442,-99941875711⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4363002111,4605235096⟩,⟨26801083513,29191698123⟩,⟨39820591103,40030926275⟩,⟨-300968491094,-289715676771⟩,⟨248728938086,249843280775⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9511269417,10059081827⟩,⟨7565740440,16152184883⟩,⟨86808202403,87438394478⟩,⟨-896777596065,-759461038797⟩,⟨100123741306,111191132797⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1468679071139,1486972364270⟩,⟨-7605996221161,-7289745879715⟩,⟨-1434329668649,-1361607687728⟩,⟨105610608843608,113279839753560⟩,⟨22305993540048,24167737903077⟩,⟨4946460627206,5406036375780⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12704733610,13603836748⟩,⟨-59478855950,-41215466352⟩,⟨102832337295,106472597152⟩,⟨-522686116354,-78414819648⟩,⟨-299238034518,-213429222072⟩,⟨-185340329219,-165544105798⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13603836748,-12704733610⟩,⟨41215466352,59478855950⟩,⟨-106472597152,-102832337295⟩,⟨78414819648,522686116354⟩,⟨213429222072,299238034518⟩,⟨165544105798,185340329219⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113975209190,-112646609321⟩,⟨-835816855492,-816694472434⟩,⟨-106472597152,-102832337295⟩,⟨2277438075200,2721709371906⟩,⟨213429222072,299238034518⟩,⟨165544105798,185340329219⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨84378412883,89424244143⟩,⟨-589150774296,-547750033479⟩,⟨605620595237,627070249996⟩,⟨3179246459902,3873887226561⟩,⟨-3707933401615,-3244673424311⟩,⟨-2555797853865,-2333373924704⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨112708957255,120936765358⟩,⟨-1415366007494,-1291087935929⟩,⟨692305954365,743553606791⟩,⟨19614586012553,22603202906592⟩,⟨-6962294227745,-5615207610622⟩,⟨-4712889865950,-4177110939309⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-120936765358,-112708957255⟩,⟨1291087935929,1415366007494⟩,⟨-743553606791,-692305954365⟩,⟨-22603202906592,-19614586012553⟩,⟨5615207610622,6962294227745⟩,⟨4177110939309,4712889865950⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨978574862418,986802670521⟩,⟨1291087935929,1415366007494⟩,⟨-743553606791,-692305954365⟩,⟨-22603202906592,-19614586012553⟩,⟨5615207610622,6962294227745⟩,⟨4177110939309,4712889865950⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121209264520,124040093936⟩,⟨771389888814,801208814691⟩,⟨181707925932,193564247735⟩,⟨-2789074725990,-2177671972421⟩,⟨-811402519815,-538444221194⟩,⟨-217466638345,-107644894694⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11540813458,11814652963⟩,⟨167343138256,173281297884⟩,⟨21070653246,22073866664⟩,⟨648983525544,804073604404⟩,⟨90725523248,118142476190⟩,⟨-19189816524,-13299665199⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165835481156,176911153198⟩,⟨1464724600081,1888107060728⟩,⟨-6052189773,222997738973⟩,⟨-11185549436224,7462079022263⟩,⟨-5898078991214,6928056677654⟩,⟨-6081104335710,4967986317888⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176911153198,-165835481156⟩,⟨-1888107060728,-1464724600081⟩,⟨-222997738973,6052189773⟩,⟨-7462079022263,11185549436224⟩,⟨-6928056677654,5898078991214⟩,⟨-4967986317888,6081104335710⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48836729446,65108472786⟩,⟨-369766176541,225100408751⟩,⟨-18788174591,289905045614⟩,⟨-14811880224296,10835831801571⟩,⟨-10294395911819,6628325515891⟩,⟨-6960493139358,7892001861587⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27773745971420,29184185619282⟩,⟨-274773659683451,-228302724547640⟩,⟨-104628323152001,-67464810654304⟩,⟨2608934104633807,4566259064098798⟩,⟨476285209778613,2248812049237536⟩,⟨-601241761453919,1236822883006282⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13362010400,13993435372⟩,⟨170074783602,180774835166⟩,⟨40062666920,43673439854⟩,⟨453083465903,687544427995⟩,⟨71888665848,163383362560⟩,⟨10992495113,44418919946⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337525382307,371425826732⟩,⟨799069664205,2023792117168⟩,⟨-319614031591,339339998150⟩,⟨-47202680752523,5735275742166⟩,⟨-20512500942673,14202976100546⟩,⟨-15686139269202,12003593481989⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371425826732,-337525382307⟩,⟨-2023792117168,-799069664205⟩,⟨-339339998150,319614031591⟩,⟨-5735275742166,47202680752523⟩,⟨-14202976100546,20512500942673⟩,⟨-12003593481989,15686139269202⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58447536810,109069415212⟩,⟨-1303139819138,285253475378⟩,⟨-560753670942,395708235005⟩,⟨-30689736976997,33904589179823⟩,⟨-25299178121061,20718130292440⟩,⟨-19788994662138,20629720314307⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236130736525,238578867888⟩,⟨1563213618214,1571521947243⟩,⟨309178858732,311217743465⟩,⟨-3938729622245,-3925004181828⟩,⟨-1560253237826,-1552371637286⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1706650695272,-1618673131264⟩,⟨-5618635757286,-2668230067690⟩,⟨-544702398272,1501582614301⟩,⟨-20783202458765,104834602131657⟩,⟨-60283145355132,43637624973836⟩,⟨-49262326864610,53101049839259⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192533764273,-178441204969⟩,⟨-1877487818799,-1429764134469⟩,⟨-361898396137,-98106546750⟩,⟨-7327264270648,12412036836340⟩,⟨-7394145710000,6835615250151⟩,⟨-5590783596705,6856775342378⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43596972252,60137662919⟩,⟨-314274200585,141757812774⟩,⟨-52719537405,213111196715⟩,⟨-11265993892893,8487032654512⟩,⟨-8954398947826,5283243612865⟩,⟨-5940568753191,6507675031850⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2596049436,6458633882⟩,⟨-113846566903,39221038684⟩,⟨-35069233801,52190200807⟩,⟨-3820204829869,3959074016812⟩,⟨-2995967335720,2148151518534⟩,⟨-2157993343486,2213147344629⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1728672932,3289222606⟩,⟨-34378383024,15506854764⟩,⟨-5766978156,23312185136⟩,⟨-1313421974309,1108053005943⟩,⟨-1101347109490,632884804206⟩,⟨-670274030078,794485003313⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3038830175,5830513090⟩,⟨-84857835526,15455899574⟩,⟨-20947516488,35912348566⟩,⟨-2500146397963,2597785477859⟩,⟨-2134549606220,1362499042767⟩,⟨-1329215950313,1472602619964⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5830513090,-3038830175⟩,⟨-15455899574,84857835526⟩,⟨-35912348566,20947516488⟩,⟨-2597785477859,2500146397963⟩,⟨-1362499042767,2134549606220⟩,⟨-1472602619964,1329215950313⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3234463654,3419803707⟩,⟨-129302466477,124078874210⟩,⟨-70981582367,73137717295⟩,⟨-6417990307728,6459220414775⟩,⟨-4358466378487,4282701124754⟩,⟨-3630595963450,3542363294942⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48836729446,65108472786⟩,⟨-369766176541,225100408751⟩,⟨-18788174591,289905045614⟩,⟨-14811880224296,10835831801571⟩,⟨-10294395911819,6628325515891⟩,⟨-6960493139358,7892001861587⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3234463654,3419803707⟩,⟨-129302466477,124078874210⟩,⟨-70981582367,73137717295⟩,⟨-6417990307728,6459220414775⟩,⟨-4358466378487,4282701124754⟩,⟨-3630595963450,3542363294942⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (519/5120) u, BivariateJet2.affineZ (115/1024) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000015

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000016Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2111858714176,-2111858675264⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2111858714112,-2111858675264⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-174174399168,-174174399104⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-174174399168,-174174399104⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨90750542720,90750542784⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-98920185216,-98920185152⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨90750665472,90750665536⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-98920331200,-98920331136⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8169665664,-8169665600⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8169642496,-8169642432⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨189670727872,189670727936⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨189670996672,189670996736⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1937684276096,1937684314688⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1937684276160,1937684314752⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2531719137984,-2531719080128⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-115845112128,-115845112064⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2118788039808,-2118788000832⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2104967663872,-2104967625024⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-175361584320,-175361584256⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-172989378112,-172989378048⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨88148627072,88148627136⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-95836372288,-95836372224⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨93374981824,93374981888⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-102046912832,-102046912768⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8671931008,-8671930944⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7687745152,-7687745088⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨183984999360,183984999424⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨195421894656,195421894720⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2415873968064,2415874025920⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1929606040768,1929606079360⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1945798622784,1945798661376⟩



end LaneCBRB2Cell000016Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000016
open Set LaneCBRB2Cell000016Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨127345780326,127345780327⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110165911143,-110165911142⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439589902745,439589902746⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50913439907,50913439909⟩,⟨-127345780327,-127345780326⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161079351049,161079351052⟩,⟨972165847449,972165847450⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨50913439906,50913439910⟩,⟨-127345780327,-127345780326⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2111858714176,-2111858675264⟩,⟨6635907373699,6635907373832⟩,⟨3000596950287,3000596950352⟩,⟨-40049841731225,-40049841729636⟩,⟨-25614727585125,-25614727584243⟩,⟨-8188710179145,-8188710178798⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309389025636,-309389019929⟩,⟨-895096730516,-895096696068⟩,⟨-404741110531,-404741094951⟩,⟨5867334507719,5867334508310⟩,⟨3665413921174,3665413960407⟩,⟨1199652725969,1199652726102⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309389019929,309389025636⟩,⟨895096696068,895096730516⟩,⟨404741094951,404741110531⟩,⟨-5867334508310,-5867334507719⟩,⟨-3665413960407,-3665413921174⟩,⟨-1199652726102,-1199652725969⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161079351052,-161079351049⟩,⟨-972165847450,-972165847449⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938432276724,938432276727⟩,⟨-972165847450,-972165847449⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-174174399168,-174174399104⟩,⟨-1139035474281,-1139035474274⟩,⟨-515044315409,-515044315405⟩,⟨-1179980073785,-1179980073770⟩,⟨754681338028,754681338040⟩,⟨-241262247832,-241262247828⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148657707504,-148657707448⟩,⟨-818164381684,-818164381617⟩,⟨-369954161545,-369954161513⟩,⟨1007112029682,1007112029715⟩,⟨1380728950442,1380728950529⟩,⟨205917131565,205917131575⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148657707448,148657707504⟩,⟨818164381617,818164381684⟩,⟨369954161513,369954161545⟩,⟨-1007112029715,-1007112029682⟩,⟨-1380728950529,-1380728950442⟩,⟨-205917131575,-205917131565⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨458046727377,458046733140⟩,⟨1713261077685,1713261112200⟩,⟨774695256464,774695272076⟩,⟨-6874446538025,-6874446537401⟩,⟨-5046142910936,-5046142871616⟩,⟨-1405569857677,-1405569857534⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨815950853704,815950865326⟩,⟨4126751021352,4126751113813⟩,⟨774695256464,774695272076⟩,⟨-19070074606238,-19070074605094⟩,⟨-5046142910936,-5046142871616⟩,⟨-1405569857677,-1405569857534⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨101826879812,101826879820⟩,⟨-254691560654,-254691560652⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11872364367362,11872364368295⟩,⟨29695410629273,29695410634175⟩,⟨-102506754751979,-102506754735634⟩,⟨148549587117686,148549587155042⟩,⟨-256392078385929,-256392078219542⟩,⟨1770099778156697,1770099778582071⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8810516957086,8810517083272⟩,⟨66597101461339,66597102780745⟩,⟨-67705523982322,-67705522717446⟩,⟨127232324719319,127232331376907⟩,⟨-608568330888093,-608568318519131⟩,⟨1153970507501396,1153970529464049⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨94600887296,94601020672⟩,⟨-707457500962,-707455463432⟩,⟨719230130140,719232200769⟩,⟨9172949782354,9173000200122⟩,⟨-4234975788740,-4234909923666⟩,⟨-1380786354912,-1380703042234⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1194112515072,1194112648448⟩,⟨-707457500962,-707455463432⟩,⟨719230130140,719232200769⟩,⟨9172949782354,9173000200122⟩,⟨-4234975788740,-4234909923666⟩,⟨-1380786354912,-1380703042234⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨90750542720,90750665536⟩,⟨-651410766279,-651408817407⟩,⟨662250661328,662252641887⟩,⟨8060311123010,8060360799185⟩,⟨-3507117021240,-3507053591408⟩,⟨-1670281529268,-1670202289009⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨98558629189,98558773581⟩,⟨-765849176242,-765846733475⟩,⟨778593246155,778595728699⟩,⟨10349189335153,10349254371348⟩,⟨-5010634471619,-5010554246387⟩,⟨-1061553414344,-1061455037638⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-94601020672,-94600887296⟩,⟨707455463432,707457500962⟩,⟨-719232200769,-719230130140⟩,⟨-9173000200122,-9172949782354⟩,⟨4234909923666,4234975788740⟩,⟨1380703042234,1380786354912⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1004910607104,1004910740480⟩,⟨707455463432,707457500962⟩,⟨-719232200769,-719230130140⟩,⟨-9173000200122,-9172949782354⟩,⟨4234909923666,4234975788740⟩,⟨1380703042234,1380786354912⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-98920331200,-98920185152⟩,⟨774054328253,774056660331⟩,⟨-786939815568,-786937445566⟩,⟨-10581471124871,-10581411345187⟩,⟨5187581034716,5187657052824⟩,⟨947453819073,947548567708⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-90409324253,-90409178770⟩,⟨643807174701,643809677311⟩,⟨-654525042715,-654522499341⟩,⟨-7849690669511,-7849623125341⟩,⟨3347556274721,3347638836268⟩,⟨1771238013821,1771338468723⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8149304936,8149594811⟩,⟨-122042001541,-122037056164⟩,⟨124068203440,124073229358⟩,⟨2499498665642,2499631246007⟩,⟨-1663078196898,-1662915410119⟩,⟨709684599477,709883431085⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4074652468,4074797406⟩,⟨-61021000771,-61018528082⟩,⟨62034101720,62036614679⟩,⟨1249749332821,1249815623004⟩,⟨-831539098449,-831457705059⟩,⟨354842299738,354941715543⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4074797406,-4074652468⟩,⟨61018528082,61021000771⟩,⟨-62036614679,-62034101720⟩,⟨-1249815623004,-1249749332821⟩,⟨831457705059,831539098449⟩,⟨-354941715543,-354842299738⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758048586210,758048750412⟩,⟨61018528082,61021000771⟩,⟨-62036614679,-62034101720⟩,⟨-1249815623004,-1249749332821⟩,⟨831457705059,831539098449⟩,⟨-354941715543,-354842299738⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8139366288,8139389240⟩,⟨-121738051664,-121737529412⟩,⟨123763690646,123764221450⟩,⟨2488854845562,2488870990827⟩,⟨-1654296734166,-1654279042538⟩,⟨703345325011,703365414185⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8139389240,-8139366288⟩,⟨121737529412,121738051664⟩,⟨-123764221450,-123763690646⟩,⟨-2488870990827,-2488854845562⟩,⟨1654279042538,1654296734166⟩,⟨-703365414185,-703345325011⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091372238536,1091372261488⟩,⟨121737529412,121738051664⟩,⟨-123764221450,-123763690646⟩,⟨-2488870990827,-2488854845562⟩,⟨1654279042538,1654296734166⟩,⟨-703365414185,-703345325011⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8169665664,-8169642432⟩,⟨122645438086,122645966813⟩,⟨-124687247653,-124686710267⟩,⟨-2521113492116,-2521097055752⟩,⟨1680524748185,1680542726710⟩,⟨-722750903634,-722730527851⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4084832832,-4084821216⟩,⟨61322719043,61322983407⟩,⟨-62343623827,-62343355133⟩,⟨-1260556746058,-1260548527876⟩,⟨840262374092,840271363355⟩,⟨-361375451817,-361365263925⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4084821216,4084832832⟩,⟨-61322983407,-61322719043⟩,⟨62343355133,62343623827⟩,⟨1260548527876,1260556746058⟩,⟨-840271363355,-840262374092⟩,⟨361365263925,361375451817⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766208204832,766208235712⟩,⟨-61322983407,-61322719043⟩,⟨62343355133,62343623827⟩,⟨1260548527876,1260556746058⟩,⟨-840271363355,-840262374092⟩,⟨361365263925,361375451817⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272843059634,272843065372⟩,⟨30434382353,30434512916⟩,⟨-30941055363,-30940922661⟩,⟨-622217747707,-622213711390⟩,⟨413569760634,413574183542⟩,⟨-175841353547,-175836331252⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532416409664,1532416471424⟩,⟨-122645966814,-122645438086⟩,⟨124686710266,124687247654⟩,⟨2521097055752,2521113492116⟩,⟨-1680542726710,-1680524748184⟩,⟨722730527850,722750903634⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1203018109884,1203018269554⟩,⟨-846925380800,-846922716775⟩,⟨861018632678,861021340068⟩,⟨12173762725979,12173833341692⟩,⟨-6282175958129,-6282088298195⟩,⟨-420505352657,-420397589677⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1306524591992,1306524911332⟩,⟨-1693850761600,-1693845433550⟩,⟨1722037265356,1722042680136⟩,⟨24347525451966,24347666683377⟩,⟨-12564351916256,-12564176596394⟩,⟨-841010555807,-840795328863⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨189670727872,189670996736⟩,⟨-1425467702264,-1425462870006⟩,⟨1449187826653,1449192737697⟩,⟨18641709000314,18641845391954⟩,⟨-8694785780898,-8694622919312⟩,⟨-2617840224531,-2617645980566⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨65221746689,65221852773⟩,⟨-482500461364,-482498730802⟩,⟨490529288293,490531047021⟩,⟨6138150866605,6138196259896⟩,⟨-2768400681779,-2768344071092⟩,⟨-1063671044271,-1063601280885⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380268085651,380268108975⟩,⟨11982633981,11982949505⟩,⟨-12182389908,-12182069215⟩,⟨-248381394700,-248371584007⟩,⟨166279446348,166290163390⟩,⟨-72746923333,-72734793406⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179140693320,3179140888316⟩,⟨-100180599350,-100177949197⟩,⟨101845279833,101847973405⟩,⟨2082764719113,2082847327456⟩,⟨-1396648196480,-1396558089502⟩,⟨614607190340,614709019070⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨188582916042,188583234342⟩,⟨-1401050130567,-1401044874359⟩,⟨1424363425684,1424368767494⟩,⟨17959390080583,17959530162350⟩,⟨-8176822279148,-8176649938694⟩,⟨-2948179980026,-2947969247839⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨378253643914,378254231078⟩,⟨-2826517832831,-2826507744365⟩,⟨2873551252337,2873561505191⟩,⟨36601099080897,36601375554304⟩,⟨-16871608060046,-16871272858006⟩,⟨-5566020204557,-5565615228405⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522629906349,522630132765⟩,⟨84137371132,84140798906⟩,⟨-85541211298,-85537727692⟩,⟨-1716576499339,-1716484170767⟩,⟨1139596500252,1139709538476⟩,⟨-482423082141,-482285326293⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360322575596,360322809748⟩,⟨87011651749,87015215472⟩,⟨-88463468728,-88459846953⟩,⟨-1768214222655,-1768117785252⟩,⟨1171406036294,1171523770990⟩,⟨-491664594216,-491521435193⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720645151192,720645619496⟩,⟨174023303498,174030430944⟩,⟨-176926937456,-176919693906⟩,⟨-3536428445310,-3536235570504⟩,⟨2342812072588,2343047541980⟩,⟨-983329188432,-983042870386⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524277020424,1524277105136⟩,⟨-908437402,-907386422⟩,⟨922488816,923557008⟩,⟨32226064925,32258646554⟩,⟨-26263684172,-26228014018⟩,⟨19365113665,19405578623⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨999046136568,999046841311⟩,⟨240656901138,240667484705⟩,⟨-244673076808,-244662320772⟩,⟨-4881794254483,-4881504882505⟩,⟨3230969801320,3231320158585⟩,⟨-1350815725984,-1350391835394⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67705818938,67705821786⟩,⟨15104542396,15104607514⟩,⟨-15356003844,-15355937660⟩,⟨-307120983024,-307118958853⟩,⟨203541208818,203543422916⟩,⟨-85528432877,-85525923542⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50244689885,50244692715⟩,⟨265326545300,265326610169⟩,⟨36308512918,36308565166⟩,⟨-1288831602393,-1288829556183⟩,⟨-206675957234,-206674000704⟩,⟨-171662312151,-171660351709⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135766456019,2135766628173⟩,⟨-341869417206,-341867929624⟩,⟨347557872152,347559384104⟩,⟨7054791061951,7054837396617⟩,⟨-4712244378208,-4712193835378⟩,⟨2042854059908,2042911181331⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2976670261353,2976670621256⟩,⟨-714707756747,-714704618022⟩,⟨726599937380,726603127531⟩,⟨14805854514742,14805952471296⟩,⟨-9909510016629,-9909403451739⟩,⟨4329884538933,4330004640354⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136025732146,136025756255⟩,⟨685649288536,685649696276⟩,⟨131500436656,131500737643⟩,⟨-3157559668338,-3157547593207⟩,⟨-860627822224,-860616612187⟩,⟨-218883477862,-218872335029⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8887477290317,8887478865522⟩,⟨-44798120831025,-44798078310710⟩,⟨-8591830443879,-8591807732764⟩,⟨657920794080938,657922433425944⟩,⟨142845332015430,142846380189612⟩,⟨30912350424368,30913168408054⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8075403321278,8075410449072⟩,⟨-38759561329501,-38759408087617⟩,⟨-9784496674121,-9784383238375⟩,⟨538733258610536,538738396926071⟩,⟨163997242812367,164001658752664⟩,⟨20992685028297,20997054583060⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16150806642556,16150820898144⟩,⟨-77519122659002,-77518816175234⟩,⟨-19568993348242,-19568766476750⟩,⟨1077466517221072,1077476793852142⟩,⟨327994485624734,328003317505328⟩,⟨41985370056594,41994109166120⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10973683302499,10973683302600⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨2186188521914400,2186188521974786⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9874171674723,9874171674824⟩,⟨-109522921071186,-109522921069170⟩,⟨0,0⟩,⟨2186188521914418,2186188521974777⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2413489943680,2413490001536⟩,⟨-12195628068220,-12195628067696⟩,⟨0,0⟩,⟨108164909937337,108164909975027⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7505157003173,7505157003314⟩,⟨-45296043663306,-45296043661556⟩,⟨-20481776315183,-20481776314366⟩,⟨546752471806303,546752471838258⟩,⟨298457710036222,298457710052905⟩,⟨111790642304853,111790642311666⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6405645375397,6405645375538⟩,⟨-45296043663307,-45296043661556⟩,⟨-20481776315184,-20481776314365⟩,⟨546752471806312,546752471838256⟩,⟨298457710036226,298457710052904⟩,⟨111790642304854,111790642311667⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1937684276096,1937684314752⟩,⟨-7774942848293,-7774942847786⟩,⟨-3515641265842,-3515641265607⟩,⟨38869861648296,38869861665684⟩,⟨26369408918610,26369408927123⟩,⟨7947447929386,7947447933024⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99127803248,99127803250⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137481094623,137481094627⟩,⟨687319666897,687319666904⟩,⟨310789343524,310789343530⟩,⟨-1719138590394,-1719138590390⟩,⟨-1554705851356,-1554705851344⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4351174219776,4351174316288⟩,⟨-19970570916513,-19970570915482⟩,⟨-3515641265842,-3515641265607⟩,⟨147034771585633,147034771640711⟩,⟨26369408918610,26369408927123⟩,⟨7947447929386,7947447933024⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨756507287828,756508462156⟩,⟨-5653035665662,-5653015488730⟩,⟨5747102504674,5747123010382⟩,⟨73202198161794,73202751108608⟩,⟨-33743216120092,-33742545716012⟩,⟨-11132040409114,-11131230456810⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5107681507604,5107682778444⟩,⟨-25623606582175,-25623586404212⟩,⟨2231461238832,2231481744775⟩,⟨220236969747427,220237522749319⟩,⟨-7373807201482,-7373136788889⟩,⟨-3184592479728,-3183782523786⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨460489216074,460489330658⟩,⟨1774022714495,1774025549897⟩,⟨201180092188,201181940931⟩,⟨-31337386743474,-31337302075766⟩,⟨1119502802286,1119579640910⟩,⟨-287110794272,-287037771706⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38449198967,38449201113⟩,⟨-771244868230,-771244857436⟩,⟨331972847757,331972866257⟩,⟨9640870282859,9640870311788⟩,⟨-6658977614141,-6658977521421⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨498938415041,498938531771⟩,⟨1002777846265,1002780692461⟩,⟨533152939945,533154807188⟩,⟨-21696516460615,-21696431763978⟩,⟨-5539474811855,-5539397880511⟩,⟨-287110794272,-287037771706⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500903595558,500903607567⟩,⟨2531120470889,2531120592376⟩,⟨0,0⟩,⟨3131155626176,3131158552760⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227300957754,227301016383⟩,⟨1605411184538,1605412815978⟩,⟨242888040339,242888896821⟩,⟨-3846531828930,-3846478020611⟩,⟨-1296274237462,-1296234772031⟩,⟨-130798828307,-130765558340⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-756508462156,-756507287828⟩,⟨5653015488730,5653035665662⟩,⟨-5747123010382,-5747102504674⟩,⟨-73202751108608,-73202198161794⟩,⟨33742545716012,33743216120092⟩,⟨11131230456810,11132040409114⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3594665757620,3594667028460⟩,⟨-14317555427783,-14317535249820⟩,⟨-9262764276224,-9262743770281⟩,⟨73832020477025,73832573478917⟩,⟨60111954634622,60112625047215⟩,⟨19078678386196,19079488342138⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449470993008,449471151926⟩,⟨456831256577,456834574092⟩,⟨-142127792941,-142124869641⟩,⟨-14288797201372,-14288700840417⟩,⟨-7403847347659,-7403743200955⟩,⟨-4000053627240,-3999940352777⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨322158702098,322158702104⟩,⟨1944331694898,1944331694900⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-322158702104,-322158702098⟩,⟨-1944331694900,-1944331694898⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨777352925672,777352925678⟩,⟨-1944331694900,-1944331694898⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1369939619555,1369939646896⟩,⟨-8923394123470,-8923394054707⟩,⟨-4034943178873,-4034943147773⟩,⟨54978714872695,54978714887024⟩,⟨34952331986822,34952332071140⟩,⟨11241112140552,11241112143558⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1369939646896,-1369939619555⟩,⟨8923394054707,8923394123470⟩,⟨4034943147773,4034943178873⟩,⟨-54978714887024,-54978714872695⟩,⟨-34952332071140,-34952331986822⟩,⟨-11241112143558,-11241112140552⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-270428019120,-270427991779⟩,⟨8923394054707,8923394123470⟩,⟨4034943147773,4034943178873⟩,⟨-54978714887024,-54978714872695⟩,⟨-34952332071140,-34952331986822⟩,⟨-11241112143558,-11241112140552⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12522305680,-12522304412⟩,⟨444523312213,444523318599⟩,⟨78721685761,78721698149⟩,⟨-4612837685607,-4612837668797⟩,⟨1752229036166,1752229098648⟩,⟨2705853006935,2705853031993⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨436948687328,436948847514⟩,⟨901354568790,901357892691⟩,⟨-63406107180,-63403171492⟩,⟨-18901634886979,-18901538509214⟩,⟨-5651618311493,-5651514102307⟩,⟨-1294200620305,-1294087320784⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99127803250,-99127803248⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4590162874,4590162875⟩,⟨29229850712,29229850717⟩,⟨39631760400,39631760401⟩,⟨-305480639453,-305480639442⟩,⟨252372404139,252372404144⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10075666010,10075666255⟩,⟨13247728522,13247730086⟩,⟨86993946002,86993948090⟩,⟨-867414829180,-867414812683⟩,⟨114381737068,114381750391⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1481615953837,1481615974942⟩,⟨-7493417461464,-7493417080086⟩,⟨-1406703462116,-1406703393689⟩,⟨110425104968836,110425112593156⟩,⟨23391941755693,23391943301773⟩,⟨5223412093736,5223412388523⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13577180203,13577180727⟩,⟨-50816313453,-50816305924⟩,⟨104335543873,104335549299⟩,⟨-337523247193,-337523083328⟩,⟨-241342057521,-241341970758⟩,⟨-174732140508,-174732120470⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13577180727,-13577180203⟩,⟨50816305924,50816313453⟩,⟨-104335549299,-104335543873⟩,⟨337523083328,337523247193⟩,⟨241341970758,241342057521⟩,⟨174732120470,174732140508⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112704983977,-112704983451⟩,⟨-828363499568,-828363492037⟩,⟨-104335549299,-104335543873⟩,⟨2536546338880,2536546502745⟩,⟨241341970758,241342057521⟩,⟨174732120470,174732140508⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨89725446694,89725448492⟩,⟨-584445848836,-584445844304⟩,⟨611901716316,611901731797⟩,⟨3600881148547,3600881149627⟩,⟨-3417911474496,-3417911435108⟩,⟨-2443129134667,-2443129134274⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨120907000825,120907004971⟩,⟨-1399052551818,-1399052491114⟩,⟨709757156109,709757196602⟩,⟨21829744374648,21829745715197⟩,⟨-6119328634323,-6119327991296⟩,⟨-4431635480233,-4431635284432⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-120907004971,-120907000825⟩,⟨1399052491114,1399052551818⟩,⟨-709757196602,-709757156109⟩,⟨-21829745715197,-21829744374648⟩,⟨6119327991296,6119328634323⟩,⟨4431635284432,4431635480233⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨978604622805,978604626951⟩,⟨1399052491114,1399052551818⟩,⟨-709757196602,-709757156109⟩,⟨-21829745715197,-21829744374648⟩,⟨6119327991296,6119328634323⟩,⟨4431635284432,4431635480233⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122363084980,122363085503⟩,⟨786674237390,786674247586⟩,⟨187866764447,187866770691⟩,⟨-2510516179389,-2510515929289⟩,⟨-666814142978,-666814014191⟩,⟨-159965207650,-159965158922⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11552777591,11552777700⟩,⟨169822112476,169822114816⟩,⟨21389743316,21389744530⟩,⟨728149901970,728149960690⟩,⟨107733836082,107733863712⟩,⟨-16020344232,-16020337894⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨169699594204,169699745592⟩,⟨1680021260336,1680026724487⟩,⟨108580369183,108583050065⟩,⟨-1929023154434,-1928809761607⟩,⟨498288167211,498423931004⟩,⟨-555560841290,-555459842566⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-169699745592,-169699594204⟩,⟨-1680026724487,-1680021260336⟩,⟨-108583050065,-108580369183⟩,⟨1928809761607,1929023154434⟩,⟨-498423931004,-498288167211⟩,⟨555459842566,555560841290⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57601212162,57601422179⟩,⟨-74615539949,-74608444358⟩,⟨134304990274,134308527638⟩,⟨-1917722067323,-1917454866177⟩,⟨-1794698168466,-1794522939242⟩,⟨424661014259,424795282950⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28462785919644,28462811610282⟩,⟨-250819809940159,-250819166281728⟩,⟨-86128260493855,-86127814402063⟩,⟨3566108970448720,3566131957724590⟩,⟨1351610419196059,1351628921549165⟩,⟨315872614082223,315889570537278⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13617613663,13617613781⟩,⟨175095713640,175095716660⟩,⟨41814849942,41814851512⟩,⟨566909602380,566909689617⟩,⟨120410745984,120410787706⟩,⟨28594667676,28594682945⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352515801229,352516122467⟩,⟨1426219125635,1426231293737⟩,⟨15739474406,15746026232⟩,⟨-21043186152323,-21042679183110⟩,⟨-3397643747943,-3397314442210⟩,⟨-1898629959467,-1898384677921⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352516122467,-352515801229⟩,⟨-1426231293737,-1426219125635⟩,⟨-15746026232,-15739474406⟩,⟨21042679183110,21043186152323⟩,⟨3397314442210,3397643747943⟩,⟨1898384677921,1898629959467⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84432564861,84433046285⟩,⟨-524876724947,-524861232944⟩,⟨-79152133412,-79142645898⟩,⟨2141044296131,2141647643109⟩,⟨-2254303869283,-2253870354364⟩,⟨604184057616,604542638683⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236608897871,236608897877⟩,⟨1566499472387,1566499472396⟩,⟨310789343524,310789343530⟩,⟨-3918161845946,-3918161845942⟩,⟨-1554705851356,-1554705851344⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1655533206341,-1655531737350⟩,⟨-4221868608431,-4221826304681⟩,⟨473294432486,473319129671⟩,⟨43617346094307,43618898172778⟩,⟨-7977834284089,-7976723892502⟩,⟨1975927332576,1976868961281⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-184241936296,-184241772025⟩,⟨-1654340129761,-1654334353447⟩,⟨-230198484483,-230195475342⟩,⟨2592897729219,2593134822240⟩,⟨-266555562341,-266405973048⟩,⟨622495052901,622608578540⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52366961575,52367125852⟩,⟨-87840657374,-87834881051⟩,⟨80590859041,80593868188⟩,⟨-1325264116727,-1325027023702⟩,⟨-1821261413697,-1821111824392⟩,⟨270994845509,271108371151⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4423252978,4423294327⟩,⟨-33227173085,-33225683684⟩,⟨6166773663,6167616261⟩,⟨36130396314,36192648778⟩,⟨-314661204218,-314619085239⟩,⟨44924799769,44957024302⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2494106106,2494121755⟩,⟨-8367283518,-8366707044⟩,⟨7676678102,7676988824⟩,⟨-112204918805,-112180092669⟩,⟨-186362092832,-186345971904⟩,⟨37627729801,37639506958⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4395397067,4395424734⟩,⟨-32382384355,-32381257471⟩,⟨5553866764,5554464663⟩,⟨8757693878,8810155338⟩,⟨-296146580844,-296113748376⟩,⟨35245976844,35268833380⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4395424734,-4395397067⟩,⟨32381257471,32382384355⟩,⟨-5554464663,-5553866764⟩,⟨-8810155338,-8757693878⟩,⟨296113748376,296146580844⟩,⟨-35268833380,-35245976844⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨27828244,27897260⟩,⟨-845915614,-843299329⟩,⟨612309000,613749497⟩,⟨27320240976,27434954900⟩,⟨-18547455842,-18472504395⟩,⟨9655966389,9711047458⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57601212162,57601422179⟩,⟨-74615539949,-74608444358⟩,⟨134304990274,134308527638⟩,⟨-1917722067323,-1917454866177⟩,⟨-1794698168466,-1794522939242⟩,⟨424661014259,424795282950⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨27828244,27897260⟩,⟨-845915614,-843299329⟩,⟨612309000,613749497⟩,⟨27320240976,27434954900⟩,⟨-18547455842,-18472504395⟩,⟨9655966389,9711047458⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨125413045043,129278515610⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110380659508,-109951162777⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439375154380,439804651111⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50116228546,51711406245⟩,⟨-129278515610,-125413045043⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160067391323,162092065753⟩,⟨970233112166,974098582733⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49686731815,52140902976⟩,⟨-129278515610,-125413045043⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2118788039808,-2104967625024⟩,⟨6581337485731,6691136211210⟩,⟨2980393204025,3021042098892⟩,⟨-40719263594802,-39393856333014⟩,⟨-25937316852654,-25297980961529⟩,⟨-8300681077596,-8078808287428⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312355705560,-306442122161⟩,⟨-918999743528,-871049632338⟩,⟨-413628248991,-395797106351⟩,⟨5612122140490,6120881865217⟩,⟨3541168060753,3788805699630⟩,⟨1158284162773,1240717178937⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306442122161,312355705560⟩,⟨871049632338,918999743528⟩,⟨395797106351,413628248991⟩,⟨-6120881865217,-5612122140490⟩,⟨-3788805699630,-3541168060753⟩,⟨-1240717178937,-1158284162773⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162092065753,-160067391323⟩,⟨-974098582733,-970233112166⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937419562023,939444236453⟩,⟨-974098582733,-970233112166⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175361584320,-172989378048⟩,⟨-1142532929444,-1135546472143⟩,⟨-515852610120,-514238176627⟩,⟨-1187237553371,-1172762304483⟩,⟨750815424706,758539963773⟩,⟨-242020101148,-240507599574⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149832366956,-147486959580⟩,⟨-823552866577,-812782678459⟩,⟨-371626380685,-368283586702⟩,⟨989663111374,1024554047736⟩,⟨1372317254725,1389148344312⟩,⟨204202085440,207630569805⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147486959580,149832366956⟩,⟨812782678459,823552866577⟩,⟨368283586702,371626380685⟩,⟨-1024554047736,-989663111374⟩,⟨-1389148344312,-1372317254725⟩,⟨-207630569805,-204202085440⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨453929081741,462188072516⟩,⟨1683832310797,1742552610105⟩,⟨764080693053,785254629676⟩,⟨-7145435912953,-6601785251864⟩,⟨-5177954043942,-4913485315478⟩,⟨-1448347748742,-1362486248213⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨810887678567,821039129979⟩,⟨4090170170271,4163182317207⟩,⟨764080693053,785254629676⟩,⟨-19449221604726,-18689005158921⟩,⟨-5177954043942,-4913485315478⟩,⟨-1448347748742,-1362486248213⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨99373463630,104281805952⟩,⟨-258557031220,-250826090086⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11592873834301,12165479348852⟩,⟨27884012845504,31653019920078⟩,⟨-107683363448848,-97689538153918⟩,⟨134137261128075,164714211636118⟩,⟨-315894075166583,-200731379508351⟩,⟨1646398641291055,1906329612034706⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8549721816431,9084337380372⟩,⟨63689757726202,69699559791732⟩,⟨-72354272529507,-63357441679725⟩,⟨91187633768829,165648197940631⟩,⟨-681533063778900,-540642915587651⟩,⟨1044378958095427,1273375069020705⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨91778446336,97454534912⟩,⟨-786002831338,-636593260173⟩,⟨633271687553,815940060992⟩,⟨6902888814633,11714074208518⟩,⟨-7702548807458,-1039484324381⟩,⟨-5680251017468,3166790883411⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1191290074112,1196966162688⟩,⟨-786002831338,-636593260173⟩,⟨633271687553,815940060992⟩,⟨6902888814633,11714074208518⟩,⟨-7702548807458,-1039484324381⟩,⟨-5680251017468,3166790883411⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨88148627072,93374981888⟩,⟨-725448210559,-584763139963⟩,⟨581712002987,753079039375⟩,⟨5862225316007,10500607754254⟩,⟨-6799757896756,-457976637056⟩,⟨-5758437469419,2615054565010⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨95506570212,101651215811⟩,⟨-856498409996,-684610628223⟩,⟨681038513876,889120671108⟩,⟨7582096759872,13463324950440⟩,⟨-9133282207237,-1253138197063⟩,⟨-6081140466562,4233484636571⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-97454534912,-91778446336⟩,⟨636593260173,786002831338⟩,⟨-815940060992,-633271687553⟩,⟨-11714074208518,-6902888814633⟩,⟨1039484324381,7702548807458⟩,⟨-3166790883411,5680251017468⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1002057092864,1007733181440⟩,⟨636593260173,786002831338⟩,⟨-815940060992,-633271687553⟩,⟨-11714074208518,-6902888814633⟩,⟨1039484324381,7702548807458⟩,⟨-3166790883411,5680251017468⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-102046912832,-95836372224⟩,⟨694570452392,862445122814⟩,⟨-895293881974,-690946370358⟩,⟨-13529813027483,-7970329382384⟩,⟨1570630930099,9153915050104⟩,⟨-4203781973814,5798481805068⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-93528851835,-87341974487⟩,⟨560057820527,734967924285⟩,⟨-765364248618,-553976448759⟩,⟨-10994495794147,-4943623356306⟩,⟨-563492462958,7499129355367⟩,⟨-3584163200745,6937167235728⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1977718377,14309241324⟩,⟨-296440589469,50357296062⟩,⟨-84325734742,335144222349⟩,⟨-3412399034275,8519701594134⟩,⟨-9696774670195,6245991158304⟩,⟨-9665303667307,11170651872299⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨988859188,7154620662⟩,⟨-148220294735,25178648031⟩,⟨-42162867371,167572111175⟩,⟨-1706199517138,4259850797067⟩,⟨-4848387335098,3122995579152⟩,⟨-4832651833654,5585325936150⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7154620662,-988859188⟩,⟨-25178648031,148220294735⟩,⟨-167572111175,42162867371⟩,⟨-4259850797067,1706199517138⟩,⟨-3122995579152,4848387335098⟩,⟨-5585325936150,4832651833654⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754968762954,761134543692⟩,⟨-25178648031,148220294735⟩,⟨-167572111175,42162867371⟩,⟨-4259850797067,1706199517138⟩,⟨-3122995579152,4848387335098⟩,⟨-5585325936150,4832651833654⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7660931452,8637822589⟩,⟨-139333752246,-106275438822⟩,⟨105720922132,144640688014⟩,⟨1889543254099,3200311957313⟩,⟨-2531995978298,-906836693384⟩,⟨-277456257819,1772380193577⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8637822589,-7660931452⟩,⟨106275438822,139333752246⟩,⟨-144640688014,-105720922132⟩,⟨-3200311957313,-1889543254099⟩,⟨906836693384,2531995978298⟩,⟨-1772380193577,277456257819⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090873805187,1091850696324⟩,⟨106275438822,139333752246⟩,⟨-144640688014,-105720922132⟩,⟨-3200311957313,-1889543254099⟩,⟨906836693384,2531995978298⟩,⟨-1772380193577,277456257819⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8671931008,-7687745088⟩,⟨107021116646,140437033146⟩,⟨-145785990612,-106462709209⟩,⟨-3243590424059,-1913218082137⟩,⟨923562043238,2570665750141⟩,⟨-1805744356770,269344735167⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4335965504,-3843872544⟩,⟨53510558323,70218516573⟩,⟨-72892995306,-53231354604⟩,⟨-1621795212030,-956609041068⟩,⟨461781021619,1285332875071⟩,⟨-902872178385,134672367584⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3843872544,4335965504⟩,⟨-70218516573,-53510558323⟩,⟨53231354604,72892995306⟩,⟨956609041068,1621795212030⟩,⟨-1285332875071,-461781021619⟩,⟨-134672367584,902872178385⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765967256160,766459368384⟩,⟨-70218516573,-53510558323⟩,⟨53231354604,72892995306⟩,⟨956609041068,1621795212030⟩,⟨-1285332875071,-461781021619⟩,⟨-134672367584,902872178385⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272718451296,272962674081⟩,⟨26568859705,34833438062⟩,⟨-36160172004,-26430230533⟩,⟨-800077989329,-472385813524⟩,⟨226709173346,632998994575⟩,⟨-443095048395,69364064455⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531934512320,1532918736768⟩,⟨-140437033146,-107021116646⟩,⟨106462709208,145785990612⟩,⟨1913218082136,3243590424060⟩,⟨-2570665750142,-923562043238⟩,⟨-269344735168,1805744356770⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1199648718410,1206444052165⟩,⟨-946321769096,-757827868308⟩,⟨753873726070,982365217031⟩,⟨9174946421084,15587932510504⟩,⟨-10814730973359,-2189902986493⟩,⟨-5891350245228,5412524230978⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1299785809044,1313376476554⟩,⟨-1892643538191,-1515655736616⟩,⟨1507747452141,1964730434061⟩,⟨18349892842178,31175865020994⟩,⟨-21629461946708,-4379805972987⟩,⟨-11777809211245,10825048461951⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨183984999360,195421894720⟩,⟨-1601020385820,-1268852561214⟩,⟨1262232029408,1661999956198⟩,⟨13030594314952,24907936889036⟩,⟨-16840107175138,-1246545656101⟩,⟨-12475301668963,7708064511833⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨63018760644,67462690787⟩,⟨-546340452098,-423973039004⟩,⟨419977077769,568569820311⟩,⟨4150315824810,8296269138709⟩,⟨-5657703199423,-54233015823⟩,⟨-4675901623071,2683120797886⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379974888061,380559502025⟩,⟨2153396987,22019045614⟩,⟨-24007258630,-632324808⟩,⟨-649805295106,141906754690⟩,⟨-317172639235,662676087434⟩,⟨-694210988522,539878432846⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176706436659,3181593988445⟩,⟨-184369192171,-17975402093⟩,⟨5278308062,201016835945⟩,⟨-1188005824592,5462297517780⟩,⟨-5571996256466,2655680405028⟩,⟨-4520475866824,5838146950853⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨182073656622,195212934571⟩,⟨-1592226490031,-1225972182087⟩,⟨1213699323333,1657571791802⟩,⟨11932053072949,24524813854692⟩,⟨-16908476696428,-2646758368⟩,⟨-13803719796985,8330100459650⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨366058655982,390634829291⟩,⟨-3193246875851,-2494824743301⟩,⟨2475931352741,3319571748000⟩,⟨24962647387901,49432750743728⟩,⟨-33748583871566,-1249192414469⟩,⟨-26279021465948,16038164971483⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518391819274,526893739881⟩,⟨-34859729168,205210356216⟩,⟨-232002862276,58374307296⟩,⟨-5904533426027,2402187686486⟩,⟨-4368953164518,6723938849194⟩,⟨-7745711315660,6741863509297⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355948605395,364741050616⟩,⟨-36197358060,213084637162⟩,⟨-240905218626,60614231754⟩,⟨-6138149648359,2535859086627⟩,⟨-4583510470978,6993751937665⟩,⟨-8056272718562,7053598549484⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711897210790,729482101232⟩,⟨-72394716120,426169274324⟩,⟨-481810437252,121228463508⟩,⟨-12276299296718,5071718173254⟩,⟨-9167020941956,13987503875330⟩,⟨-16112545437124,14107197098968⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523296689731,1525257805316⟩,⟨-34161594324,32312635600⟩,⟨-38177978806,40065068480⟩,⟨-1287093875177,1354047169961⟩,⟨-1663829056758,1608433935060⟩,⟨-2041724928745,2083200614589⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨986283943916,1011947705359⟩,⟨-123091810962,612626082660⟩,⟨-693703698109,194751383363⟩,⟨-17910270354140,7958962860140⟩,⟨-13849460270868,20501290367279⟩,⟨-23741263265917,20985279793673⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67643990111,67765196438⟩,⟨13180066654,17295366708⟩,⟨-17954111620,-13111296608⟩,⟨-395967659888,-232130258282⟩,⟨110172898598,313016930092⟩,⟨-218733206923,36818816733⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49887310624,50602355192⟩,⟨261355111617,269500597250⟩,⟨33600771221,38727326105⟩,⟨-1396317961413,-1190003710435⟩,⟨-296697937761,-104969123310⟩,⟨-278244615544,-74551730213⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134423402855,2137166896805⟩,⟨-391589418444,-298222116064⟩,⟨296666073174,406504253202⟩,⟨5352155001722,9080182454859⟩,⟨-7205190643358,-2594297850602⟩,⟨-730413890302,5073730632586⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2973862933447,2979598484411⟩,⟨-818920066175,-623263193032⟩,⟨620011173117,850111045533⟩,⟨11229167775526,19064157833507⟩,⟨-15145897110149,-5465213617292⟩,⟨-1484415444893,10691400408058⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134930836715,137128791574⟩,⟨669201649399,702048643328⟩,⟨119011727340,144072603914⟩,⟨-3675879992975,-2637537074189⟩,⟨-1382550441171,-342556890043⟩,⟨-784445042157,350290492149⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8815988281806,8959596257216⟩,⟨-46617011724545,-43022868002763⟩,⟨-9566622383895,-7651245092907⟩,⟨589478281473111,729182614566480⟩,⟨96700547335998,191354051589819⟩,⟨-9979009662156,72517798725205⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7908117997519,8246063656255⟩,⟨-43907521989365,-33600264555450⟩,⟨-14457533895087,-5276348402397⟩,⟨330880155631528,746404213933493⟩,⟨-39700230553432,373656388694480⟩,⟨-206033833196684,249816964211206⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15816235995038,16492127312510⟩,⟨-87815043978730,-67200529110900⟩,⟨-28915067790174,-10552696804794⟩,⟨661760311263056,1492808427866986⟩,⟨-79400461106864,747312777388960⟩,⟨-412067666393368,499633928422412⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10952333724070,10995116277821⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨2173453475238562,2199023255588622⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9852822096294,9895604650045⟩,⟨-109951162778820,-109097176394608⟩,⟨0,0⟩,⟨2173453475238575,2199023255588602⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2411110045440,2415874025920⟩,⟨-12269843176037,-12121908488212⟩,⟨0,0⟩,⟨104571265817406,111755106875729⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7458266473430,7552605247219⟩,⟨-45961779013523,-44642882785551⟩,⟨-20751702693960,-20216763651861⟩,⟨534437054643874,559405678157391⟩,⟨292613938393525,304450427120117⟩,⟨109601214708883,114035660703190⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6358754845654,6453093619443⟩,⟨-45961779013523,-44642882785551⟩,⟨-20751702693960,-20216763651860⟩,⟨534437054643872,559405678157385⟩,⟨292613938393523,304450427120114⟩,⟨109601214708882,114035660703189⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1929606040768,1945798661376⟩,⟨-7947390909916,-7606486379184⟩,⟨-3588239987550,-3444637258032⟩,⟨33615547733903,44106414105078⟩,⟨23920890475791,28813244735116⟩,⟨6964256262813,8926619818691⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨98913096826,99342593558⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136469956367,138494630798⟩,⟨683596088077,691041910656⟩,⟨309764818990,311813264378⟩,⟨-1725980926281,-1712309844048⟩,⟨-1558655711318,-1550755991382⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4340716086208,4361672687296⟩,⟨-20217234085953,-19728394867396⟩,⟨-3588239987550,-3444637258032⟩,⟨138186813551309,155861520980807⟩,⟨23920890475791,28813244735116⟩,⟨6964256262813,8926619818691⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨732117311964,781269658582⟩,⟨-6386493751702,-4989649486602⟩,⟨4951862705482,6639143496000⟩,⟨49925294775802,98865501487456⟩,⟨-67497167743132,-2498384828938⟩,⟨-52558042931896,32076329942966⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5072833398172,5142942345878⟩,⟨-26603727837655,-24718044353998⟩,⟨1363622717932,3194506237968⟩,⟨188112108327111,254727022468263⟩,⟨-43576277267341,26314859906178⟩,⟨-45593786669083,41002949761657⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨456356848276,464672876805⟩,⟨1650615188943,1890695433477⟩,⟨122672778100,288628630021⟩,⟨-35929107612006,-26640931327032⟩,⟨-2847351895003,4933193699907⟩,⟨-4119469865907,3704680578132⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37394246917,39511317887⟩,⟨-792582362627,-750102669253⟩,⟨330673852191,333275037186⟩,⟨9278057723618,10011625245203⟩,⟨-6692236630045,-6625935308195⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨493751095193,504184194692⟩,⟨858032826316,1140592764224⟩,⟨453346630291,621903667207⟩,⟨-26651049888388,-16629306081829⟩,⟨-9539588525048,-1692741608288⟩,⟨-4119469865907,3704680578132⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500409295618,501398026980⟩,⟨2510857612204,2551553037358⟩,⟨0,0⟩,⟨1957166706152,4308831445771⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨224715802465,229917496157⟩,⟨1518043334847,1690153726418⟩,⟨206326938436,283599794520⟩,⟨-7355660381467,-298722413012⟩,⟨-3314964512381,672804667502⟩,⟨-1878555906815,1689404173219⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-781269658582,-732117311964⟩,⟨4989649486602,6386493751702⟩,⟨-6639143496000,-4951862705482⟩,⟨-98865501487456,-49925294775802⟩,⟨2498384828938,67497167743132⟩,⟨-32076329942966,52558042931896⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3559446427626,3629555375332⟩,⟨-15227584599351,-13341901115694⟩,⟨-10227383483550,-8396499963514⟩,⟨39321312063853,105936226205005⟩,⟨26419275304729,96310412478248⟩,⟨-25112073680153,61484662750587⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441793871385,457179277571⟩,⟨294935440808,625192313501⟩,⟨-285441657276,-12847953106⟩,⟨-19958100819605,-8789556378711⟩,⟨-12612420826576,-1868123916344⟩,⟨-10125396603546,1876734175223⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨320134782646,324184131506⟩,⟨1940466224332,1948197165466⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-324184131506,-320134782646⟩,⟨-1948197165466,-1940466224332⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨775327496270,779376845130⟩,⟨-1948197165466,-1940466224332⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1360673759678,1379258193958⟩,⟨-9081133513106,-8769214571804⟩,⟨-4100123773118,-3971184819363⟩,⟨50552733473129,59427917915228⟩,⟨32885670577724,37031377571217⟩,⟨10416926197424,12068721239552⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1379258193958,-1360673759678⟩,⟨8769214571804,9081133513106⟩,⟨3971184819363,4100123773118⟩,⟨-59427917915228,-50552733473129⟩,⟨-37031377571217,-32885670577724⟩,⟨-12068721239552,-10416926197424⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-279746566182,-261162131902⟩,⟨8769214571804,9081133513106⟩,⟨3971184819363,4100123773118⟩,⟨-59427917915228,-50552733473129⟩,⟨-37031377571217,-32885670577724⟩,⟨-12068721239552,-10416926197424⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13266106694,-11801869557⟩,⟨426068027872,463536455065⟩,⟨67558498056,90072720761⟩,⟨-4953668597723,-4284945966687⟩,⟨1527240262315,1973139190884⟩,⟨2601523977284,2809360005621⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428527764691,445377408014⟩,⟨721003468680,1088728768566⟩,⟨-217883159220,77224767655⟩,⟨-24911769417328,-13074502345398⟩,⟨-11085180564261,105015274540⟩,⟨-7523872626262,4686094180844⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99342593558,-98913096826⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4469864975,4711012055⟩,⟨28030051808,30430447275⟩,⟨39526600801,39737037424⟩,⟨-311127430929,-299838377815⟩,⟨251814268106,252930624064⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9801930303,10351151705⟩,⟨8895004041,17583109173⟩,⟨86677559241,87311197222⟩,⟨-937669822040,-796734743681⟩,⟨108761645553,119972071186⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1472433865174,1490867171334⟩,⟨-7654268290245,-7335222954819⟩,⟨-1443739224885,-1370285833033⟩,⟨106600210819154,114354228389078⟩,⟨22464442898158,24344605848592⟩,⟨4993901801944,5459079042700⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13126458836,14035497100⟩,⟨-60147783264,-41550505487⟩,⟨102484236628,106172548293⟩,⟨-565910330326,-109080181247⟩,⟨-284989727299,-197479302630⟩,⟨-184772327884,-164653381578⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14035497100,-13126458836⟩,⟨41550505487,60147783264⟩,⟨-106172548293,-102484236628⟩,⟨109080181247,565910330326⟩,⟨197479302630,284989727299⟩,⟨164653381578,184772327884⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113378090658,-112039555662⟩,⟨-838058796735,-818602525496⟩,⟨-106172548293,-102484236628⟩,⟨2308103436799,2764933585878⟩,⟨197479302630,284989727299⟩,⟨164653381578,184772327884⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨87198548368,92273420900⟩,⟨-605663536558,-563831434267⟩,⟨600927595778,622656929190⟩,⟨3254310234161,3960487500158⟩,⟨-3650870369191,-3180952688665⟩,⟨-2555878507731,-2329701634326⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨116773749697,125116834176⟩,⟨-1463603806002,-1336798315314⟩,⟨683582934810,735610082524⟩,⟨20335209041404,23399697101171⟩,⟨-6800718376157,-5430501996776⟩,⟨-4704745913760,-4159563856087⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-125116834176,-116773749697⟩,⟨1336798315314,1463603806002⟩,⟨-735610082524,-683582934810⟩,⟨-23399697101171,-20335209041404⟩,⟨5430501996776,6800718376157⟩,⟨4159563856087,4704745913760⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨974394793600,982737878079⟩,⟨1336798315314,1463603806002⟩,⟨-735610082524,-683582934810⟩,⟨-23399697101171,-20335209041404⟩,⟨5430501996776,6800718376157⟩,⟨4159563856087,4704745913760⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120940617277,123785793763⟩,⟨771729243669,802005460800⟩,⟨181858176869,193851676619⟩,⟨-2827854628884,-2201693629628⟩,⟨-804806354248,-527606173895⟩,⟨-215423475329,-103758118301⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11416761511,11691182810⟩,⟨166830183334,172835836990⟩,⟨20886160808,21896341070⟩,⟨648701105064,807165021442⟩,⟨93827591240,121605525694⟩,⟨-19001372468,-13051397579⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164227635065,175361924755⟩,⟨1466072551994,1894675927845⟩,⟨-7013018267,218860461143⟩,⟨-11405067046950,7587378916381⟩,⟨-5788637351794,6892546214977⟩,⟨-5818219364795,4723985481402⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-175361924755,-164227635065⟩,⟨-1894675927845,-1466072551994⟩,⟨-218860461143,7013018267⟩,⟨-7587378916381,11405067046950⟩,⟨-6892546214977,5788637351794⟩,⟨-4723985481402,5818219364795⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49353877710,65689861092⟩,⟨-376632592998,224081174424⟩,⟨-12533522707,290612812787⟩,⟨-14943039297848,11106344633938⟩,⟨-10207510727358,6461442019296⟩,⟨-6602541388217,7507623538014⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27756963862191,29186011713978⟩,⟨-274612628082748,-227352330131374⟩,⟨-104992623985010,-68069987984251⟩,⟨2574713970650569,4572861327591902⟩,⟨487117657836630,2250283343127046⟩,⟨-562933535465126,1206821602497651⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13302845134,13936117046⟩,⟨169772485786,180583597408⟩,⟨40006926004,43648621910⟩,⟨446594268670,685647269223⟩,⟨74072304238,166730545762⟩,⟨11652501788,45529125880⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨335827818752,369927579734⟩,⟨805207514972,2042799815819⟩,⟨-320795786586,335062106331⟩,⟨-47779349509485,5950732389795⟩,⟨-20382081383336,14164773167305⟩,⟨-15176952969022,11551200043462⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-369927579734,-335827818752⟩,⟨-2042799815819,-805207514972⟩,⟨-335062106331,320795786586⟩,⟨-5950732389795,47779349509485⟩,⟨-14164773167305,20382081383336⟩,⟨-11551200043462,15176952969022⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58600184957,109549589262⟩,⟨-1321796347139,283521253594⟩,⟨-552945265551,398020554241⟩,⟨-30862501807123,34704847164087⟩,⟨-25249953731566,20487096657876⟩,⟨-19075072669724,19863047149866⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235383053193,237837224356⟩,⟨1562346396837,1570651212878⟩,⟨309764818990,311813264378⟩,⟨-3925004181833,-3911333099600⟩,⟨-1558655711318,-1550755991382⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1700614944258,-1611664677629⟩,⟨-5722772538581,-2720215627069⟩,⟨-517222108554,1507414986025⟩,⟨-20668462568811,107906676625469⟩,⟨-60099462087266,42981294846380⟩,⟨-47184925223755,50846853678710⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-191459522067,-177274815501⟩,⟨-1884746246312,-1430410811534⟩,⟨-358060613042,-96859220704⟩,⟨-7448270339253,12703699725074⟩,⟨-7379021000869,6733353992463⟩,⟨-5342489088474,6589198500718⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43923531126,60562408855⟩,⟨-322399849475,140240401344⟩,⟨-48295794052,214954043674⟩,⟨-11373274521086,8792366625474⟩,⟨-8937676712187,5182598001081⟩,⟨-5694332809364,6238041639054⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2630391793,6544994268⟩,⟨-116495870591,39265134897⟩,⟨-34284257664,52734712150⟩,⟨-3871479411556,4085555022863⟩,⟨-3011276047401,2132123855548⟩,⟨-2089773742263,2145132046912⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1754666833,3335849548⟩,⟨-35516334718,15449216380⟩,⟨-5320379616,23679849034⟩,⟨-1335149837998,1157656816426⟩,⟨-1110653797846,625761204772⟩,⟨-646184867914,771244356823⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3079381458,5903431507⟩,⟨-86964916524,15201490157⟩,⟨-20301937435,36408917189⟩,⟨-2532497641805,2695945874325⟩,⟨-2148921333101,1349186489331⟩,⟨-1286992905003,1426674949073⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5903431507,-3079381458⟩,⟨-15201490157,86964916524⟩,⟨-36408917189,20301937435⟩,⟨-2695945874325,2532497641805⟩,⟨-1349186489331,2148921333101⟩,⟨-1426674949073,1286992905003⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3273039714,3465612810⟩,⟨-131697360748,126230051421⟩,⟨-70693174853,73036649585⟩,⟨-6567425285881,6618052664668⟩,⟨-4360462536732,4281045188649⟩,⟨-3516448691336,3432124951915⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49353877710,65689861092⟩,⟨-376632592998,224081174424⟩,⟨-12533522707,290612812787⟩,⟨-14943039297848,11106344633938⟩,⟨-10207510727358,6461442019296⟩,⟨-6602541388217,7507623538014⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3273039714,3465612810⟩,⟨-131697360748,126230051421⟩,⟨-70693174853,73036649585⟩,⟨-6567425285881,6618052664668⟩,⟨-4360462536732,4281045188649⟩,⟨-3516448691336,3432124951915⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (513/5120) u, BivariateJet2.affineZ (593/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000016

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000017Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2101360023744,-2101359984896⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2101360023744,-2101359984896⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-175986594432,-175986594368⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-175986594432,-175986594368⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨93068508608,93068508672⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-101680939776,-101680939712⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨93068634944,93068635008⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-101681090560,-101681090496⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8612455616,-8612455552⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8612431104,-8612431040⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨194749448320,194749448384⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨194749725440,194749725504⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1925373390528,1925373429120⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1925373390528,1925373429120⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2531719137984,-2531719080128⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-115845112128,-115845112064⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2108228430016,-2108228391104⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2094529183872,-2094529145088⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-177176625920,-177176625856⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-174798734656,-174798734592⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨90467785920,90467785984⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-98584286336,-98584286272⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨95691495488,95691495552⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-104820421248,-104820421184⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9128925760,-9128925696⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8116500352,-8116500288⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨189052072256,189052072320⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨200511916672,200511916736⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2415873968064,2415874025920⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1917352519232,1917352557824⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1933429656512,1933429695104⟩



end LaneCBRB2Cell000017Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000017
open Set LaneCBRB2Cell000017Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨131211250892,131211250893⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110165911143,-110165911142⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439589902745,439589902746⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨52458873159,52458873160⟩,⟨-131211250893,-131211250892⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨162624784301,162624784303⟩,⟨968300376883,968300376884⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52458873158,52458873161⟩,⟨-131211250893,-131211250892⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2101360023744,-2101359984896⟩,⟨6546711364603,6546711364692⟩,⟨2972082094328,2972082094373⟩,⟨-38980424226416,-38980424225368⟩,⟨-25130204164710,-25130204164119⟩,⟨-8033814061209,-8033814060972⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310804553560,-310804547809⟩,⟨-882291878418,-882291844176⟩,⟨-400543684880,-400543669333⟩,⟨5765453426209,5765453426605⟩,⟨3619254248305,3619254287373⟩,⟨1188252352910,1188252353002⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨310804547809,310804553560⟩,⟨882291844176,882291878418⟩,⟨400543669333,400543684880⟩,⟨-5765453426605,-5765453426209⟩,⟨-3619254287373,-3619254248305⟩,⟨-1188252353002,-1188252352910⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162624784303,-162624784301⟩,⟨-968300376884,-968300376883⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨936886843473,936886843475⟩,⟨-968300376884,-968300376883⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175986594432,-175986594368⟩,⟨-1136377921178,-1136377921173⟩,⟨-515893902118,-515893902115⟩,⟨-1174480330283,-1174480330272⟩,⟨757173147110,757173147119⟩,⟨-242058848237,-242058848234⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149957054375,-149957054319⟩,⟨-813315307746,-813315307681⟩,⟨-369229637383,-369229637351⟩,⟨1000767196586,1000767196611⟩,⟨1377854252992,1377854253074⟩,⟨206256800314,206256800323⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149957054319,149957054375⟩,⟨813315307681,813315307746⟩,⟨369229637351,369229637383⟩,⟨-1000767196611,-1000767196586⟩,⟨-1377854253074,-1377854252992⟩,⟨-206256800323,-206256800314⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨460761602128,460761607935⟩,⟨1695607151857,1695607186164⟩,⟨769773306684,769773322263⟩,⟨-6766220623216,-6766220622795⟩,⟨-4997108540447,-4997108501297⟩,⟨-1394509153325,-1394509153224⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨818665728455,818665740121⟩,⟨4109097095524,4109097187777⟩,⟨769773306684,769773322263⟩,⟨-18961848691429,-18961848690488⟩,⟨-4997108540447,-4997108501297⟩,⟨-1394509153325,-1394509153224⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨104917746316,104917746322⟩,⟨-262422501786,-262422501784⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11522605679160,11522605679820⟩,⟨28820586749121,28820586752643⟩,⟨-96556041051756,-96556041040474⟩,⟨144173330875306,144173330902280⟩,⟨-241508026514545,-241508026399091⟩,⟨1618222357165565,1618222357451010⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8579411198324,8579411321073⟩,⟨64521311446309,64521312723979⟩,⟨-63825908487641,-63825907291037⟩,⟨124048745526387,124048751960048⟩,⟨-572860605560648,-572860593944569⟩,⟨1055070494413033,1055070514549079⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨97120944128,97121081600⟩,⟨-722201057982,-722198969279⟩,⟨714415181986,714417247424⟩,⟨9291567690915,9291619154622⟩,⟨-4152875889291,-4152810460037⟩,⟨-1358537823726,-1358457312086⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1196632571904,1196632709376⟩,⟨-722201057982,-722198969279⟩,⟨714415181986,714417247424⟩,⟨9291567690915,9291619154622⟩,⟨-4152875889291,-4152810460037⟩,⟨-1358537823726,-1358457312086⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨93068508608,93068635008⟩,⟨-663585865443,-663583870028⟩,⟨656431830333,656433803550⟩,⟨8136953111002,8137003787200⟩,⟨-3419647006325,-3419584066868⟩,⟨-1640182467947,-1640105991275⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨101289341563,101289490765⟩,⟨-783332160369,-783329645904⟩,⟨774886998374,774889484922⟩,⟨10513917595955,10513984332634⟩,⟨-4935571566878,-4935491538491⟩,⟨-1047013502371,-1046918063803⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-97121081600,-97120944128⟩,⟨722198969279,722201057982⟩,⟨-714417247424,-714415181986⟩,⟨-9291619154622,-9291567690915⟩,⟨4152810460037,4152875889291⟩,⟨1358457312086,1358537823726⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1002390546176,1002390683648⟩,⟨722198969279,722201057982⟩,⟨-714417247424,-714415181986⟩,⟨-9291619154622,-9291567690915⟩,⟨4152810460037,4152875889291⟩,⟨1358457312086,1358537823726⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-101681090560,-101680939712⟩,⟨792172330852,792174730572⟩,⟨-783636750790,-783634377760⟩,⟨-10762624179831,-10762562874182⟩,⟨5119763593563,5119839406969⟩,⟨931568836830,931660736134⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-92699499765,-92699349528⟩,⟨655410862426,655413441466⟩,⟨-648349461070,-648346910649⟩,⟨-7912028007553,-7911958575225⟩,⟨3254032976174,3254115448253⟩,⟨1741990473294,1742088031398⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8589841798,8590141237⟩,⟨-127921297943,-127916204438⟩,⟨126537537304,126542574273⟩,⟨2601889588402,2602025757409⟩,⟨-1681538590704,-1681376090238⟩,⟨694976970923,695169967595⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4294920899,4295070619⟩,⟨-63960648972,-63958102219⟩,⟨63268768652,63271287137⟩,⟨1300944794201,1301012878705⟩,⟨-840769295352,-840688045119⟩,⟨347488485461,347584983798⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4295070619,-4294920899⟩,⟨63958102219,63960648972⟩,⟨-63271287137,-63268768652⟩,⟨-1301012878705,-1300944794201⟩,⟨840688045119,840769295352⟩,⟨-347584983798,-347488485461⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757828312997,757828481981⟩,⟨63958102219,63960648972⟩,⟨-63271287137,-63268768652⟩,⟨-1301012878705,-1300944794201⟩,⟨840688045119,840769295352⟩,⟨-347584983798,-347488485461⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8578788573,8578812860⟩,⟨-127585640956,-127585091366⟩,⟨126209992182,126210535716⟩,⟨2590199397306,2590216300201⟩,⟨-1672169110042,-1672151085094⟩,⟨688389972158,688409903360⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8578812860,-8578788573⟩,⟨127585091366,127585640956⟩,⟨-126210535716,-126209992182⟩,⟨-2590216300201,-2590199397306⟩,⟨1672151085094,1672169110042⟩,⟨-688409903360,-688389972158⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090932814916,1090932839203⟩,⟨127585091366,127585640956⟩,⟨-126210535716,-126209992182⟩,⟨-2590216300201,-2590199397306⟩,⟨1672151085094,1672169110042⟩,⟨-688409903360,-688389972158⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8612455616,-8612431040⟩,⟨128588384588,128588941364⟩,⟨-127203022653,-127202472011⟩,⟨-2625623689991,-2625606465825⟩,⟨1700176797159,1700195130183⟩,⟨-708539558520,-708519327728⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4306227808,-4306215520⟩,⟨64294192294,64294470682⟩,⟨-63601511327,-63601236005⟩,⟨-1312811844996,-1312803232912⟩,⟨850088398579,850097565092⟩,⟨-354269779260,-354259663864⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4306215520,4306227808⟩,⟨-64294470682,-64294192294⟩,⟨63601236005,63601511327⟩,⟨1312803232912,1312811844996⟩,⟨-850097565092,-850088398579⟩,⟨354259663864,354269779260⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766429599136,766429630688⟩,⟨-64294470682,-64294192294⟩,⟨63601236005,63601511327⟩,⟨1312803232912,1312811844996⟩,⟨-850097565092,-850088398579⟩,⟨354259663864,354269779260⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272733203729,272733209801⟩,⟨31896272841,31896410239⟩,⟨-31552633929,-31552498045⟩,⟨-647554075051,-647549849326⟩,⟨418037771273,418042277511⟩,⟨-172102475840,-172097493039⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532859198272,1532859261376⟩,⟨-128588941364,-128588384588⟩,⟨127202472010,127203022654⟩,⟨2625606465824,2625623689992⟩,⟨-1700195130184,-1700176797158⟩,⟨708519327728,708539558520⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1206042553403,1206042718806⟩,⟨-868928114713,-868925363316⟩,⟨859560173819,859562894656⟩,⟨12431380528438,12431453271797⟩,⟨-6235194671459,-6235106906023⟩,⟨-409310666903,-409205761020⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1312573479030,1312573809836⟩,⟨-1737856229426,-1737850726632⟩,⟨1719120347639,1719125789312⟩,⟨24862761056886,24862906543581⟩,⟨-12470389342913,-12470213812049⟩,⟨-818621180613,-818411675234⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨194749448320,194749725504⟩,⟨-1455760886675,-1455755910221⟩,⟨1440065920568,1440070841868⟩,⟨18899501827394,18899642124848⟩,⟨-8539498389075,-8539335684676⟩,⟨-2571853296945,-2571664735284⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨66939720677,66939830356⟩,⟨-492121089505,-492119305934⟩,⟨486815293973,486817057729⟩,⟨6205184393942,6205231058106⟩,⟨-2704959056824,-2704902490669⟩,⟨-1049284659384,-1049216880909⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380224810223,380224834343⟩,⟨12571054404,12571386605⟩,⟨-12435893429,-12435564887⟩,⟨-258953377198,-258943097446⟩,⟨168445637684,168456564575⟩,⟨-71485654791,-71473613057⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179502521721,3179502723417⟩,⟨-105124013145,-105121221887⟩,⟨103988236290,103990996807⟩,⟨2172275785029,2172362389442⟩,⟨-1415538159062,-1415446243195⟩,⟨604476133885,604577265399⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨193572314579,193572644023⟩,⟨-1429486772340,-1429481344016⟩,⟨1414074539106,1414079907173⟩,⟨18170135561442,18170279969369⟩,⟨-8001309559003,-8001136942264⟩,⟨-2905375223196,-2905170037508⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨388321762899,388322369527⟩,⟨-2885247659015,-2885237254237⟩,⟨2854140459674,2854150749041⟩,⟨37069637388836,37069922094217⟩,⟨-16540807948078,-16540472626940⟩,⟨-5477228520141,-5476834772792⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522326219634,522326452576⟩,⟨88165071622,88168601938⟩,⟨-87218329072,-87214837936⟩,⟨-1785981978298,-1785887132563⟩,⟨1151511842912,1151624689412⟩,⟨-471858335995,-471724628271⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360008560036,360008800867⟩,⟨91150451443,91154121627⟩,⟨-90171671112,-90168041653⟩,⟨-1838765194248,-1838666109671⟩,⟨1182892996390,1183010538286⟩,⟨-480308305874,-480169359737⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720017120072,720017601734⟩,⟨182300902886,182308243254⟩,⟨-180343342224,-180336083306⟩,⟨-3677530388496,-3677332219342⟩,⟨2365785992780,2366021076572⟩,⟨-960616611748,-960338719474⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524280385412,1524280472803⟩,⟨-1003849998,-1002743632⟩,⟨991936294,993030472⟩,⟨35390165623,35424292686⟩,⟨-28044045090,-28007687116⟩,⟨20109424368,20149586362⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨998177686857,998178411826⟩,⟨252070913887,252081829459⟩,⟨-249364915216,-249354120701⟩,⟨-5075409948817,-5075112185715⟩,⟨3261712336578,3262062624661⟩,⟨-1318883902230,-1318471895873⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67651308578,67651311591⟩,⟨15823702922,15823771438⟩,⟨-15653224418,-15653156656⟩,⟨-319400222339,-319398102864⟩,⟨205557380254,205559636184⟩,⟨-83568921616,-83566432151⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50371279774,50371282736⟩,⟨264608496640,264608564762⟩,⟨35708047063,35708100752⟩,⟨-1286238048258,-1286235899974⟩,⟨-201833355089,-201831354355⟩,⟨-169942955331,-169941001702⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137000885092,2137001061043⟩,⟨-358538727016,-358537159820⟩,⟨354672882646,354674432584⟩,⟨7350936347996,7350984935210⟩,⟨-4770330185186,-4770278615256⟩,⟨2004964403653,2005021148400⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2979251315472,2979251683419⟩,⟨-749772982456,-749769674284⟩,⟨741688732716,741692004468⟩,⟨15435108404469,15435211189721⟩,⟨-10037891134743,-10037782340192⟩,⟨4254311619352,4254430991473⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136486688942,136486713825⟩,⟨682637787405,682638214117⟩,⟨130733548618,130733857931⟩,⟨-3138969452574,-3138956765499⟩,⟨-852605484398,-852594007074⟩,⟨-217404888266,-217393772686⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8857461548709,8857463163521⟩,⟨-44300604567549,-44300560722620⟩,⟨-8484126472883,-8484103306164⟩,⟨646844369567303,646846063557923⟩,⟨140196485915267,140197551182348⟩,⟨30360983354915,30361795655368⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8041134133341,8041141439545⟩,⟨-38187134744355,-38186977426400⟩,⟨-9711050042128,-9710936091618⟩,⟨526029548399214,526034818652696⟩,⟨161652977898004,161657398479505⟩,⟨20786303861895,20790559396027⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16082268266682,16082282879090⟩,⟨-76374269488710,-76373954852800⟩,⟨-19422100084256,-19421872183236⟩,⟨1052059096798428,1052069637305392⟩,⟨323305955796008,323314796959010⟩,⟨41572607723790,41581118792054⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10973683302499,10973683302600⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨2186188521914400,2186188521974786⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9874171674723,9874171674824⟩,⟨-109522921071186,-109522921069170⟩,⟨0,0⟩,⟨2186188521914418,2186188521974777⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2413489943680,2413490001536⟩,⟨-12195628068220,-12195628067696⟩,⟨0,0⟩,⟨108164909937337,108164909975027⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7433835038097,7433835038189⟩,⟨-44262535382365,-44262535381221⟩,⟨-20094346845799,-20094346845255⟩,⟨527095914378936,527095914399608⟩,⟨289551900173949,289551900184876⟩,⟨108633773299547,108633773304078⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6334323410321,6334323410413⟩,⟨-44262535382365,-44262535381220⟩,⟨-20094346845800,-20094346845254⟩,⟨527095914378935,527095914399606⟩,⟨289551900173947,289551900184876⟩,⟨108633773299546,108633773304078⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1925373390528,1925373429120⟩,⟨-7683089285985,-7683089285664⟩,⟨-3487975996543,-3487975996393⟩,⟨37805943890748,37805943901834⟩,⟨25887377309102,25887377314573⟩,⟨7791755211812,7791755214184⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99127803248,99127803250⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138571541205,138571541208⟩,⟨681864770467,681864770474⟩,⟨309553600608,309553600612⟩,⟨-1705494687256,-1705494687251⟩,⟨-1548524118348,-1548524118340⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4338863334208,4338863430656⟩,⟨-19878717354205,-19878717353360⟩,⟨-3487975996543,-3487975996393⟩,⟨145970853828085,145970853876861⟩,⟨25887377309102,25887377314573⟩,⟨7791755211812,7791755214184⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨776643525798,776644739054⟩,⟨-5770495318030,-5770474508474⟩,⟨5708280919348,5708301498082⟩,⟨74139274777672,74139844188434⟩,⟨-33081615896156,-33080945253880⟩,⟨-10954457040282,-10953669545584⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5115506860006,5115508169710⟩,⟨-25649212672235,-25649191861834⟩,⟨2220304922805,2220325501689⟩,⟨220110128605757,220110698065295⟩,⟨-7194238587054,-7193567939307⟩,⟨-3162701828470,-3161914331400⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461194720203,461194838291⟩,⟨1777971391558,1777974315054⟩,⟨200174280997,200176136316⟩,⟨-31405422782185,-31405335541583⟩,⟨1126771333446,1126848251593⟩,⟨-285137216080,-285066218320⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨39616291010,39616293221⟩,⟨-794655336393,-794655325287⟩,⟨331972847757,331972866257⟩,⟨9933510527549,9933510557218⟩,⟨-6658977614141,-6658977521421⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨500811011213,500811131512⟩,⟨983316055165,983318989767⟩,⟨532147128754,532149002573⟩,⟨-21471912254636,-21471824984365⟩,⟨-5532206280695,-5532129269828⟩,⟨-285137216080,-285066218320⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500903595558,500903607567⟩,⟨2531120470889,2531120592376⟩,⟨0,0⟩,⟨3131155626176,3131158552760⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228154054831,228154115107⟩,⟨1600855785117,1600857465042⟩,⟨242429823773,242430683240⟩,⟨-3828480022217,-3828424626009⟩,⟨-1295278336958,-1295238820351⟩,⟨-129899726914,-129867379408⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-776644739054,-776643525798⟩,⟨5770474508474,5770495318030⟩,⟨-5708301498082,-5708280919348⟩,⟨-74139844188434,-74139274777672⟩,⟨33080945253880,33081615896156⟩,⟨10953669545584,10954457040282⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3562218595154,3562219904858⟩,⟨-14108242845731,-14108222035330⟩,⟨-9196277494625,-9196256915741⟩,⟨71831009639651,71831579099189⟩,⟨58968322562982,58968993210729⟩,⟨18745424757396,18746212254466⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨448946703581,448946868654⟩,⟨431055386678,431058821694⟩,⟨-156109993919,-156107031589⟩,⟨-13971149155703,-13971049543504⟩,⟨-7260248014064,-7260143026469⟩,⟨-3954501387431,-3954390132835⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨325249568602,325249568606⟩,⟨1936600753766,1936600753768⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-325249568606,-325249568602⟩,⟨-1936600753768,-1936600753766⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨774262059170,774262059174⟩,⟨-1936600753768,-1936600753766⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1355823374998,1355823402182⟩,⟨-8801547815441,-8801547747208⟩,⟨-3995734836596,-3995734805614⟩,⟨53687345798109,53687345807214⟩,⟨34367248018235,34367248099911⟩,⟨11064891215002,11064891216954⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1355823402182,-1355823374998⟩,⟨8801547747208,8801547815441⟩,⟨3995734805614,3995734836596⟩,⟨-53687345807214,-53687345798109⟩,⟨-34367248099911,-34367248018235⟩,⟨-11064891216954,-11064891215002⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-256311774406,-256311747222⟩,⟨8801547747208,8801547815441⟩,⟨3995734805614,3995734836596⟩,⟨-53687345807214,-53687345798109⟩,⟨-34367248099911,-34367248018235⟩,⟨-11064891216954,-11064891215002⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12228908294,-12228906995⟩,⟨450518438661,450518445187⟩,⟨88166122946,88166135306⟩,⟨-4662162483664,-4662162466780⟩,⟨1658678947472,1658679009638⟩,⟨2667109242155,2667109267061⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨436717795287,436717961659⟩,⟨881573825339,881577266881⟩,⟨-67943870973,-67940896283⟩,⟨-18633311639367,-18633212010284⟩,⟨-5601569066592,-5601464016831⟩,⟨-1287392145276,-1287280865774⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99127803250,-99127803248⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4729493281,4729493283⟩,⟨30117097445,30117097450⟩,⟨39631760400,39631760401⟩,⟨-314753238962,-314753238953⟩,⟨252372404139,252372404144⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10381504100,10381504354⟩,⟨13649851812,13649853434⟩,⟨86993946002,86993948090⟩,⟨-893744453050,-893744435966⟩,⟨114381737068,114381750391⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1476702591018,1476702612062⟩,⟨-7411956235012,-7411955857349⟩,⟨-1388510885668,-1388510817990⟩,⟨108608311433346,108608318931893⟩,⟨22952340239978,22952341758458⟩,⟨5126576332122,5126576621328⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13942912121,13942912662⟩,⟨-51650644663,-51650636943⟩,⟨103727282893,103727288324⟩,⟨-358906045614,-358905878425⟩,⟨-233340582998,-233340496425⟩,⟨-171314709051,-171314689151⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13942912662,-13942912121⟩,⟨51650636943,51650644663⟩,⟨-103727288324,-103727282893⟩,⟨358905878425,358906045614⟩,⟨233340496425,233340582998⟩,⟨171314689151,171314709051⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113070715912,-113070715369⟩,⟨-827529168549,-827529160827⟩,⟨-103727288324,-103727282893⟩,⟨2557929133977,2557929301166⟩,⟨233340496425,233340582998⟩,⟨171314689151,171314709051⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨91861619217,91861621064⟩,⟨-596334632437,-596334627791⟩,⟨603358249552,603358265002⟩,⟨3637499255052,3637499255777⟩,⟨-3345753256258,-3345753217176⟩,⟨-2417265350112,-2417265349850⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨123375040050,123375044290⟩,⟨-1420160719488,-1420160657829⟩,⟨694335385198,694335425486⟩,⟨21999268754591,21999270106417⟩,⟨-5890152720864,-5890152084948⟩,⟨-4342096409779,-4342096217086⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-123375044290,-123375040050⟩,⟨1420160657829,1420160719488⟩,⟨-694335425486,-694335385198⟩,⟨-21999270106417,-21999268754591⟩,⟨5890152084948,5890152720864⟩,⟨4342096217086,4342096409779⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨976136583486,976136587726⟩,⟨1420160657829,1420160719488⟩,⟨-694335425486,-694335385198⟩,⟨-21999270106417,-21999268754591⟩,⟨5890152084948,5890152720864⟩,⟨4342096217086,4342096409779⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123022574189,123022574727⟩,⟨784336406064,784336416477⟩,⟨187311765400,187311771679⟩,⟨-2525260685205,-2525260431696⟩,⟨-663195002755,-663194874259⟩,⟨-155786720054,-155786671705⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11627877642,11627877754⟩,⟨170201591032,170201593440⟩,⟨21334050106,21334051328⟩,⟨719551489389,719551549551⟩,⟨108145040204,108145067876⟩,⟨-15663913625,-15663907310⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170077917219,170078073392⟩,⟨1681798473533,1681804105930⟩,⟨106649269139,106651982687⟩,⟨-1994349255092,-1994129489917⟩,⟨512531801626,512668687071⟩,⟨-543163381946,-543064181231⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170078073392,-170077917219⟩,⟨-1681804105930,-1681798473533⟩,⟨-106651982687,-106649269139⟩,⟨1994129489917,1994349255092⟩,⟨-512668687071,-512531801626⟩,⟨543064181231,543163381946⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58075981439,58076197888⟩,⟨-80948320813,-80941008491⟩,⟨135777841086,135781414101⟩,⟨-1834350532300,-1834075370917⟩,⟨-1807947024029,-1807770621977⟩,⟨413164454317,413296002538⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28161931713841,28161957866352⟩,⟨-246118910967680,-246118255210500⟩,⟨-85028124969374,-85027678849271⟩,⟨3462617087672167,3462640482084043⟩,⟨1322789949198863,1322808377222564⟩,⟨309990298984485,310006753849955⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13764796458,13764796579⟩,⟨175516258794,175516261894⟩,⟨41916019754,41916021344⟩,⟨553917791924,553917880839⟩,⟨118829994064,118830035978⟩,⟨28959064452,28959079706⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352559489242,352559819746⟩,⟨1414355348160,1414367838832⟩,⟨9132456699,9139088761⟩,⟨-21040366858775,-21039847403883⟩,⟨-3352149715254,-3351818159761⟩,⟨-1860448571320,-1860207198820⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352559819746,-352559489242⟩,⟨-1414367838832,-1414355348160⟩,⟨-9139088761,-9132456699⟩,⟨21039847403883,21040366858775⟩,⟨3351818159761,3352149715254⟩,⟨1860207198820,1860448571320⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84157975541,84158472417⟩,⟨-532794013493,-532778081279⟩,⟨-77082959734,-77073352982⟩,⟨2406535764516,2407154848491⟩,⟨-2249750906831,-2249314301577⟩,⟨572815053544,573167705546⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237699344453,237699344458⟩,⟨1561044575957,1561044575966⟩,⟨309553600608,309553600612⟩,⟨-3904517942808,-3904517942803⟩,⟨-1548524118348,-1548524118340⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1653857215059,-1653855704416⟩,⟨-4249978218047,-4249934713313⟩,⟨480098050007,480122954271⟩,⟨44185421754384,44187017354182⟩,⟨-8013160082517,-8012044632755⟩,⟨1894184587612,1895105622516⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185047404400,-185047234567⟩,⟨-1655301916201,-1655295953165⟩,⟨-228032174239,-228029120708⟩,⟨2678821442395,2679065992613⟩,⟨-280564135791,-280413015847⟩,⟨609845452573,609957284187⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52651940053,52652109891⟩,⟨-94257340244,-94251377199⟩,⟨81521426369,81524479904⟩,⟨-1225696500413,-1225451950190⟩,⟨-1829088254139,-1828937134187⟩,⟨258345245181,258457076798⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4445207219,4445250032⟩,⟨-34338097600,-34336554901⟩,⟨6321081859,6321939307⟩,⟨65149814069,65214310404⟩,⟨-317337406412,-317294664378⟩,⟨42841760574,42873629696⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2521325578,2521341845⟩,⟨-9027367628,-9026767406⟩,⟨7807577738,7807895372⟩,⟨-101230734307,-101204889558⟩,⟨-189156046688,-189139600580⟩,⟨36831118119,36842814068⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4415135824,4415164398⟩,⟨-33426429839,-33425264791⟩,⟨5673539441,5674147535⟩,⟨35580385127,35634593597⟩,⟨-297795057974,-297761745638⟩,⟨32825212838,32847825650⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4415164398,-4415135824⟩,⟨33425264791,33426429839⟩,⟨-5674147535,-5673539441⟩,⟨-35634593597,-35580385127⟩,⟨297761745638,297795057974⟩,⟨-32847825650,-32825212838⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨30042821,30114208⟩,⟨-912832809,-910125062⟩,⟨646934324,648399866⟩,⟨29515220472,29633925277⟩,⟨-19575660774,-19499606404⟩,⟨9993934924,10048416858⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58075981439,58076197888⟩,⟨-80948320813,-80941008491⟩,⟨135777841086,135781414101⟩,⟨-1834350532300,-1834075370917⟩,⟨-1807947024029,-1807770621977⟩,⟨413164454317,413296002538⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨30042821,30114208⟩,⟨-912832809,-910125062⟩,⟨646934324,648399866⟩,⟨29515220472,29633925277⟩,⟨-19575660774,-19499606404⟩,⟨9993934924,10048416858⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨129278515609,133143986176⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110380659508,-109951162777⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439375154380,439804651111⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨51660906823,53257594471⟩,⟨-133143986176,-129278515609⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161612069600,163638253979⟩,⟨966367641600,970233112167⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨51231410092,53687091202⟩,⟨-133143986176,-129278515609⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2108228430016,-2094529145088⟩,⟨6493178904133,6600884396329⟩,⟨2952232008407,2992167163279⟩,⟨-39628207390425,-38345544709115⟩,⟨-25443801869153,-24822235658637⟩,⟨-8142764575496,-7926859172096⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313763684314,-307865038826⟩,⟨-905944898327,-858497508369⟩,⟨-409356602457,-391674853984⟩,⟨5515999239342,6013297371674⟩,⟨3497246147275,3740431669780⟩,⟨1147606791366,1228601790348⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307865038826,313763684314⟩,⟨858497508369,905944898327⟩,⟨391674853984,409356602457⟩,⟨-6013297371674,-5515999239342⟩,⟨-3740431669780,-3497246147275⟩,⟨-1228601790348,-1147606791366⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-163638253979,-161612069600⟩,⟨-970233112167,-966367641600⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨935873373797,937899558176⟩,⟨-970233112167,-966367641600⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-177176625920,-174798734592⟩,⟨-1139879195573,-1132885125472⟩,⟨-516704867759,-515085103714⟩,⟨-1181728821848,-1167271609589⟩,⟨753296304259,761042677570⟩,⟨-242820461032,-241300462283⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151134262678,-148783766670⟩,⟨-818701985736,-807935425955⟩,⟨-370905623807,-367555303143⟩,⟨983367603035,1018159909498⟩,⟨1369431035676,1386285197148⟩,⟨204536255121,207975727289⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148783766670,151134262678⟩,⟨807935425955,818701985736⟩,⟨367555303143,370905623807⟩,⟨-1018159909498,-983367603035⟩,⟨-1386285197148,-1369431035676⟩,⟨-207975727289,-204536255121⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨456648805496,464897946992⟩,⟨1666432934324,1724646884063⟩,⟨759230157127,780262226264⟩,⟨-7031457281172,-6499366842377⟩,⟨-5126716866928,-4866677182951⟩,⟨-1436577517637,-1352143046487⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨813607402322,823749004455⟩,⟨4072770793798,4145276591165⟩,⟨759230157127,780262226264⟩,⟨-19335242972945,-18586586749434⟩,⟨-5126716866928,-4866677182951⟩,⟨-1436577517637,-1352143046487⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨102462820184,107374182404⟩,⟨-266287972352,-258557031218⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11258999068006,11798677973569⟩,⟨27111669754620,30663278917896⟩,⟨-101287734232154,-92143648368953⟩,⟨130569801532773,159380004455233⟩,⟨-295883842845459,-190544474946221⟩,⟨1508207236443997,1739043158710775⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8331339799466,8839514734621⟩,⟨61767039163206,67455065702665⟩,⟨-68109783210953,-59810819627551⟩,⟨89986756541941,160287801667598⟩,⟨-639833323247995,-510387390743715⟩,⟨956858339378722,1161783820983367⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨94293841920,99979029760⟩,⟨-800388502811,-651485912925⟩,⟨630852748581,808157057489⟩,⟨7036192243559,11808947772220⟩,⟨-7498614907025,-1063064307575⟩,⟨-5404254808100,2914508104355⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1193805469696,1199490657536⟩,⟨-800388502811,-651485912925⟩,⟨630852748581,808157057489⟩,⟨7036192243559,11808947772220⟩,⟨-7498614907025,-1063064307575⟩,⟨-5404254808100,2914508104355⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨90467785920,95691495552⟩,⟨-737169068093,-597183756365⟩,⟨578270391787,744324016212⟩,⟨5955480912601,10551855308620⟩,⟨-6592250636440,-475423532560⟩,⟨-5481271340969,2380170977148⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨98226280590,104392761314⟩,⟨-873858683062,-702002328454⟩,⟨679769262281,882340337830⟩,⟨7752849370365,13612326282820⟩,⟨-8927957874633,-1288941635730⟩,⟨-5786449089721,3944431139875⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-99979029760,-94293841920⟩,⟨651485912925,800388502811⟩,⟨-808157057489,-630852748581⟩,⟨-11808947772220,-7036192243559⟩,⟨1063064307575,7498614907025⟩,⟨-2914508104355,5404254808100⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨999532598016,1005217785856⟩,⟨651485912925,800388502811⟩,⟨-808157057489,-630852748581⟩,⟨-11808947772220,-7036192243559⟩,⟨1063064307575,7498614907025⟩,⟨-2914508104355,5404254808100⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-104820421248,-98584286272⟩,⟨712598152034,880447988717⟩,⟨-888993599151,-690029506280⟩,⟨-13695176987752,-8158055856221⟩,⟨1609995458563,8960542713771⟩,⟨-3924816468210,5511772159743⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-95831048166,-89619977899⟩,⟨571497386969,746527533956⟩,⟨-756190283408,-550240312731⟩,⟨-11045342201104,-5008608231730⟩,⟨-545556341884,7279055776139⟩,⟨-3311613513056,6623781042638⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2395232424,14772783415⟩,⟨-302361296093,44525205502⟩,⟨-76421021127,332100025099⟩,⟨-3292492830739,8603718051090⟩,⟨-9473514216517,5990114140409⟩,⟨-9098062602777,10568212182513⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1197616212,7386391708⟩,⟨-151180648047,22262602751⟩,⟨-38210510564,166050012550⟩,⟨-1646246415370,4301859025545⟩,⟨-4736757108259,2995057070205⟩,⟨-4549031301389,5284106091257⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7386391708,-1197616212⟩,⟨-22262602751,151180648047⟩,⟨-166050012550,38210510564⟩,⟨-4301859025545,1646246415370⟩,⟨-2995057070205,4736757108259⟩,⟨-5284106091257,4549031301389⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754736991908,760925786668⟩,⟨-22262602751,151180648047⟩,⟨-166050012550,38210510564⟩,⟨-4301859025545,1646246415370⟩,⟨-2995057070205,4736757108259⟩,⟨-5284106091257,4549031301389⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8086616275,9091132954⟩,⟨-145559290000,-111742537566⟩,⟨108203547550,146972085534⟩,⟨1978884927433,3312868823170⟩,⟨-2540298483344,-929925766466⟩,⟨-258909425425,1718049174216⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9091132954,-8086616275⟩,⟨111742537566,145559290000⟩,⟨-146972085534,-108203547550⟩,⟨-3312868823170,-1978884927433⟩,⟨929925766466,2540298483344⟩,⟨-1718049174216,258909425425⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090420494822,1091425011501⟩,⟨111742537566,145559290000⟩,⟨-146972085534,-108203547550⟩,⟨-3312868823170,-1978884927433⟩,⟨929925766466,2540298483344⟩,⟨-1718049174216,258909425425⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9128925760,-8116500288⟩,⟨112570463454,146772857486⟩,⟨-148197431882,-109005252256⟩,⟨-3360081695733,-2005072152391⟩,⟨947975999990,2581260391557⟩,⟨-1752347776709,250261275954⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4564462880,-4058250144⟩,⟨56285231727,73386428743⟩,⟨-74098715941,-54502626128⟩,⟨-1680040847867,-1002536076195⟩,⟨473987999995,1290630195779⟩,⟨-876173888355,125130637977⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4058250144,4564462880⟩,⟨-73386428743,-56285231727⟩,⟨54502626128,74098715941⟩,⟨1002536076195,1680040847867⟩,⟨-1290630195779,-473987999995⟩,⟨-125130637977,876173888355⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766181633760,766687865760⟩,⟨-73386428743,-56285231727⟩,⟨54502626128,74098715941⟩,⟨1002536076195,1680040847867⟩,⟨-1290630195779,-473987999995⟩,⟨-125130637977,876173888355⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272605123705,272856252876⟩,⟨27935634391,36389822500⟩,⟨-36743021384,-27050886887⟩,⟨-828217205793,-494721231858⟩,⟨232481441616,635074620836⟩,⟨-429512293554,64727356357⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532363267520,1533375731520⟩,⟨-146772857486,-112570463454⟩,⟨109005252256,148197431882⟩,⟨2005072152390,3360081695734⟩,⟨-2581260391558,-947975999990⟩,⟨-250261275954,1752347776710⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1202650646083,1209491138173⟩,⟨-968515487307,-779442987496⟩,⟨754757303679,977915879108⟩,⟨9428477623050,15840598930703⟩,⟨-10639906644815,-2250181513105⟩,⟨-5592116422992,5108078489041⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1305789664390,1319470648570⟩,⟨-1937030974614,-1558885974993⟩,⟨1509514607358,1955831758216⟩,⟨18856955246106,31681197861392⟩,⟨-21279813289622,-4500363026212⟩,⟨-11179334492212,10216156978077⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨189052072256,200511916736⟩,⟨-1631034567077,-1299015827095⟩,⟨1257874788564,1646865355715⟩,⟨13293949275291,25141740088106⟩,⟨-16432087697894,-1307152823435⟩,⟨-11880014256703,7163244476714⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨64726055467,69191284520⟩,⟨-555939590927,-433452099679⟩,⟨417936813986,562766030721⟩,⟨4218575096967,8354582364722⟩,⟨-5505996596074,-67007339746⟩,⟨-4464641843186,2486824355841⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379923292806,380524539973⟩,⟨2509885304,22839217837⟩,⟨-24215721186,-923309444⟩,⟨-667621223434,138640828367⟩,⟨-311026046693,660448361516⟩,⟨-671006568283,519769881063⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176998307915,3182026062909⟩,⟨-191288577958,-20955025303⟩,⟨7708707936,202817403948⟩,⟨-1160901988331,5614622573856⟩,⟨-5555932792907,2604879381593⟩,⟨-4353265848718,5645832115819⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨187023550730,200242057571⟩,⟨-1620946723193,-1253677440556⟩,⟨1208066810346,1641428183372⟩,⟨12132884553042,24725224252330⟩,⟨-16484638523224,-40696692584⟩,⟨-13188920326532,7759863166215⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨376075622986,400753974307⟩,⟨-3251981290270,-2552693267651⟩,⟨2465941598910,3288293539087⟩,⟨25426833828333,49866964340436⟩,⟨-32916726221118,-1347849516019⟩,⟨-25068934583235,14923107642929⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518073581546,526604756321⟩,⟨-30814023398,209251545210⟩,⟨-229832469680,52887776856⟩,⟨-5960393787718,2320169982358⟩,⟨-4191169329294,6566728768316⟩,⟨-7325356709929,6346541028061⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355620883531,364441019399⟩,⟨-31987635787,217221299841⟩,⟨-238586089099,54902111346⟩,⟨-6193762350176,2451695699947⟩,⟨-4398200472673,6827743430561⟩,⟨-7616338052421,6640325967340⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711241767062,728882038798⟩,⟨-63975271574,434442599682⟩,⟨-477172178198,109804222692⟩,⟨-12387524700352,4903391399894⟩,⟨-8796400945346,13655486861122⟩,⟨-15232676104842,13280651934680⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523272134566,1525289115245⟩,⟨-35030319920,32988826546⟩,⟨-37966833278,39993884332⟩,⟨-1307796670780,1381196768301⟩,⟨-1651334625092,1592322483354⟩,⟨-1968310450170,2011257202135⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨985359988321,1011136046215⟩,⟨-111971309143,624545947762⟩,⟨-687122221599,178837589950⟩,⟨-18079138881618,7743876767233⟩,⟨-13326751762647,20030048537477⟩,⟨-22470948470509,19789728432838⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67587783151,67712366885⟩,⟨13852326572,18061092506⟩,⟨-18236393106,-13413610514⟩,⟨-409643405276,-242906614272⟩,⟨112847483476,313827327142⟩,⟨-211845625931,34581377868⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50013041507,50729790756⟩,⟨260606525146,268814161567⟩,⟨33007811503,38126008191⟩,⟨-1395022728590,-1186090563560⟩,⟨-291407900378,-100909480074⟩,⟨-273066711780,-75733633510⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135618327560,2138441353977⟩,⟨-409378003888,-313773567912⟩,⟨303836067402,413351418542⟩,⟨5611893401312,9411105565701⟩,⟨-7239202025994,-2664663720934⟩,⟨-676413805319,4927587784199⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2976360591306,2982264118571⟩,⟨-856376067778,-655948165040⟩,⟨635173677030,864688036629⟩,⟨11779931281171,19769022120239⟩,⟨-15226422152966,-5617179030887⟩,⟨-1369813727251,10391569697166⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135384512571,137597121206⟩,⟨665945856375,699282159804⟩,⟨118243512438,143306596675⟩,⟨-3666707985071,-2609561851770⟩,⟨-1372071284177,-336955264726⟩,⟨-765718172508,334408251077⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8785981923304,8929572494348⟩,⟨-46122637083026,-42522606612169⟩,⟨-9452090343471,-7550196935245⟩,⟨578232087352704,718306750691679⟩,⟨94598836650377,188140916681329⟩,⟨-9080144512107,70514932229186⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7873818545099,8211839145884⟩,⟨-43324795863938,-33035709601020⟩,⟨-14272752149382,-5313921737761⟩,⟨318974679777321,732856443350886⟩,⟨-36325230559401,365476885138857⟩,⟨-193920643977649,237381288651656⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15747637090198,16423678291768⟩,⟨-86649591727876,-66071419202040⟩,⟨-28545504298764,-10627843475522⟩,⟨637949359554642,1465712886701772⟩,⟨-72650461118802,730953770277714⟩,⟨-387841287955298,474762577303312⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10952333724070,10995116277821⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨2173453475238562,2199023255588622⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9852822096294,9895604650045⟩,⟨-109951162778820,-109097176394608⟩,⟨0,0⟩,⟨2173453475238575,2199023255588602⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2411110045440,2415874025920⟩,⟨-12269843176037,-12121908488212⟩,⟨0,0⟩,⟨104571265817406,111755106875729⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7387794664258,7480417908185⟩,⟨-44908459902357,-43628708646816⟩,⟨-20356911438711,-19836519531383⟩,⟨515299708422524,539213128345361⟩,⟨283929375933836,295316467807005⟩,⟨106523671813086,110796976428301⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6288283036482,6380906280409⟩,⟨-44908459902358,-43628708646816⟩,⟨-20356911438712,-19836519531383⟩,⟨515299708422527,539213128345360⟩,⟨283929375933837,295316467807005⟩,⟨106523671813086,110796976428302⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1917352519232,1933429695104⟩,⟨-7852282341904,-7517783580233⟩,⟨-3559423248392,-3418085601139⟩,⟨32714787740219,42879897605252⟩,⟨23504647102069,28265570179011⟩,⟨6832551277550,8747037601724⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨98913096826,99342593558⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137559648303,139585832683⟩,⟨678146982540,685581228642⟩,⟨308528472389,310578125146⟩,⟨-1712309844053,-1698693120000⟩,⟨-1552473978312,-1544574258376⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4328462564672,4349303721024⟩,⟨-20122125517941,-19639692068445⟩,⟨-3559423248392,-3418085601139⟩,⟨137286053557625,154635004480981⟩,⟨23504647102069,28265570179011⟩,⟨6832551277550,8747037601724⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨752151245972,801507948614⟩,⟨-6503962580540,-5105386535302⟩,⟨4931883197820,6576587078174⟩,⟨50853667656666,99733928680872⟩,⟨-65833452442236,-2695699032038⟩,⟨-50137869166470,29846215285858⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5080613810644,5150811669638⟩,⟨-26626088098481,-24745078603747⟩,⟨1372459949428,3158501477035⟩,⟨188139721214291,254368933161853⟩,⟨-42328805340167,25569871146973⟩,⟨-43305317888920,38593252887582⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457056781476,465383882503⟩,⟨1654813155970,1894558866033⟩,⟨123467783730,285375543614⟩,⟨-35978138595629,-26732058638908⟩,⟨-2727577976097,4837078992721⟩,⟨-3912703135883,3486960700405⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38556772178,40682987940⟩,⟨-816109757021,-773396973068⟩,⟨330673852191,333275037186⟩,⟨9565615269225,10309358704577⟩,⟨-6692236630045,-6625935308195⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨495613553654,506066870443⟩,⟨838703398949,1121161892965⟩,⟨454141635921,618650580800⟩,⟨-26412523326404,-16422699934331⟩,⟨-9419814606142,-1788856315474⟩,⟨-3912703135883,3486960700405⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500409295618,501398026980⟩,⟨2510857612204,2551553037358⟩,⟨0,0⟩,⟨1957166706152,4308831445771⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225563443821,230776031786⟩,⟨1513499265459,1685661865344⟩,⟨206688761083,282116325801⟩,⟨-7331854348950,-287497454815⟩,⟨-3258529863585,621511789828⟩,⟨-1784266380574,1590119805169⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-801507948614,-752151245972⟩,⟨5105386535302,6503962580540⟩,⟨-6576587078174,-4931883197820⟩,⟨-99733928680872,-50853667656666⟩,⟨2695699032038,65833452442236⟩,⟨-29846215285858,50137869166470⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3526954616058,3597152475052⟩,⟨-15016738982639,-13135729487905⟩,⟨-10136010326566,-8349968798959⟩,⟨37552124876753,103781336824315⟩,⟨26200346134107,94099022621247⟩,⟨-23013664008308,58884906768194⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441256485433,456667770339⟩,⟨268909948645,599533345758⟩,⟨-297111475121,-28578051350⟩,⟨-19630689372520,-8477145324506⟩,⟨-12363038209665,-1844460331188⟩,⟨-9798953335567,1663082178690⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨323224139200,327276507958⟩,⟨1932735283200,1940466224334⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-327276507958,-323224139200⟩,⟨-1940466224334,-1932735283200⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨772235119818,776287488576⟩,⟨-1940466224334,-1932735283200⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1346640558424,1365058126204⟩,⟨-8956143173474,-8650414536622⟩,⟨-4059801066687,-3933055142643⟩,⟨49406734601092,57990569402297⟩,⟨32359754218002,36386833501792⟩,⟨10262395889384,11870742539017⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1365058126204,-1346640558424⟩,⟨8650414536622,8956143173474⟩,⟨3933055142643,4059801066687⟩,⟨-57990569402297,-49406734601092⟩,⟨-36386833501792,-32359754218002⟩,⟨-11870742539017,-10262395889384⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-265546498428,-247128930648⟩,⟨8650414536622,8956143173474⟩,⟨3933055142643,4059801066687⟩,⟨-57990569402297,-49406734601092⟩,⟨-36386833501792,-32359754218002⟩,⟨-11870742539017,-10262395889384⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12966137620,-11514897406⟩,⟨432120392278,469467699704⟩,⟨77040909519,99477436447⟩,⟨-5000636696529,-4336290824584⟩,⟨1435598287046,1877769606818⟩,⟨2563745314218,2769667636216⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428290347813,445152872933⟩,⟨701030340923,1069001045462⟩,⟨-220070565602,70899385097⟩,⟨-24631326069049,-12813436149090⟩,⟨-10927439922619,33309275630⟩,⟨-7235208021349,4432749814906⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99342593558,-98913096826⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4608825681,4850712577⟩,⟨28915336345,31319656500⟩,⟨39526600801,39737037424⟩,⟨-320404560286,-309106447477⟩,⟨251814268106,252930624064⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10106656097,10658105132⟩,⟨9277369205,18004885985⟩,⟨86677559241,87311197222⟩,⟨-964683628584,-822379552405⟩,⟨108761645553,119972071186⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1467590022053,1485883506179⟩,⟨-7570479444742,-7256042492018⟩,⟨-1424985526426,-1352643337976⟩,⟨104864327204492,112453968354750⟩,⟨22045913668724,23883290969157⟩,⟨4902375419729,5356774759984⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13490014356,14403397129⟩,⟨-61001256969,-42365320928⟩,⟨101881119485,105559199091⟩,⟨-587707326308,-130061178919⟩,⟨-276683160528,-189784147350⟩,⟨-181251163893,-161339428412⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14403397129,-13490014356⟩,⟨42365320928,61001256969⟩,⟨-105559199091,-101881119485⟩,⟨130061178919,587707326308⟩,⟨189784147350,276683160528⟩,⟨161339428412,181251163893⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113745990687,-112403111182⟩,⟨-837243981294,-817749051791⟩,⟨-105559199091,-101881119485⟩,⟨2329084434471,2786730581860⟩,⟨189784147350,276683160528⟩,⟨161339428412,181251163893⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨89338457840,94405746835⟩,⟨-617538475883,-575727555012⟩,⟨592392078556,614107218409⟩,⟨3292189385897,3995469630015⟩,⟨-3577258648482,-3110350614174⟩,⟨-2529177948743,-2304696656117⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨119245877896,127580226136⟩,⟨-1484556379753,-1358035352872⟩,⟨668352987104,720000313811⟩,⟨20513660978680,23558848593701⟩,⟨-6563071771177,-5209984291849⟩,⟨-4611393646239,-4073835854422⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-127580226136,-119245877896⟩,⟨1358035352872,1484556379753⟩,⟨-720000313811,-668352987104⟩,⟨-23558848593701,-20513660978680⟩,⟨5209984291849,6563071771177⟩,⟨4073835854422,4611393646239⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨971931401640,980265749880⟩,⟨1358035352872,1484556379753⟩,⟨-720000313811,-668352987104⟩,⟨-23558848593701,-20513660978680⟩,⟨5209984291849,6563071771177⟩,⟨4073835854422,4611393646239⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121598115387,124447261395⟩,⟨769362680131,799695804409⟩,⟨181322927600,193277352896⟩,⟨-2842266474407,-2216708891020⟩,⟨-800154874526,-525032383047⟩,⟨-210764134552,-100068983617⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11490973887,11767179238⟩,⟨167197026870,173228083622⟩,⟨20830620634,21840488766⟩,⟨639800566011,798865853674⟩,⟨94299300422,121956828472⟩,⟨-18620686558,-12718936334⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164578238205,175769279128⟩,⟨1467321294464,1897039841225⟩,⟨-7155005202,215165427450⟩,⟨-11472619815125,7524915713441⟩,⟨-5645463058696,6776637061708⟩,⟨-5562936756890,4496136168992⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-175769279128,-164578238205⟩,⟨-1897039841225,-1467321294464⟩,⟨-215165427450,7155005202⟩,⟨-7524915713441,11472619815125⟩,⟨-6776637061708,5645463058696⟩,⟨-4496136168992,5562936756890⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49794164693,66197793581⟩,⟨-383540575766,218340570880⟩,⟨-8476666367,289271331003⟩,⟨-14856770062391,11185122360310⟩,⟨-10035166925293,6266974848524⟩,⟨-6280402549566,7153056562059⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27461075339344,28880119600344⟩,⟨-269659951986684,-222889438737568⟩,⟨-103363661772874,-67488230389938⟩,⟨2484535504936443,4455516847169209⟩,⟨486955911948228,2191920691222946⟩,⟨-518060521873347,1150319494568280⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13447881124,14085454376⟩,⟨170172010170,181025739600⟩,⟨40106035652,43751856098⟩,⟨433295380723,672963789985⟩,⟨72624990426,165018973172⟩,⟨12094432763,45816587456⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨335870278559,369972992307⟩,⟨795647284741,2028768298670⟩,⟨-322478877421,323766596280⟩,⟨-47585025899767,5760890728652⟩,⟨-19978616532898,13839005049550⟩,⟨-14560733531528,11016336917016⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-369972992307,-335870278559⟩,⟨-2028768298670,-795647284741⟩,⟨-323766596280,322478877421⟩,⟨-5760890728652,47585025899767⟩,⟨-13839005049550,19978616532898⟩,⟨-11016336917016,14560733531528⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58317355506,109282594374⟩,⟨-1327737957747,273353760721⟩,⟨-543837161882,393378262518⟩,⟨-30392216797701,34771589750677⟩,⟨-24766444972169,20011925808528⟩,⟨-18251544938365,18993483346434⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236472745129,238928426241⟩,⟨1556897291300,1565190530864⟩,⟨308528472389,310578125146⟩,⟨-3911333099605,-3897716375552⟩,⟨-1552473978312,-1544574258376⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1699052116257,-1609881476454⟩,⟨-5751637874686,-2748103401923⟩,⟨-490279175942,1493890313333⟩,⟨-19992246169033,108370452001772⟩,⟨-58873474508565,41704031048165⟩,⟨-44834516072581,48311161186974⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192305726920,-178041367265⟩,⟨-1886747150715,-1430404992770⟩,⟨-354159234329,-96404495780⟩,⟨-7383699136208,12812041349122⟩,⟨-7262440982796,6590035761848⟩,⟨-5100403778419,6318952076918⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44167018209,60887058976⟩,⟨-329849859415,134785538094⟩,⟨-45630761940,214173629366⟩,⟨-11295032235813,8914324973570⟩,⟨-8814914961108,5045461503472⟩,⟨-5452247499309,5967795215254⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2641048926,6579527167⟩,⟨-118059353941,38158977868⟩,⟨-33585067537,52435184037⟩,⟨-3833776825403,4131492889689⟩,⟨-2975053703393,2089358193685⟩,⟨-2009240859505,2061476494356⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1774174504,3371709637⟩,⟨-36531833474,14927891256⟩,⟨-5053739904,23720353788⟩,⟨-1331828179301,1185195215211⟩,⟨-1104780292086,611309260426⟩,⟨-621629116610,744388385547⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3093844456,5928962797⟩,⟨-88318618237,14119148806⟩,⟨-19801875597,36195484488⟩,⟨-2502375029643,2737385083843⟩,⟨-2122494403059,1315986466900⟩,⟨-1235653701395,1368509291657⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5928962797,-3093844456⟩,⟨-14119148806,88318618237⟩,⟨-36195484488,19801875597⟩,⟨-2737385083843,2502375029643⟩,⟨-1315986466900,2122494403059⟩,⟨-1368509291657,1235653701395⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3287913871,3485682711⟩,⟨-132178502747,126477596105⟩,⟨-69780552025,72237059634⟩,⟨-6571161909246,6633867919332⟩,⟨-4291040170293,4211852596744⟩,⟨-3377750151162,3297130195751⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49794164693,66197793581⟩,⟨-383540575766,218340570880⟩,⟨-8476666367,289271331003⟩,⟨-14856770062391,11185122360310⟩,⟨-10035166925293,6266974848524⟩,⟨-6280402549566,7153056562059⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3287913871,3485682711⟩,⟨-132178502747,126477596105⟩,⟨-69780552025,72237059634⟩,⟨-6571161909246,6633867919332⟩,⟨-4291040170293,4211852596744⟩,⟨-3377750151162,3297130195751⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (513/5120) u, BivariateJet2.affineZ (611/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000017

end


