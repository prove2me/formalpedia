-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000026_000029_data
-- name    : GeneralCK_RB2_cells000026_000029_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T01:58:51.874434+00:00
-- url     : https://prove2.me/theorems/91cac634-3593-4b10-897d-5b714ed3e2fd
-- title:
--   Exact certificate data for RB2 cells 000026–000029
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000026 through 000029. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000026Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2104109631232,-2104109592384⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2104109631168,-2104109592384⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-175510017280,-175510017216⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-175510017280,-175510017216⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨89992660992,89992661056⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-98020290368,-98020290304⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨89992784320,89992784384⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-98020436736,-98020436672⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8027652352,-8027652288⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8027629312,-8027629248⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨188012951296,188012951360⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨188013220992,188013221056⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1928599575168,1928599613760⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1928599575168,1928599613760⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2518909148928,-2518909091072⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2110974691968,-2110974653056⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2097282082752,-2097282043968⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-176695986368,-176695986304⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-174326210688,-174326210624⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨87413718912,87413718976⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-94968234880,-94968234816⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨92593776192,92593776256⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-101114482624,-101114482560⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8520706368,-8520706304⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7554515968,-7554515904⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨182381953728,182381953792⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨193708258752,193708258816⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1920586057600,1920586096192⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1936648442432,1936648481024⟩



end LaneCBRB2Cell000026Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000026
open Set LaneCBRB2Cell000026Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111454401331,111454401332⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨127345780326,127345780327⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111454401332,-111454401331⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438301412556,438301412557⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50764206571,50764206572⟩,⟨-127345780327,-127345780326⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨162218607902,162218607904⟩,⟨972165847449,972165847450⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨50764206570,50764206573⟩,⟨-127345780327,-127345780326⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2104109631232,-2104109592384⟩,⟨6589303577487,6589303577577⟩,⟨2970790501797,2970790501841⟩,⟨-39489279185966,-39489279184896⟩,⟨-25256207893912,-25256207893313⟩,⟨-8026832989189,-8026832988950⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310433947794,-310433942058⟩,⟨-888245148774,-888245114395⟩,⟨-400465727557,-400465712055⟩,⟨5826128377822,5826128378226⟩,⟨3631310582024,3631310621092⟩,⟨1184254573041,1184254573134⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨310433942058,310433947794⟩,⟨888245114395,888245148774⟩,⟨400465712055,400465727557⟩,⟨-5826128378226,-5826128377822⟩,⟨-3631310621092,-3631310582024⟩,⟨-1184254573134,-1184254573041⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162218607904,-162218607902⟩,⟨-972165847450,-972165847449⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937293019872,937293019874⟩,⟨-972165847450,-972165847449⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175510017280,-175510017216⟩,⟨-1140419944176,-1140419944170⟩,⟨-514158848258,-514158848254⟩,⟨-1182850291184,-1182850291171⟩,⟨756517046576,756517046587⟩,⟨-240433402034,-240433402030⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149615802106,-149615802051⟩,⟨-816983455278,-816983455213⟩,⟨-368337360775,-368337360743⟩,⟨1008336149843,1008336149871⟩,⟨1378610420261,1378610420347⟩,⟨204960587747,204960587757⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149615802051,149615802106⟩,⟨816983455213,816983455278⟩,⟨368337360743,368337360775⟩,⟨-1008336149871,-1008336149843⟩,⟨-1378610420347,-1378610420261⟩,⟨-204960587757,-204960587747⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨460049744109,460049749900⟩,⟨1705228569608,1705228604052⟩,⟨768803072798,768803088332⟩,⟨-6834464528097,-6834464527665⟩,⟨-5009921041439,-5009921002285⟩,⟨-1389215160891,-1389215160788⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨820773833762,820773845479⟩,⟨4104500450428,4104500542816⟩,⟨768803072798,768803088332⟩,⟨-18904822700090,-18904822699152⟩,⟨-5009921041439,-5009921002285⟩,⟨-1389215160891,-1389215160788⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨101528413140,101528413146⟩,⟨-254691560654,-254691560652⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11907265977615,11907265978319⟩,⟨29870260560224,29870260563992⟩,⟨-102808097488781,-102808097476388⟩,⟨149863531664289,149863531693227⟩,⟨-257901743871404,-257901743744185⟩,⟨1775303403247196,1775303403570199⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8888648468265,8888648595682⟩,⟨66747913337141,66747914661421⟩,⟨-68419335411849,-68419334138297⟩,⟨130152610936382,130152617625190⟩,⟨-609675237036272,-609675224656227⟩,⟨1166429192601080,1166429214685110⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨93778081792,93778215680⟩,⟨-696843505222,-696841473439⟩,⟨714290937783,714293019568⟩,⟨8942870408087,8942920464373⟩,⟨-4194715568076,-4194649814978⟩,⟨-1353401128438,-1353317273516⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1193289709568,1193289843456⟩,⟨-696843505222,-696841473439⟩,⟨714290937783,714293019568⟩,⟨8942870408087,8942920464373⟩,⟨-4194715568076,-4194649814978⟩,⟨-1353401128438,-1353317273516⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨89992660992,89992784384⟩,⟨-642080067053,-642078122900⟩,⟨658156269421,658158261450⟩,⟨7865113975525,7865163293192⟩,⟨-3480720545845,-3480657199448⟩,⟨-1641008142439,-1640928352762⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨97668195211,97668340086⟩,⟨-753878803167,-753876370508⟩,⟨772754034006,772756526633⟩,⟨10081753868645,10081818288309⟩,⟨-4955171997369,-4955092014356⟩,⟨-1036609835459,-1036510944913⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-93778215680,-93778081792⟩,⟨696841473439,696843505222⟩,⟨-714293019568,-714290937783⟩,⟨-8942920464373,-8942870408087⟩,⟨4194649814978,4194715568076⟩,⟨1353317273516,1353401128438⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1005733412096,1005733545984⟩,⟨696841473439,696843505222⟩,⟨-714293019568,-714290937783⟩,⟨-8942920464373,-8942870408087⟩,⟨4194649814978,4194715568076⟩,⟨1353317273516,1353401128438⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-98020436736,-98020290304⟩,⟨761817387738,761819710390⟩,⟨-780896280475,-780893900619⟩,⟨-10304633444164,-10304574200319⟩,⟨5126830583417,5126906376583⟩,⟨924896306390,924991557653⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-89660208157,-89660062278⟩,⟨634718431724,634720922980⟩,⟨-650614838492,-650612285806⟩,⟨-7662857459208,-7662790600442⟩,⟨3325778344632,3325860620725⟩,⟨1739962519000,1740063463842⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8007987054,8008277808⟩,⟨-119160371443,-119155447528⟩,⟨122139195514,122144240827⟩,⟨2418896409437,2419027687867⟩,⟨-1629393652737,-1629231393631⟩,⟨703352683541,703552518929⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4003993527,4004138904⟩,⟨-59580185722,-59577723764⟩,⟨61069597757,61072120414⟩,⟨1209448204718,1209513843934⟩,⟨-814696826369,-814615696815⟩,⟨351676341770,351776259465⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4004138904,-4003993527⟩,⟨59577723764,59580185722⟩,⟨-61072120414,-61069597757⟩,⟨-1209513843934,-1209448204718⟩,⟨814615696815,814696826369⟩,⟨-351776259465,-351676341770⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758119244712,758119409353⟩,⟨59577723764,59580185722⟩,⟨-61072120414,-61069597757⟩,⟨-1209513843934,-1209448204718⟩,⟨814615696815,814696826369⟩,⟨-351776259465,-351676341770⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7998395289,7998418129⟩,⟨-118868666556,-118868150260⟩,⟨121844703220,121845232294⟩,⟨2408766289025,2408782156432⟩,⟨-1620944008704,-1620926492226⟩,⟨697204088053,697224131432⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7998418129,-7998395289⟩,⟨118868150260,118868666556⟩,⟨-121845232294,-121844703220⟩,⟨-2408782156432,-2408766289025⟩,⟨1620926492226,1620944008704⟩,⟨-697224131432,-697204088053⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091513209647,1091513232487⟩,⟨118868150260,118868666556⟩,⟨-121845232294,-121844703220⟩,⟨-2408782156432,-2408766289025⟩,⟨1620926492226,1620944008704⟩,⟨-697224131432,-697204088053⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8027652352,-8027629248⟩,⟨119739192794,119739715380⟩,⟨-122738092872,-122737557352⟩,⟨-2439473262023,-2439457113744⟩,⟨1646170709526,1646188505186⟩,⟨-716034477830,-716014153318⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4013826176,-4013814624⟩,⟨59869596397,59869857690⟩,⟨-61369046436,-61368778676⟩,⟨-1219736631012,-1219728556872⟩,⟨823085354763,823094252593⟩,⟨-358017238915,-358007076659⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4013814624,4013826176⟩,⟨-59869857690,-59869596397⟩,⟨61368778676,61369046436⟩,⟨1219728556872,1219736631012⟩,⟨-823094252593,-823085354763⟩,⟨358007076659,358017238915⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766137198240,766137229056⟩,⟨-59869857690,-59869596397⟩,⟨61368778676,61369046436⟩,⟨1219728556872,1219736631012⟩,⟨-823094252593,-823085354763⟩,⟨358007076659,358017238915⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272878302411,272878308122⟩,⟨29717037565,29717166639⟩,⟨-30461308074,-30461175805⟩,⟨-602195539108,-602191572256⟩,⟨405231623056,405236002176⟩,⟨-174306032858,-174301022013⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532274396480,1532274458112⟩,⟨-119739715380,-119739192794⟩,⟨122737557352,122738092872⟩,⟨2439457113744,2439473262024⟩,⟨-1646188505186,-1646170709526⟩,⟨716014153318,716034477830⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1202033902957,1202034062979⟩,⟨-832854531598,-832851881499⟩,⟨853707154561,853709869975⟩,⟨11842465563905,11842535427116⟩,⟨-6196468446671,-6196381155281⟩,⟨-404922265357,-404814060114⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1304556178138,1304556498182⟩,⟨-1665709063196,-1665703762998⟩,⟨1707414309123,1707419739950⟩,⟨23684931127820,23685070854220⟩,⟨-12392936893336,-12392762310566⟩,⟨-809844383049,-809628267894⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨188012951296,188013221056⟩,⟨-1403900049818,-1403895238264⟩,⟨1439049890845,1439054821120⟩,⟨18169674981967,18169809931252⟩,⟨-8607638501472,-8607476203845⟩,⟨-2566009789695,-2565814569589⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨64660497208,64660603568⟩,⟨-475396065612,-475394343102⟩,⟨487298595340,487300360299⟩,⟨5987476450435,5987521390175⟩,⟨-2745392098194,-2745335690302⟩,⟨-1042531396384,-1042461301494⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380281959350,380281982606⟩,⟨11696360936,11696672798⟩,⟨-11989566730,-11989247147⟩,⟨-240261740613,-240252101933⟩,⟨162810192443,162820800749⟩,⟨-72011499563,-71999399612⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179024710374,3179024904787⟩,⟨-97780116080,-97777497062⟩,⟨100225923610,100228607472⟩,⟨2014438457768,2014519601283⟩,⟨-1367290901575,-1367201723492⟩,⟨608209559787,608311122865⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨186953292003,186953610957⟩,⟨-1380265942809,-1380260714966⟩,⟨1414823540443,1414828897174⟩,⟨17514645077389,17514783608558⟩,⟨-8104849512132,-8104677922397⟩,⟨-2889670428888,-2889458846428⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨374966243299,374966832013⟩,⟨-2784165992627,-2784155953230⟩,⟨2853873431288,2853883718294⟩,⟨35684320059356,35684593539810⟩,⟨-16712488013604,-16712154126242⟩,⟨-5455680218583,-5455273416017⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522727340651,522727567694⟩,⟨82158328844,82161741756⟩,⟨-84219136364,-84215639300⟩,⟨-1661476591470,-1661385178427⟩,⟨1116745167604,1116857837012⟩,⟨-478319478644,-478181025233⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360423343122,360423577943⟩,⟨84972921571,84976469859⟩,⟨-87104347472,-87100711688⟩,⟨-1711718386533,-1711622914340⟩,⟨1148157313105,1148274661313⟩,⟨-487689611584,-487545725366⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720846686244,720847155886⟩,⟨169945843142,169952939718⟩,⟨-174208694944,-174201423376⟩,⟨-3423436773066,-3423245828680⟩,⟨2296314626210,2296549322626⟩,⟨-975379223168,-975091450732⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524275978351,1524276062823⟩,⟨-871565120,-870526238⟩,⟨892325058,893389652⟩,⟨30674957312,30706972999⟩,⟨-25262012960,-25226700822⟩,⟨18790021886,18830389777⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨999324845830,999325552286⟩,⟨235028074787,235038607448⟩,⟨-240924158860,-240913366412⟩,⟨-4726141045971,-4725854737558⟩,⟨3167142919770,3167491963086⟩,⟨-1340152948189,-1339727105660⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67723311009,67723313845⟩,⟨14750430206,14750494584⟩,⟨-15119858674,-15119792702⟩,⟨-297301080627,-297299091416⟩,⟨199495286532,199497478678⟩,⟨-84831212209,-84828708540⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50554737401,50554740241⟩,⟨263823610739,263823675234⟩,⟨36066835542,36066887892⟩,⟨-1276228337944,-1276226317900⟩,⟨-205788852284,-205786905638⟩,⟨-170037203761,-170035237616⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135370619824,2135370791605⟩,⟨-333737457366,-333735987392⟩,⟨342093001776,342094508134⟩,⟨6825312359052,6825357868523⟩,⟨-4614974794170,-4614924776404⟩,⟨2023070306005,2023127273695⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2975842769730,2975843128820⟩,⟨-697642528808,-697639427924⟩,⟨715108873695,715112051341⟩,⟨14322103179652,14322199364282⟩,⟨-9702994658676,-9702889223887⟩,⟨4286293676517,4286413433652⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136827065735,136827089933⟩,⟨681965000400,681965405498⟩,⟨130495548634,130495850054⟩,⟨-3130402907937,-3130390994427⟩,⟨-854403794014,-854392645956⟩,⟨-216212506470,-216201335554⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8835427401157,8835428963712⟩,⟨-44037024865074,-44036983130420⟩,⟨-8426598984769,-8426576540467⟩,⟨641113575153514,641115170362931⟩,⟨139169697698981,139170725567212⟩,⟨30034203488811,30035012554495⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8030349022650,8030356119749⟩,⟨-38135795605111,-38135644406600⟩,⟨-9594790731715,-9594677850216⟩,⟨525890244866572,525895275614514⟩,⟨159786686522813,159791046403768⟩,⟨20221022569087,20225376351327⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16060698045300,16060712239498⟩,⟨-76271591210222,-76271288813200⟩,⟨-19189581463430,-19189355700432⟩,⟨1051780489733144,1051790551229028⟩,⟨319573373045626,319582092807536⟩,⟨40442045138174,40450752702654⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10846819911700,10846819911799⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738054,2111240126795878⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9747308283924,9747308284023⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738069,2111240126795861⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2399271880896,2399271938752⟩,⟨-12070358171930,-12070358171514⟩,⟨0,0⟩,⟨105643681588589,105643681622780⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7452448490558,7452448490651⟩,⟨-44662052006198,-44662052005035⟩,⟨-20135906371693,-20135906371143⟩,⟨535313700410748,535313700431908⟩,⟨291858840027157,291858840038262⟩,⟨108811144659683,108811144664258⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6352936862782,6352936862875⟩,⟨-44662052006198,-44662052005035⟩,⟨-20135906371693,-20135906371143⟩,⟨535313700410749,535313700431901⟩,⟨291858840027156,291858840038259⟩,⟨108811144659682,108811144664257⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1928599575168,1928599613760⟩,⟨-7729723521892,-7729723521527⟩,⟨-3484949350162,-3484949349992⟩,⟨38306428887534,38306428900977⟩,⟨26012724936926,26012724943474⟩,⟨7786399585636,7786399588446⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100156582133,100156582135⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138285366920,138285366923⟩,⟨685305051361,685305051368⟩,⟨308970092738,308970092743⟩,⟨-1719138590394,-1719138590390⟩,⟨-1550148823944,-1550148823936⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4327871456064,4327871552512⟩,⟨-19800081693822,-19800081693041⟩,⟨-3484949350162,-3484949349992⟩,⟨143950110476123,143950110523757⟩,⟨26012724936926,26012724943474⟩,⟨7786399585636,7786399588446⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨749932486598,749933664026⟩,⟨-5568331985254,-5568311906460⟩,⟨5707746862576,5707767436588⟩,⟨71368640118712,71369187079620⟩,⟨-33424976027208,-33424308252484⟩,⟨-10911360437166,-10910546832034⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5077803942662,5077805216538⟩,⟨-25368413679076,-25368393599501⟩,⟨2222797512414,2222818086596⟩,⟨215318750594835,215319297603377⟩,⟨-7412251090282,-7411583309010⟩,⟨-3124960851530,-3124147243588⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨462546711458,462546827508⟩,⟨1737502019040,1737504863801⟩,⟨202478806038,202480680184⟩,⟨-30992548844626,-30992464450842⟩,⟨1096964155207,1097041387767⟩,⟨-284658561391,-284584448307⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37551974190,37551976323⟩,⟨-760054387465,-760054376721⟩,⟨324226151534,324226169925⟩,⟨9458522760093,9458522788713⟩,⟨-6562358286202,-6562358193788⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨500098685648,500098803831⟩,⟨977447631575,977450487080⟩,⟨526704957572,526706850109⟩,⟨-21534026084533,-21533941662129⟩,⟨-5465394130995,-5465316806021⟩,⟨-284658561391,-284584448307⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503871945521,503871957673⟩,⟨2534900173993,2534900296365⟩,⟨0,0⟩,⟨3319096918590,3319099843609⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229179656971,229179716659⟩,⟨1600900473048,1600902120570⟩,⟨241372483003,241373356116⟩,⟨-3851756928793,-3851702931282⟩,⟨-1290313186153,-1290273268295⟩,⟨-130450158938,-130416192072⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-749933664026,-749932486598⟩,⟨5568311906460,5568331985254⟩,⟨-5707767436588,-5707746862576⟩,⟨-71369187079620,-71368640118712⟩,⟨33424308252484,33424976027208⟩,⟨10910546832034,10911360437166⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3577937792038,3577939065914⟩,⟨-14231769787362,-14231749707787⟩,⟨-9192716786750,-9192696212568⟩,⟨72580923396503,72581470405045⟩,⟨59437033189410,59437700970682⟩,⟨18696946417670,18697760025612⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449996551095,449996711321⟩,⟨440134804493,440138123944⟩,⟨-150741873276,-150738927654⟩,⟨-14206580953566,-14206485133797⟩,⟨-7297851491595,-7297747242583⟩,⟨-3952045088273,-3951930792991⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨324437215804,324437215808⟩,⟨1944331694898,1944331694900⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-324437215808,-324437215804⟩,⟨-1944331694900,-1944331694898⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨775074411968,775074411972⟩,⟨-1944331694900,-1944331694898⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1359520121373,1359520148585⟩,⟨-8859340841121,-8859340772586⟩,⟨-3994237830071,-3994237799165⟩,⟨54341058526920,54341058537857⟩,⟨34519532849320,34519532931829⟩,⟨11045696711639,11045696713934⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1359520148585,-1359520121373⟩,⟨8859340772586,8859340841121⟩,⟨3994237799165,3994237830071⟩,⟨-54341058537857,-54341058526920⟩,⟨-34519532931829,-34519532849320⟩,⟨-11045696713934,-11045696711639⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-260008520809,-260008493597⟩,⟨8859340772586,8859340841121⟩,⟨3994237799165,3994237830071⟩,⟨-54341058537857,-54341058526920⟩,⟨-34519532931829,-34519532849320⟩,⟨-11045696713934,-11045696711639⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12004535403,-12004534145⟩,⟨439148052065,439148058407⟩,⟨80765140208,80765152496⟩,⟨-4561097799708,-4561097783162⟩,⟨1735259414210,1735259476239⟩,⟨2674491142159,2674491166944⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437992015692,437992177176⟩,⟨879282856558,879286182351⟩,⟨-69976733068,-69973775158⟩,⟨-18767678753274,-18767582916959⟩,⟨-5562592077385,-5562487766344⟩,⟨-1277553946114,-1277439626047⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100156582135,-100156582133⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4624207053,4624207055⟩,⟨28872390236,28872390241⟩,⟨39925700025,39925700027⟩,⟨-304585239434,-304585239425⟩,⟨249286067484,249286067488⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10090598110,10090598359⟩,⟨12238959800,12238961355⟩,⟨87122870713,87122872820⟩,⟨-854256307688,-854256291171⟩,⟨105671963339,105671976504⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1472909774444,1472909795472⟩,⟨-7365682001981,-7365681625871⟩,⟨-1379646320356,-1379646253085⟩,⟨107593566396248,107593573838216⟩,⟨22789077711134,22789079218501⟩,⟨5077575472921,5077575759436⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13517401918,13517402445⟩,⟨-51202055333,-51202047894⟩,⟨104048623100,104048628521⟩,⟨-320920335492,-320920175155⟩,⟨-248295802633,-248295717362⟩,⟨-172041589704,-172041569975⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13517402445,-13517401918⟩,⟨51202047894,51202055333⟩,⟨-104048628521,-104048623100⟩,⟨320920175155,320920335492⟩,⟨248295717362,248295802633⟩,⟨172041569975,172041589704⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113673984580,-113673984051⟩,⟨-825400777220,-825400769779⟩,⟨-104048628521,-104048623100⟩,⟨2519943430707,2519943591044⟩,⟨248295717362,248295802633⟩,⟨172041569975,172041589704⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨89043012144,89043013932⟩,⟨-580250620598,-580250616086⟩,⟨607903738767,607903754171⟩,⟨3559117263750,3559117264575⟩,⟨-3405291411088,-3405291371945⟩,⟨-2418933989912,-2418933989617⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨119282342832,119282346931⟩,⟨-1373809343959,-1373809284378⟩,⟨702620575089,702620615044⟩,⟨21255433646743,21255434950991⟩,⟨-6060476248556,-6060475619557⟩,⟨-4354781875910,-4354781684746⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-119282346931,-119282342832⟩,⟨1373809284378,1373809343959⟩,⟨-702620615044,-702620575089⟩,⟨-21255434950991,-21255433646743⟩,⟨6060475619557,6060476248556⟩,⟨4354781684746,4354781875910⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨980229280845,980229284944⟩,⟨1373809284378,1373809343959⟩,⟨-702620615044,-702620575089⟩,⟨-21255434950991,-21255433646743⟩,⟨6060475619557,6060476248556⟩,⟨4354781684746,4354781875910⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123283248983,123283249502⟩,⟨783742324186,783742334246⟩,⟨187082498312,187082504497⟩,⟨-2493387663077,-2493387418279⟩,⟨-671634236987,-671634110415⟩,⟨-158714873236,-158714825412⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11752285581,11752285692⟩,⟨170669580146,170669582480⟩,⟨21514318218,21514319442⟩,⟨718199593103,718199651027⟩,⟨104877545454,104877572876⟩,⟨-15880754375,-15880748076⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171667043158,171667196497⟩,⟨1677751299354,1677756776630⟩,⟨109151665020,109154375678⟩,⟨-1945290722613,-1945078753162⟩,⟨476679724130,476815799604⟩,⟨-550672969753,-550570718803⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171667196497,-171667043158⟩,⟨-1677756776630,-1677751299354⟩,⟨-109154375678,-109151665020⟩,⟨1945078753162,1945290722613⟩,⟨-476815799604,-476679724130⟩,⟨550570718803,550672969753⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57512460474,57512673501⟩,⟨-76856303582,-76849178784⟩,⟨132218107325,132221691096⟩,⟨-1906678175631,-1906412208669⟩,⟨-1767128985757,-1766952992425⟩,⟨420120559865,420256777681⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28171285000159,28171310461227⟩,⟨-246693367921473,-246692735032002⟩,⟨-84564624631426,-84564182966447⟩,⟨3476819386868477,3476841818717432⟩,⟨1317168048018540,1317186235676308⟩,⟨306317259880713,306334066510445⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13823191220,13823191337⟩,⟨175754940012,175754943008⟩,⟨41953423022,41953424588⟩,⟨558173446457,558173532393⟩,⟨116093762388,116093803648⟩,⟨28072419550,28072434636⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354172752368,354173075466⟩,⟨1401670377996,1401682507678⟩,⟨11758720631,11765293924⟩,⟨-20854672745586,-20854171555578⟩,⟨-3396331636794,-3396003763803⟩,⟨-1883047857947,-1882801548210⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354173075466,-354172752368⟩,⟨-1401682507678,-1401670377996⟩,⟨-11765293924,-11758720631⟩,⟨20854171555578,20854672745586⟩,⟨3396003763803,3396331636794⟩,⟨1882801548210,1883047857947⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83818940226,83819424808⟩,⟨-522399651120,-522384195645⟩,⟨-81742026992,-81732495789⟩,⟨2086492802304,2087089828627⟩,⟨-2166588313582,-2166156129550⟩,⟨605247602096,605608231900⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238441949053,238441949058⟩,⟨1561907876473,1561907876482⟩,⟨308970092738,308970092743⟩,⟨-3918161845946,-3918161845942⟩,⟨-1550148823944,-1550148823936⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1660450975994,-1660449500786⟩,⟨-4171363886679,-4171321822155⟩,⟨464056422286,464081194635⟩,⟨42582167795377,42583698441280⟩,⟨-7790309425747,-7789204718726⟩,⟨1962836490973,1963782176754⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186178833210,-186178667017⟩,⟨-1651301334853,-1651295549643⟩,⟨-230494100592,-230491062411⟩,⟨2593208545867,2593443949715⟩,⟨-238186368203,-238036563486⟩,⟨617689222171,617803979003⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52263115843,52263282041⟩,⟨-89393458380,-89387673161⟩,⟨78475992146,78479030332⟩,⟨-1324953300079,-1324717896227⟩,⟨-1788335192147,-1788185387422⟩,⟨268246572550,268361329384⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4384340615,4384382203⟩,⟨-33184416436,-33182929770⟩,⟨5803648604,5804494470⟩,⟨36809305798,36870985489⟩,⟨-305151399114,-305109420548⟩,⟨44026092656,44058468201⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2484224094,2484239895⟩,⟨-8498310360,-8497733356⟩,⟨7460402900,7460715454⟩,⟨-111424473108,-111399812282⟩,⟨-182771652298,-182755550464⟩,⟨36703355433,36715213445⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4357455993,4357483797⟩,⟨-32371031583,-32369908104⟩,⟨5212022784,5212621365⟩,⟨10585442032,10637365671⟩,⟨-287333930274,-287301280432⟩,⟨34677947227,34700841291⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4357483797,-4357455993⟩,⟨32369908104,32371031583⟩,⟨-5212621365,-5212022784⟩,⟨-10637365671,-10585442032⟩,⟨287301280432,287333930274⟩,⟨-34700841291,-34677947227⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨26856818,26926210⟩,⟨-814508332,-811898187⟩,⟨591027239,592471686⟩,⟨26171940127,26285543457⟩,⟨-17850118682,-17775490274⟩,⟨9325251365,9380520974⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57512460474,57512673501⟩,⟨-76856303582,-76849178784⟩,⟨132218107325,132221691096⟩,⟨-1906678175631,-1906412208669⟩,⟨-1767128985757,-1766952992425⟩,⟨420120559865,420256777681⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨26856818,26926210⟩,⟨-814508332,-811898187⟩,⟨591027239,592471686⟩,⟨26171940127,26285543457⟩,⟨-17850118682,-17775490274⟩,⟨9325251365,9380520974⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111239652966,111669149696⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨125413045043,129278515610⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111669149696,-111239652966⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438086664192,438516160922⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49969260134,51559907984⟩,⟨-129278515610,-125413045043⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161208913100,163229057680⟩,⟨970233112166,974098582733⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49539763404,51989404714⟩,⟨-129278515610,-125413045043⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2110974691968,-2097282043968⟩,⟨6535494376075,6643756214961⟩,⟨2950953635945,2990862035044⟩,⟨-40144638336483,-38846962288256⟩,⟨-25571292615464,-24946776067639⟩,⟨-8135662676674,-7919995697645⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313386781051,-307500666869⟩,⟨-911966263351,-864382325912⟩,⟨-409251233093,-391624510375⟩,⟨5574415453808,6076216285063⟩,⟨3509043251057,3752745672974⟩,⟨1143753540233,1224460699392⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307500666869,313386781051⟩,⟨864382325912,911966263351⟩,⟨391624510375,409251233093⟩,⟨-6076216285063,-5574415453808⟩,⟨-3752745672974,-3509043251057⟩,⟨-1224460699392,-1143753540233⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-163229057680,-161208913100⟩,⟨-974098582733,-970233112166⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨936282570096,938302714676⟩,⟨-974098582733,-970233112166⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-176695986368,-174326210624⟩,⟨-1143920385281,-1136927957037⟩,⟨-514965923004,-513353924824⟩,⟨-1190122791615,-1175617562231⟩,⟨752652539250,760374278143⟩,⟨-241188810702,-239681187060⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150789058973,-148446445126⟩,⟨-822371058364,-811602621736⟩,⟨-370004213826,-366672144545⟩,⟨990871607390,1025793807920⟩,⟨1370210261023,1387018260406⟩,⟨203252876527,206666701433⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148446445126,150789058973⟩,⟨811602621736,822371058364⟩,⟨366672144545,370004213826⟩,⟨-1025793807920,-990871607390⟩,⟨-1387018260406,-1370210261023⟩,⟨-206666701433,-203252876527⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨455947111995,464175840024⟩,⟨1675984947648,1734337321715⟩,⟨758296654920,779255446919⟩,⟨-7102010092983,-6565287061198⟩,⟨-5139763933380,-4879253512080⟩,⟨-1431127400825,-1347006416760⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨815727882174,825844636404⟩,⟨4068178289633,4140675709388⟩,⟨758296654920,779255446919⟩,⟨-19278074928217,-18529696608400⟩,⟨-5139763933380,-4879253512080⟩,⟨-1431127400825,-1347006416760⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨99079526808,103978809428⟩,⟨-258557031220,-250826090086⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11626655722113,12201570380502⟩,⟨28046758869390,31841106991943⟩,⟨-108005881191702,-97971554954876⟩,⟨135313318271159,166184525902084⟩,⟨-317812935895186,-201861724356423⟩,⟨1651106871947879,1912093281146316⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8625818053556,9164615634694⟩,⟨63826366025849,69866067421932⟩,⟨-73104841740379,-64037511817025⟩,⟨94000360659343,168703620903791⟩,⟨-683145904213845,-541283074632457⟩,⟨1055981163296118,1286796574164764⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨90982459904,96604389632⟩,⟨-774261671130,-627002612293⟩,⟨629076817217,810154042187⟩,⟨6714507021351,11436423484163⟩,⟨-7615475550161,-1041811391182⟩,⟨-5619405186518,3158828969192⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1190494087680,1196116017408⟩,⟨-774261671130,-627002612293⟩,⟨629076817217,810154042187⟩,⟨6714507021351,11436423484163⟩,⟨-7615475550161,-1041811391182⟩,⟨-5619405186518,3158828969192⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨87413718912,92593776256⟩,⟨-715089406289,-576362704644⟩,⟨578269386269,748238734567⟩,⟨5707136699582,10260276260114⟩,⟨-6730341419275,-471037379450⟩,⟨-5699137903588,2613287333077⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨94647035027,100729174749⟩,⟨-843121328837,-673903762022⟩,⟨676133121954,882205820178⟩,⟨7370558133253,13131971220408⟩,⟨-9016803196079,-1252363886139⟩,⟨-6011396497721,4211560745397⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-96604389632,-90982459904⟩,⟨627002612293,774261671130⟩,⟨-810154042187,-629076817217⟩,⟨-11436423484163,-6714507021351⟩,⟨1041811391182,7615475550161⟩,⟨-3158828969192,5619405186518⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1002907238144,1008529167872⟩,⟨627002612293,774261671130⟩,⟨-810154042187,-629076817217⟩,⟨-11436423484163,-6714507021351⟩,⟨1041811391182,7615475550161⟩,⟨-3158828969192,5619405186518⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-101114482624,-94968234816⟩,⟨683566410197,848841924728⟩,⟨-888191605161,-685827735407⟩,⟨-13193350157354,-7745216220276⟩,⟨1562175463462,9034730521753⟩,⟨-4180587238259,5732901109326⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-92747454820,-86624213591⟩,⟨552303965601,724445734420⟩,⟨-760360149407,-551065834895⟩,⟨-10742058044731,-4817496874515⟩,⟨-526327515788,7414945414762⟩,⟨-3566647827766,6857904173118⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1899580207,14104961158⟩,⟨-290817363236,50541972398⟩,⟨-84227027453,331139985283⟩,⟨-3371499911478,8314474345893⟩,⟨-9543130711867,6162581528623⟩,⟨-9578044325487,11069464918515⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨949790103,7052480579⟩,⟨-145408681618,25270986199⟩,⟨-42113513727,165569992642⟩,⟨-1685749955739,4157237172947⟩,⟨-4771565355934,3081290764312⟩,⟨-4789022162744,5534732459258⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7052480579,-949790103⟩,⟨-25270986199,145408681618⟩,⟨-165569992642,42113513727⟩,⟨-4157237172947,1685749955739⟩,⟨-3081290764312,4771565355934⟩,⟨-5534732459258,4789022162744⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755070903037,761173612777⟩,⟨-25270986199,145408681618⟩,⟨-165569992642,42113513727⟩,⟨-4157237172947,1685749955739⟩,⟨-3081290764312,4771565355934⟩,⟨-5534732459258,4789022162744⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7528622527,8487775719⟩,⟨-136055088944,-103766506130⟩,⟨104109779020,142362181130⟩,⟨1826328373984,3100085169794⟩,⟨-2479209051412,-889884851592⟩,⟨-267612569913,1748969801325⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8487775719,-7528622527⟩,⟨103766506130,136055088944⟩,⟨-142362181130,-104109779020⟩,⟨-3100085169794,-1826328373984⟩,⟨889884851592,2479209051412⟩,⟨-1748969801325,267612569913⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091023852057,1091983005249⟩,⟨103766506130,136055088944⟩,⟨-142362181130,-104109779020⟩,⟨-3100085169794,-1826328373984⟩,⟨889884851592,2479209051412⟩,⟨-1748969801325,267612569913⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8520706368,-7554515904⟩,⟨104481919146,137113548921⟩,⟨-143469708030,-104827558714⟩,⟨-3141301339031,-1848848377062⟩,⟨905981436033,2516387665062⟩,⟨-1781296797578,259700229183⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4260353184,-3777257952⟩,⟨52240959573,68556774461⟩,⟨-71734854015,-52413779357⟩,⟨-1570650669516,-924424188531⟩,⟨452990718016,1258193832531⟩,⟨-890648398789,129850114592⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3777257952,4260353184⟩,⟨-68556774461,-52240959573⟩,⟨52413779357,71734854015⟩,⟨924424188531,1570650669516⟩,⟨-1258193832531,-452990718016⟩,⟨-129850114592,890648398789⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765900641568,766383756064⟩,⟨-68556774461,-52240959573⟩,⟨52413779357,71734854015⟩,⟨924424188531,1570650669516⟩,⟨-1258193832531,-452990718016⟩,⟨-129850114592,890648398789⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272755963014,272995751313⟩,⟨25941626532,34013772236⟩,⟨-35590545283,-26027444755⟩,⟨-775021292449,-456582093496⟩,⟨222471212898,619802262853⟩,⟨-437242450332,66903142479⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531801283136,1532767512128⟩,⟨-137113548922,-104481919146⟩,⟨104827558714,143469708030⟩,⟨1848848377062,3141301339032⟩,⟨-2516387665062,-905981436032⟩,⟨-259700229184,1781296797578⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1198701889966,1205421372621⟩,⟨-930606072910,-745232999016⟩,⟨747698325197,973746085805⟩,⟨8907246926660,15182634984960⟩,⟨-10656743841960,-2167948096554⟩,⟨-5821351624242,5369877095360⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1297892152156,1311331117466⟩,⟨-1861212145820,-1490465998032⟩,⟨1495396650394,1947492171610⟩,⟨17814493853326,30365269969912⟩,⟨-21313487683915,-4335896193108⟩,⟨-11637933920302,10739754190717⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨182381953728,193708258816⟩,⟨-1576729154799,-1249710827275⟩,⟨1253845030706,1649821430951⟩,⟨12675844409608,24303564011767⟩,⟨-16630631711865,-1269630137069⟩,⟨-12334659673699,7668360215434⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62480656343,66877612214⟩,⟨-538228816046,-417807597600⟩,⟨417460625953,564556311917⟩,⟨4041023915085,8100948742365⟩,⟨-5591069131908,-72477067768⟩,⟨-4620503019480,2669634967192⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379994102447,380568070397⟩,⟨2097295241,21497852299⟩,⟨-23610200353,-638694961⟩,⟨-630253031677,138923515465⟩,⟨-309903641288,648161244801⟩,⟨-683303744388,530577957609⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176634914099,3181433111277⟩,⟨-179986948969,-17506306508⟩,⟨5331242609,197672207762⟩,⟨-1162919498362,5297046759905⟩,⟨-5448981150433,2594554417287⟩,⟨-4442151790718,5745403163513⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨180514902599,193510140799⟩,⟨-1568310903339,-1208096371039⟩,⟨1206402065873,1645565124973⟩,⟨11617624217114,23938472373359⟩,⟨-16698352700118,-60255121838⟩,⟨-13635554418244,8277036713114⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨362896856327,387218399615⟩,⟨-3145040058138,-2457807198314⟩,⟨2460247096579,3295386555924⟩,⟨24293468626722,48242036385126⟩,⟨-33328984411983,-1329885258907⟩,⟨-25970214091943,15945396928548⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518532095714,526947832248⟩,⟨-34989366876,201328023680⟩,⟨-229242704276,58308970240⟩,⟨-5762656399183,2372493452165⟩,⟨-4310045437586,6617689561768⟩,⟨-7675889784743,6680585509000⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356093094309,364797220043⟩,⟨-36333835116,209064063444⟩,⟨-238051367092,60549495450⟩,⟨-5991027703568,2503594607476⟩,⟨-4521134637381,6883541531067⟩,⟨-7984006935438,6989068133697⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712186188618,729594440086⟩,⟨-72667670232,418128126888⟩,⟨-476102734184,121098990900⟩,⟨-11982055407136,5007189214952⟩,⟨-9042269274762,13767083062134⟩,⟨-15968013870876,13978136267394⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523313507417,1525238889601⟩,⟨-33347042792,31573169798⟩,⟨-37534622416,39359929010⟩,⟨-1251236792732,1314972965048⟩,⟨-1626502813470,1573227615380⟩,⟨-2008670030509,2048909367491⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨986695195858,1012090991623⟩,⟨-122932191216,600976717676⟩,⟨-685354696043,194105883367⟩,⟨-17477103906101,7842536381844⟩,⟨-13650637366879,20170994244425⟩,⟨-23517740347792,20782509268112⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67662599903,67781620815⟩,⟨12870683942,16890435850⟩,⟨-17673424098,-12913261814⟩,⟨-383633145301,-224424278538⟩,⟨108174901862,306550992104⟩,⟨-215892038530,35526610302⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50198895515,50910864954⟩,⟨259899475803,267946767696⟩,⟨33390115887,38458428672⟩,⟨-1381340613308,-1179579116513⟩,⟨-294276440124,-105820593326⟩,⟨-275432867850,-74020738020⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134052166199,2136745248422⟩,⟨-382284621556,-291121137364⟩,⟨292084203366,400006151618⟩,⟨5171359203332,8792421365017⟩,⟨-7051692412930,-2544286163764⟩,⟨-704078515118,5003853253417⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2973087108751,2978716746362⟩,⟨-799382335082,-608369735021⟩,⟨610382300010,836439222237⟩,⟨10848332146937,18457041127110⟩,⟨-14820377099247,-5358549508544⟩,⟨-1430512344750,10541679059420⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135738163525,137924003876⟩,⟨665756065221,698126346204⟩,⟨118154494344,142918552056⟩,⟨-3636552674846,-2622580256897⟩,⟨-1367142727786,-345425595450⟩,⟨-775347548640,346473983273⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8765158969003,8906307468880⟩,⟨-45806777769424,-42309225241791⟩,⟨-9377440614803,-7508793949734⟩,⟨575118016230351,709793697940485⟩,⟨94441577383817,186163342258335⟩,⟨-9868478933470,70620552715695⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7865801531485,8198179382706⟩,⟨-43160524936416,-33099991794449⟩,⟨-14183390539004,-5166042899968⟩,⟨324464152718251,727128374889074⟩,⟨-39034340612271,364352670605148⟩,⟨-202894132534151,245039326426273⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15731603062970,16396358765412⟩,⟨-86321049872832,-66199983588898⟩,⟨-28366781078008,-10332085799936⟩,⟨648928305436502,1454256749778148⟩,⟨-78068681224542,728705341210296⟩,⟨-405788265068302,490078652852546⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10825960642717,10867759718598⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790014,2123491006166466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9726449014941,9768248090822⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790024,2123491006166451⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2396916401408,2401631448192⟩,⟨-12142992897062,-11998203029636⟩,⟨0,0⟩,⟨102165241571294,109118793444233⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7406315007862,7499125180906⟩,⟨-45313172020006,-44023117953952⟩,⟨-20398919150114,-19877636260757⟩,⟨523346606870049,547606156446775⟩,⟨286194210256678,297666492991069⟩,⟨106698249506141,110977185326197⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6306803380086,6399613553130⟩,⟨-45313172020007,-44023117953952⟩,⟨-20398919150115,-19877636260757⟩,⟨523346606870051,547606156446772⟩,⟨286194210256678,297666492991067⟩,⟨106698249506141,110977185326197⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1920586057600,1936648481024⟩,⟨-7899780051011,-7563570781145⟩,⟨-3556294282226,-3415158121634⟩,⟨33157288045551,43438215162220⟩,⟨23619468008066,28401432064258⟩,⟨6829138811400,8739758516355⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99941875711,100371372442⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137276488639,139296633220⟩,⟨681585477744,689023289920⟩,⟨307949747501,309989836064⟩,⟨-1725980926281,-1712309844048⟩,⟨-1554089624210,-1546208023672⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4317502459008,4338279929216⟩,⟨-20042772948073,-19561773810781⟩,⟨-3556294282226,-3415158121634⟩,⟨135322529616845,152557008606453⟩,⟨23619468008066,28401432064258⟩,⟨6829138811400,8739758516355⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨725793712654,774436799230⟩,⟨-6290080116276,-4915614396628⟩,⟨4920494193158,6590773111848⟩,⟨48586937253444,96484072770252⟩,⟨-66657968823966,-2659770517814⟩,⟨-51940428183886,31890793857096⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5043296171662,5112716728446⟩,⟨-26332853064349,-24477388207409⟩,⟨1364199910932,3175614990214⟩,⟨183909466870289,249041081376705⟩,⟨-43038500815900,25741661546444⟩,⟨-45111289372486,40630552373451⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458418507298,466725755306⟩,⟨1615023384482,1853278930254⟩,⟨124001142415,289893100595⟩,⟨-35517816679642,-26363158963765⟩,⟨-2841768781033,4882934159928⟩,⟨-4118084713760,3709050638281⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36519414053,38591603943⟩,⟨-781071587434,-739227806177⟩,⟨322945996948,325509439814⟩,⟨9105236444839,9819479980411⟩,⟨-6594864009033,-6530061933853⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨494937921351,505317359249⟩,⟨833951797048,1114051124077⟩,⟨446947139363,615402540409⟩,⟨-26412580234803,-16543678983354⟩,⟨-9436632790066,-1647127773925⟩,⟨-4118084713760,3709050638281⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503376910943,504367118897⟩,⟨2514798172912,2555168940688⟩,⟨0,0⟩,⟨2165995870996,4475808627517⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226591802818,231798786093⟩,⟨1513818515187,1685350050411⟩,⟨204620728588,282296974791⟩,⟨-7326127698065,-339081966514⟩,⟨-3306509318424,676055939500⟩,⟨-1889044617613,1701412824580⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-774436799230,-725793712654⟩,⟨4915614396628,6290080116276⟩,⟨-6590773111848,-4920494193158⟩,⟨-96484072770252,-48586937253444⟩,⟨2659770517814,66657968823966⟩,⟨-31890793857096,51940428183886⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3543065659778,3612486216562⟩,⟨-15127158551445,-13271693694505⟩,⟨-10147067394074,-8335652314792⟩,⟨38838456846593,103970071353009⟩,⟨26279238525880,95059400888224⟩,⟨-25061655045696,60680186700241⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442359680884,457664252755⟩,⟨279887757639,606810889670⟩,⟨-293190305223,-22241756809⟩,⟨-19780968096438,-8800027614333⟩,⟨-12448651356140,-1823842775887⟩,⟨-10045890797656,1893328169230⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨322417826200,326458115360⟩,⟨1940466224332,1948197165466⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-326458115360,-322417826200⟩,⟨-1948197165466,-1940466224332⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨773053512416,777093801576⟩,⟨-1948197165466,-1940466224332⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1350341151669,1368750900325⟩,⟨-9014768868556,-8707390711121⟩,⟨-4058235897180,-3931623959870⟩,⟨50009535023595,58695355583455⟩,⟨32502179311951,36548987501201⟩,⟨10244394308491,11850336007532⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1368750900325,-1350341151669⟩,⟨8707390711121,9014768868556⟩,⟨3931623959870,4058235897180⟩,⟨-58695355583455,-50009535023595⟩,⟨-36548987501201,-32502179311951⟩,⟨-11850336007532,-10244394308491⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-269239272549,-250829523893⟩,⟨8707390711121,9014768868556⟩,⟨3931623959870,4058235897180⟩,⟨-58695355583455,-50009535023595⟩,⟨-36548987501201,-32502179311951⟩,⟨-11850336007532,-10244394308491⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12730733493,-11301413240⟩,⟨420931764958,457911774547⟩,⟨69763653843,91950095412⟩,⟨-4895235608319,-4239610734597⟩,⟨1514835196477,1951708637227⟩,⟨2572680510803,2775504236738⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429628947391,446362839515⟩,⟨700819522597,1064722664217⟩,⟨-223426651380,69708338603⟩,⟨-24676203704757,-13039638348930⟩,⟨-10933816159663,127865861340⟩,⟨-7473210286853,4668832405968⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100371372442,-99941875711⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4502996377,4745968821⟩,⟨27675521186,30070053406⟩,⟨39820591103,40030926275⟩,⟨-310218441363,-298956567345⟩,⟨248728938086,249843280775⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9816454504,10366482432⟩,⟨7917737970,16543091202⟩,⟨86808202403,87438394478⟩,⟨-923374993166,-784723445018⟩,⟨100123741306,111191132797⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1463865921414,1482020960707⟩,⟨-7522812848387,-7211123373469⟩,⟨-1415757547728,-1344132519032⟩,⟨103890318736401,111396913071968⟩,⟨21891423163587,23710877219660⟩,⟨4856045554504,5304997488993⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13069414505,13972880200⟩,⟨-60385537330,-42082735127⟩,⟨102226425451,105856922953⟩,⟨-543448245733,-98341240333⟩,⟨-290801646152,-205583241807⟩,⟨-181820708924,-162225926274⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13972880200,-13069414505⟩,⟨42082735127,60385537330⟩,⟨-105856922953,-102226425451⟩,⟨98341240333,543448245733⟩,⟨205583241807,290801646152⟩,⟨162225926274,181820708924⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114344252642,-113011290216⟩,⟨-834949586717,-815787791054⟩,⟨-105856922953,-102226425451⟩,⟨2297364495885,2742471501285⟩,⟨205583241807,290801646152⟩,⟨162225926274,181820708924⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86534217999,91572657465⟩,⟨-601241393369,-559852244566⟩,⟨597077375047,618515997869⟩,⟨3219379405906,3911619046816⟩,⟨-3633559124604,-3173118060151⟩,⟨-2529005642402,-2308202616204⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨115209780019,123429888655⟩,⟨-1436943704500,-1312907937848⟩,⟨677024709881,727905186935⟩,⟨19806188450171,22777445100581⟩,⟨-6722182741409,-5391610038121⟩,⟨-4619471521353,-4091096947398⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-123429888655,-115209780019⟩,⟨1312907937848,1436943704500⟩,⟨-727905186935,-677024709881⟩,⟨-22777445100581,-19806188450171⟩,⟨5391610038121,6722182741409⟩,⟨4091096947398,4619471521353⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨976081739121,984301847757⟩,⟨1312907937848,1436943704500⟩,⟨-727905186935,-677024709881⟩,⟨-22777445100581,-19806188450171⟩,⟨5391610038121,6722182741409⟩,⟨4091096947398,4619471521353⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121865990669,124700758047⟩,⟨768990985388,798871331045⟩,⟨181161688722,192980217917⟩,⟨-2803053269139,-2191975924546⟩,⟨-806527126085,-535565286515⟩,⟨-212793721734,-103912302589⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11615658619,11891286806⟩,⟨167698509920,173661986060⟩,⟨21014312068,22017285560⟩,⟨640145782792,795830940813⟩,⟨91210627776,118510736990⟩,⟨-18808188574,-12965161835⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166194632319,177327642317⟩,⟨1465830819943,1890355467734⟩,⟨-6119729249,219178520282⟩,⟨-11253287901061,7401864890369⟩,⟨-5748219730538,6807173361803⟩,⟨-5805167792324,4719786091580⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177327642317,-166194632319⟩,⟨-1890355467734,-1465830819943⟩,⟨-219178520282,6119729249⟩,⟨-7401864890369,11253287901061⟩,⟨-6807173361803,5748219730538⟩,⟨-4719786091580,5805167792324⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49264160501,65604153774⟩,⟨-376536952547,219519230468⟩,⟨-14557791694,288416704040⟩,⟨-14727992588434,10914205934547⟩,⟨-10113682680227,6424275670038⟩,⟨-6608830709193,7506580616904⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27479379702015,28880079569135⟩,⟨-269848131211656,-223853802492009⟩,⟨-102997328588596,-66911135854850⟩,⟨2518715039651435,4449654898909209⟩,⟨477131267164347,2190063741287294⟩,⟨-552849553653580,1177042156534433⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13507196564,14142896414⟩,⟨170464496930,181207470748⟩,⟨40158645182,43773578842⟩,⟨439839401406,674968916426⟩,⟨70462486320,161706647022⟩,⟨11430564067,44707101207⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337576587382,371481268098⟩,⟨789281757182,2009663932646⟩,⟨-321184315793,327784233079⟩,⟨-47011509775495,5553295223820⟩,⟨-20095406057905,13868254360667⟩,⟨-15026591906118,11426717544877⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371481268098,-337576587382⟩,⟨-2009663932646,-789281757182⟩,⟨-327784233079,321184315793⟩,⟨-5553295223820,47011509775495⟩,⟨-13868254360667,20095406057905⟩,⟨-11426717544877,15026591906118⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58147679293,108786252133⟩,⟨-1308844410049,275440907035⟩,⟨-551210884459,390892654396⟩,⟨-30229498928577,33971871426565⟩,⟨-24802070520330,20223271919245⟩,⟨-18899927831730,19695424312086⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237218364350,239668005662⟩,⟨1557758806128,1566055611764⟩,⟨307949747501,309989836064⟩,⟨-3925004181833,-3911333099600⟩,⟨-1554089624210,-1546208023672⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1705147396098,-1616944027148⟩,⟨-5646859260365,-2695136370217⟩,⟨-516616400699,1487381118280⟩,⟨-20131117801746,105299269686406⟩,⟨-59019781966984,42307243340869⟩,⟨-46723634131920,50373631704704⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-193388744152,-179216372748⟩,⟨-1879344381725,-1429599109995⟩,⟨-357869951465,-97725894713⟩,⟨-7265308539416,12519600739790⟩,⟨-7272569402770,6685662467117⟩,⟨-5327679636245,6565228417769⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43829620198,60451632914⟩,⟨-321585575597,136456501769⟩,⟨-49920203964,212263941351⟩,⟨-11190312721249,8608267640190⟩,⟨-8826659026980,5139454443445⟩,⟨-5677464792731,6216128107241⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2605335435,6490909085⟩,⟨-115349097360,38153977562⟩,⟨-34329251525,51859346144⟩,⟨-3783513281409,4003293731078⟩,⟨-2957700964619,2103294299402⟩,⟨-2070756225912,2122937402321⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1747171706,3323657368⟩,⟨-35361832792,15004876976⟩,⟨-5489269544,23340729720⟩,⟨-1310318329130,1134687623276⟩,⟨-1094753266652,617825586746⟩,⟨-643573506349,765487266624⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3051894617,5854195473⟩,⟨-86165166009,14410320855⟩,⟨-20418782897,35684862375⟩,⟨-2470883356958,2638049598724⟩,⟨-2106965779565,1327888384239⟩,⟨-1273708205812,1410235773369⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5854195473,-3051894617⟩,⟨-14410320855,86165166009⟩,⟨-35684862375,20418782897⟩,⟨-2638049598724,2470883356958⟩,⟨-1327888384239,2106965779565⟩,⟨-1410235773369,1273708205812⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3248860038,3439014468⟩,⟨-129759418215,124319143571⟩,⟨-70014113900,72278129041⟩,⟨-6421562880133,6474177088036⟩,⟨-4285589348858,4210260078967⟩,⟨-3480991999281,3396645608133⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49264160501,65604153774⟩,⟨-376536952547,219519230468⟩,⟨-14557791694,288416704040⟩,⟨-14727992588434,10914205934547⟩,⟨-10113682680227,6424275670038⟩,⟨-6608830709193,7506580616904⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3248860038,3439014468⟩,⟨-129759418215,124319143571⟩,⟨-70014113900,72278129041⟩,⟨-6421562880133,6474177088036⟩,⟨-4285589348858,4210260078967⟩,⟨-3480991999281,3396645608133⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (519/5120) u, BivariateJet2.affineZ (593/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000026

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000027Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2093714738176,-2093714699456⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2093714738176,-2093714699392⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-177319094464,-177319094400⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-177319094400,-177319094336⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨92296414016,92296414080⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-100759939136,-100759939072⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨92296538112,92296538176⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-100760087040,-100760086976⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8463548928,-8463548864⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8463525056,-8463524992⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨193056353152,193056353216⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨193056625088,193056625152⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1916395604992,1916395643584⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1916395605056,1916395643648⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2518909148928,-2518909091072⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2100520102144,-2100520063296⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2086946198784,-2086946160000⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-178507905600,-178507905536⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-176132453376,-176132453312⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨89718545216,89718545280⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-97695144192,-97695144128⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨94896198144,94896198208⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-103866782144,-103866782080⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8970584000,-8970583936⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7976598976,-7976598912⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨187413689408,187413689472⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨198762980224,198762980288⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1908438254464,1908438293056⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1924387609984,1924387648576⟩



end LaneCBRB2Cell000027Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000027
open Set LaneCBRB2Cell000027Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111454401331,111454401332⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨131211250892,131211250893⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111454401332,-111454401331⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438301412556,438301412557⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨52305109974,52305109976⟩,⟨-131211250893,-131211250892⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163759511305,163759511308⟩,⟨968300376883,968300376884⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52305109973,52305109977⟩,⟨-131211250893,-131211250892⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2093714738176,-2093714699392⟩,⟨6501347708349,6501347708477⟩,⟨2942836698318,2942836698380⟩,⟨-38442087340180,-38442087338682⟩,⟨-24783144938711,-24783144937875⟩,⟨-7876485900244,-7876485899916⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311834539700,-311834533917⟩,⟨-875558950175,-875558915980⟩,⟨-396321982106,-396321966623⟩,⟨5725503284335,5725503284902⟩,⟨3585853593504,3585853632597⟩,⟨1173111269727,1173111269853⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨311834533917,311834539700⟩,⟨875558915980,875558950175⟩,⟨396321966623,396321982106⟩,⟨-5725503284902,-5725503284335⟩,⟨-3585853632597,-3585853593504⟩,⟨-1173111269853,-1173111269727⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-163759511308,-163759511305⟩,⟨-968300376884,-968300376883⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨935752116468,935752116471⟩,⟨-968300376884,-968300376883⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-177319094464,-177319094336⟩,⟨-1137755934320,-1137755934314⟩,⟨-515005513850,-515005513846⟩,⟨-1177330492356,-1177330492343⟩,⟨759010611841,759010611853⟩,⟨-241225897567,-241225897563⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150909470845,-150909470735⟩,⟨-812141822912,-812141822789⟩,⟨-367616203276,-367616203217⟩,⟨1001980763235,1001980763265⟩,⟨1375739381336,1375739381486⟩,⟨205298096434,205298096444⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150909470735,150909470845⟩,⟨812141822789,812141822912⟩,⟨367616203217,367616203276⟩,⟨-1001980763265,-1001980763235⟩,⟨-1375739381486,-1375739381336⟩,⟨-205298096444,-205298096434⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨462744004652,462744010545⟩,⟨1687700738769,1687700773087⟩,⟨763938169840,763938185382⟩,⟨-6727484048167,-6727484047570⟩,⟨-4961593014083,-4961592974840⟩,⟨-1378409366297,-1378409366161⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨823468094305,823468106124⟩,⟨4086972619589,4086972711851⟩,⟨763938169840,763938185382⟩,⟨-18797842220160,-18797842219057⟩,⟨-4961593014083,-4961592974840⟩,⟨-1378409366297,-1378409366161⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨104610219946,104610219954⟩,⟨-262422501786,-262422501784⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11556479091108,11556479091992⟩,⟨28990285616802,28990285621459⟩,⟨-96839890267323,-96839890252285⟩,⟨145448566733522,145448566769118⟩,⟨-242930053054858,-242930052901382⟩,⟨1622979502691363,1622979503071219⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8655107934855,8655108059743⟩,⟨64668337358340,64668338646466⟩,⟨-64497840457110,-64497839240914⟩,⟨126874866123646,126874872640362⟩,⟨-573908346126581,-573908334388914⟩,⟨1066457934092516,1066457954584100⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨96280944640,96281079552⟩,⟨-711448882659,-711446845527⟩,⟨709571115413,709573146420⟩,⟨9060062514916,9060112506437⟩,⟨-4114519659044,-4114455758183⟩,⟨-1331824186285,-1331744913065⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1195792572416,1195792707328⟩,⟨-711448882659,-711446845527⟩,⟨709571115413,709573146420⟩,⟨9060062514916,9060112506437⟩,⟨-4114519659044,-4114455758183⟩,⟨-1331824186285,-1331744913065⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨92296414016,92296538176⟩,⟨-654165561066,-654163614150⟩,⟨652438911316,652440852406⟩,⟨7941375303027,7941424525970⟩,⟨-3395059267385,-3394997774609⟩,⟨-1611743317302,-1611667985074⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨100378534935,100378681294⟩,⟨-771170267642,-771167818629⟩,⟨769134634126,769137075866⟩,⟨10243869985519,10243934656292⟩,⟨-4882076304571,-4881998252187⟩,⟨-1022572227781,-1022478380602⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-96281079552,-96280944640⟩,⟨711446845527,711448882659⟩,⟨-709573146420,-709571115413⟩,⟨-9060112506437,-9060062514916⟩,⟨4114455758183,4114519659044⟩,⟨1331744913065,1331824186285⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1003230548224,1003230683136⟩,⟨711446845527,711448882659⟩,⟨-709573146420,-709571115413⟩,⟨-9060112506437,-9060062514916⟩,⟨4114455758183,4114519659044⟩,⟨1331744913065,1331824186285⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-100760087040,-100759939072⟩,⟨779725034681,779727372175⟩,⟨-777671619577,-777669289072⟩,⟨-10482570767126,-10482511327259⟩,⟨5060812429294,5060886375166⟩,⟨909515687958,909606062064⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-91936827589,-91936680213⟩,⟨646249029765,646251540675⟩,⟨-644547697273,-644545193806⟩,⟨-7725320258151,-7725253022220⟩,⟨3234195045731,3234275444608⟩,⟨1711562191352,1711658088153⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8441707346,8442001081⟩,⟨-124921237877,-124916277954⟩,⟨124586936853,124591882060⟩,⟨2518549727368,2518681634072⟩,⟨-1647881258840,-1647722807579⟩,⟨688989963571,689179707551⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4220853673,4221000541⟩,⟨-62460618939,-62458138977⟩,⟨62293468426,62295941030⟩,⟨1259274863684,1259340817036⟩,⟨-823940629420,-823861403789⟩,⟨344494981785,344589853776⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4221000541,-4220853673⟩,⟨62458138977,62460618939⟩,⟨-62295941030,-62293468426⟩,⟨-1259340817036,-1259274863684⟩,⟨823861403789,823940629420⟩,⟨-344589853776,-344494981785⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757902383075,757902549207⟩,⟨62458138977,62460618939⟩,⟨-62295941030,-62293468426⟩,⟨-1259340817036,-1259274863684⟩,⟨823861403789,823940629420⟩,⟨-344589853776,-344494981785⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8431034348,8431057977⟩,⟨-124599076060,-124598544694⟩,⟨124270040544,124270570376⟩,⟨2507418669563,2507434920735⟩,⟨-1638864736008,-1638847277380⟩,⟨682597051124,682616504258⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8431057977,-8431034348⟩,⟨124598544694,124599076060⟩,⟨-124270570376,-124270040544⟩,⟨-2507434920735,-2507418669563⟩,⟨1638847277380,1638864736008⟩,⟨-682616504258,-682597051124⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091080569799,1091080593428⟩,⟨124598544694,124599076060⟩,⟨-124270570376,-124270040544⟩,⟨-2507434920735,-2507418669563⟩,⟨1638847277380,1638864736008⟩,⟨-682616504258,-682597051124⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8463548928,-8463524992⟩,⟨125561346723,125561884916⟩,⟨-125230840784,-125230304145⟩,⟨-2541149409894,-2541132855497⟩,⟨1665812005292,1665829757178⟩,⟨-702154646471,-702134905874⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4231774464,-4231762496⟩,⟨62780673361,62780942458⟩,⟨-62615420392,-62615152072⟩,⟨-1270574704947,-1270566427748⟩,⟨832906002646,832914878589⟩,⟨-351077323236,-351067452937⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4231762496,4231774464⟩,⟨-62780942458,-62780673361⟩,⟨62615152072,62615420392⟩,⟨1270566427748,1270574704947⟩,⟨-832914878589,-832906002646⟩,⟨351067452937,351077323236⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766355146112,766355177344⟩,⟨-62780942458,-62780673361⟩,⟨62615152072,62615420392⟩,⟨1270566427748,1270574704947⟩,⟨-832914878589,-832906002646⟩,⟨351067452937,351077323236⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272770142449,272770148357⟩,⟨31149636173,31149769015⟩,⟨-31067642594,-31067510136⟩,⟨-626858730184,-626854667390⟩,⟨409711819345,409716184002⟩,⟨-170654126065,-170649262781⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532710292224,1532710354688⟩,⟨-125561884916,-125561346722⟩,⟨125230304144,125230840784⟩,⟨2541132855496,2541149409894⟩,⟨-1665829757178,-1665812005292⟩,⟨702134905874,702154646472⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1205032740661,1205032902711⟩,⟨-854558619372,-854555942626⟩,⟨852302905276,852305574059⟩,⟨12094540593981,12094610998288⟩,⟨-6151004149172,-6150918656218⟩,⟨-394079987023,-393976949314⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1310553853546,1310554177646⟩,⟨-1709117238744,-1709111885253⟩,⟨1704605810552,1704611148117⟩,⟨24189081187968,24189221996567⟩,⟨-12302008298340,-12301837312437⟩,⟨-788159826111,-787954046564⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨193056353152,193056625152⟩,⟨-1433893214039,-1433888368033⟩,⟨1430107920331,1430112752041⟩,⟨18423873065700,18424008857695⟩,⟨-8455957227298,-8455798619179⟩,⟨-2521359213595,-2521173838834⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨66367244823,66367352368⟩,⟨-484938385105,-484936648567⟩,⟨483658112787,483659844155⟩,⟨6054067127811,6054112326993⟩,⟨-2683414824056,-2683359685166⟩,⟨-1028618028411,-1028551412016⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380239366443,380239390176⟩,⟨12272570515,12272891658⟩,⟨-12240534125,-12240213909⟩,⟨-250538635674,-250528755203⟩,⟨164966558417,164977139554⟩,⟨-70779753336,-70768002681⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179380808114,3179381006559⟩,⟨-102620091650,-102617393593⟩,⟨102346843054,102349533325⟩,⟨2101426351964,2101509577192⟩,⟨-1386067514294,-1385978520700⟩,⟨598317612362,598416285628⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨191909516140,191909839100⟩,⟨-1408456696243,-1408451414398⟩,⟨1404738031372,1404743297540⟩,⟨17723483855879,17723623581042⟩,⟨-7933389670501,-7933221541016⟩,⟨-2848226512608,-2848024993323⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨384965869292,384966464252⟩,⟨-2842349910282,-2842339782431⟩,⟨2834845951703,2834856049581⟩,⟨36147356921579,36147632438737⟩,⟨-16389346897799,-16389020160195⟩,⟨-5369585726203,-5369198832157⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522428328868,522428557902⟩,⟨86105814940,86109252732⟩,⟨-85882225016,-85878797416⟩,⟨-1729052376374,-1728960507923⟩,⟨1128711079620,1128821112298⟩,⟨-467998784006,-467867327429⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360114131976,360114368789⟩,⟨89030166699,89033740764⟩,⟨-88799002613,-88795439138⟩,⟨-1780438463180,-1780342497451⟩,⟨1159726561658,1159841170837⟩,⟨-476594937474,-476458328200⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720228263952,720228737578⟩,⟨178060333398,178067481528⟩,⟨-177598005226,-177590878276⟩,⟨-3560876926360,-3560684994902⟩,⟨2319453123316,2319682341674⟩,⟨-953189874948,-952916656400⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524279234247,1524279320340⟩,⟨-963340222,-962270662⟩,⟨959733768,960800240⟩,⟨33697934761,33730740331⟩,⟨-26982479798,-26947269284⟩,⟨19518401616,19557595348⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨998469646819,998470359814⟩,⟨246218263172,246228887764⟩,⟨-245579703292,-245569110123⟩,⟨-4914767428282,-4914479207733⟩,⟨3198149401508,3198490788036⟩,⟨-1308954945347,-1308550062308⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67669635074,67669638006⟩,⟨15455390340,15455456588⟩,⟨-15414708250,-15414642194⟩,⟨-309261029539,-309258991926⟩,⟨201524747234,201526932246⟩,⟨-82917106010,-82914676206⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50680487617,50680490541⟩,⟨263108601352,263108667713⟩,⟨35472018283,35472070915⟩,⟨-1273636606435,-1273634531771⟩,⟨-200991537901,-200989590566⟩,⟨-168354584813,-168352668231⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136585717279,2136585891429⟩,⟨-350064512832,-350062998088⟩,⟨349140056750,349141567124⟩,⟨7113314738157,7113361426124⟩,⟨-4672908723286,-4672858796874⟩,⟨1986067265238,1986122625975⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2978383162455,2978383526601⟩,⟨-731980667697,-731977470554⟩,⟨730047611443,730050799371⟩,⟨14933819001013,14933917747657⟩,⟨-9830802528036,-9830697219236⟩,⟨4212491131477,4212607573003⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137284506293,137284531000⟩,⟨678975164971,678975581187⟩,⟨129737992141,129738295346⟩,⟨-3112023455349,-3112011203842⟩,⟨-846505685505,-846494518635⟩,⟨-214768891028,-214757989581⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8805987177205,8805988762013⟩,⟨-43552266013569,-43552223639640⟩,⟨-8321943980928,-8321921536738⟩,⟨630413977358499,630415595823771⟩,⟨136613905708277,136614928822495⟩,⟨29504379370427,29505165603165⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7996742084939,7996749234486⟩,⟨-37578003547422,-37577851378154⟩,⟨-9524034347448,-9523923374675⟩,⟨513611832994953,513616887642383⟩,⟨157536922957822,157541193921577⟩,⟨20026890018449,20031038106070⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15993484169878,15993498468972⟩,⟨-75156007094844,-75155702756308⟩,⟨-19048068694896,-19047846749350⟩,⟨1027223665989906,1027233775284766⟩,⟨315073845915644,315082387843154⟩,⟨40053780036898,40062076212140⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10846819911700,10846819911799⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738054,2111240126795878⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9747308283924,9747308284023⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738069,2111240126795861⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2399271880896,2399271938752⟩,⟨-12070358171930,-12070358171514⟩,⟨0,0⟩,⟨105643681588589,105643681622780⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7382324299569,7382324299705⟩,⟨-43651250206599,-43651250204944⟩,⟨-19758749539063,-19758749538289⟩,⟨516214559841511,516214559871118⟩,⟨283230942045726,283230942061247⟩,⟨105768364399718,105768364406049⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6282812671793,6282812671929⟩,⟨-43651250206600,-43651250204943⟩,⟨-19758749539063,-19758749538288⟩,⟨516214559841513,516214559871115⟩,⟨283230942045725,283230942061245⟩,⟨105768364399717,105768364406049⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1916395604992,1916395643648⟩,⟨-7639103642962,-7639103642473⟩,⟨-3457842212304,-3457842212078⟩,⟨37264756839395,37264756855728⟩,⟨25542155546333,25542155554354⟩,⟨7635260000894,7635260004331⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100156582133,100156582135⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139369430412,139369430416⟩,⟨679866143879,679866143888⟩,⟨307741583422,307741583427⟩,⟨-1705494687256,-1705494687251⟩,⟨-1543985210332,-1543985210320⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4315667485888,4315667582400⟩,⟨-19709461814892,-19709461813987⟩,⟨-3457842212304,-3457842212078⟩,⟨142908438427984,142908438478508⟩,⟨25542155546333,25542155554354⟩,⟨7635260000894,7635260004331⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨769931738584,769932928504⟩,⟨-5684699820564,-5684679564862⟩,⟨5669691903406,5669712099162⟩,⟨72294713843158,72295264877474⟩,⟨-32778693795598,-32778040320390⟩,⟨-10739171452406,-10738397664314⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5085599224472,5085600510904⟩,⟨-25394161635456,-25394141378849⟩,⟨2211849691102,2211869887084⟩,⟨215203152271142,215203703355982⟩,⟨-7236538249265,-7235884766036⟩,⟨-3103911451512,-3103137659983⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463256798340,463256915533⟩,⟨1741371499490,1741374370389⟩,⟨201481548404,201483388099⟩,⟨-31059725423152,-31059640350654⟩,⟨1104241846776,1104317475373⟩,⟨-282741131954,-282670645821⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38691831753,38691833952⟩,⟨-783125178321,-783125167239⟩,⟨324226151534,324226169925⟩,⟨9745628004008,9745628033606⟩,⟨-6562358286202,-6562358193788⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨501948630093,501948749485⟩,⟨958246321169,958249203150⟩,⟨525707699938,525709558024⟩,⟨-21314097419144,-21314012317048⟩,⟨-5458116439426,-5458040718415⟩,⟨-282741131954,-282670645821⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503871945521,503871957673⟩,⟨2534900173993,2534900296365⟩,⟨0,0⟩,⟨3319096918590,3319099843609⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨230027428912,230027489174⟩,⟨1596366117058,1596367779494⟩,⟨240915470879,240916328193⟩,⟨-3833922445363,-3833868012424⟩,⟨-1289277202431,-1289238099236⟩,⟨-129571460705,-129539155979⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-769932928504,-769931738584⟩,⟨5684679564862,5684699820564⟩,⟨-5669712099162,-5669691903406⟩,⟨-72295264877474,-72294713843158⟩,⟨32778040320390,32778693795598⟩,⟨10738397664314,10739171452406⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3545734557384,3545735843816⟩,⟨-14024782250030,-14024761993423⟩,⟨-9127554311466,-9127534115484⟩,⟨70613173550510,70613724635350⟩,⟨58320195866723,58320849349952⟩,⟨18373657665208,18374431456737⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449442273433,449442436510⟩,⟨414728644365,414732007534⟩,⟨-164556766683,-164553846617⟩,⟨-13893318392655,-13893221492814⟩,⟨-7155936212116,-7155833415008⟩,⟨-3907335811154,-3907226014333⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨327519022610,327519022616⟩,⟨1936600753766,1936600753768⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-327519022616,-327519022610⟩,⟨-1936600753768,-1936600753766⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨771992605160,771992605166⟩,⟨-1936600753768,-1936600753766⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1345545784365,1345545811518⟩,⟨-8738993320067,-8738993251591⟩,⟨-3955707555168,-3955707524166⟩,⟨53074385921097,53074385934521⟩,⟨33947320273417,33947320357312⟩,⟨10874530528746,10874530531576⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1345545811518,-1345545784365⟩,⟨8738993251591,8738993320067⟩,⟨3955707524166,3955707555168⟩,⟨-53074385934521,-53074385921097⟩,⟨-33947320357312,-33947320273417⟩,⟨-10874530531576,-10874530528746⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-246034183742,-246034156589⟩,⟨8738993251591,8738993320067⟩,⟨3955707524166,3955707555168⟩,⟨-53074385934521,-53074385921097⟩,⟨-33947320357312,-33947320273417⟩,⟨-10874530531576,-10874530528746⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11704146381,-11704145088⟩,⟨445085290744,445085297275⟩,⟨90100535817,90100548133⟩,⟨-4610565232189,-4610565214995⟩,⟨1642710086611,1642710148889⟩,⟨2636434942903,2636434967803⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437738127052,437738291422⟩,⟨859813935109,859817304809⟩,⟨-74456230866,-74453298484⟩,⟨-18503883624844,-18503786707809⟩,⟨-5513226125505,-5513123266119⟩,⟨-1270900868251,-1270791046530⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100156582135,-100156582133⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4764570842,4764570844⟩,⟨29748786567,29748786572⟩,⟨39925700025,39925700027⟩,⟨-313830659855,-313830659844⟩,⟨249286067484,249286067488⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10396889452,10396889708⟩,⟨12610462798,12610464399⟩,⟨87122870713,87122872820⟩,⟨-880186516026,-880186499012⟩,⟨105671963339,105671976504⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1468090640820,1468090661892⟩,⟨-7286313234447,-7286312860793⟩,⟨-1361959891318,-1361959824510⟩,⟨105838778576691,105838785920568⟩,⟨22364743815170,22364745301440⟩,⟨4984450582381,4984450864808⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13882141591,13882142133⟩,⟨-52061016201,-52061008591⟩,⟨103449678425,103449683859⟩,⟨-341576298154,-341576134688⟩,⟨-240397365389,-240397280201⟩,⟨-168704841701,-168704822060⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13882142133,-13882141591⟩,⟨52061008591,52061016201⟩,⟨-103449683859,-103449678425⟩,⟨341576134688,341576298154⟩,⟨240397280201,240397365389⟩,⟨168704822060,168704841701⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114038724268,-114038723724⟩,⟨-824541816523,-824541808911⟩,⟨-103449683859,-103449678425⟩,⟨2540599390240,2540599553706⟩,⟨240397280201,240397365389⟩,⟨168704822060,168704841701⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨91165277691,91165279538⟩,⟨-592096353812,-592096349145⟩,⟨599444395889,599444411326⟩,⟨3595969150270,3595969151315⟩,⟨-3333876660836,-3333876621469⟩,⟨-2393600096262,-2393600095882⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨121725762206,121725766420⟩,⟨-1394719138982,-1394719078180⟩,⟨687464537881,687464577810⟩,⟨21424447168842,21424448490149⟩,⟨-5836112378403,-5836111753371⟩,⟨-4267759885578,-4267759696315⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-121725766420,-121725762206⟩,⟨1394719078180,1394719138982⟩,⟨-687464577810,-687464537881⟩,⟨-21424448490149,-21424447168842⟩,⟨5836111753371,5836112378403⟩,⟨4267759696315,4267759885578⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨977785861356,977785865570⟩,⟨1394719078180,1394719138982⟩,⟨-687464577810,-687464537881⟩,⟨-21424448490149,-21424447168842⟩,⟨5836111753371,5836112378403⟩,⟨4267759696315,4267759885578⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123939988554,123939989093⟩,⟨781387558718,781387569045⟩,⟨186531745002,186531751252⟩,⟨-2507547123151,-2507546873830⟩,⟨-668007649849,-668007522951⟩,⟨-154621121572,-154621073864⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11827824445,11827824558⟩,⟨171039019814,171039022212⟩,⟨21459107842,21459109074⟩,⟨709665005453,709665064713⟩,⟨105290339182,105290366680⟩,⟨-15528801595,-15528795307⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172047405635,172047561100⟩,⟨1679452715896,1679458256732⟩,⟨107237326008,107240012508⟩,⟨-2009421874405,-2009207915445⟩,⟨490993908198,491128189475⟩,⟨-538529960474,-538431712044⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172047561100,-172047405635⟩,⟨-1679458256732,-1679452715896⟩,⟨-107240012508,-107237326008⟩,⟨2009207915445,2009421874405⟩,⟨-491128189475,-490993908198⟩,⟨538431712044,538529960474⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57979867812,57980083539⟩,⟨-83092139674,-83084936402⟩,⟨133675458371,133679002185⟩,⟨-1824714529918,-1824446138019⟩,⟨-1780405391906,-1780232007434⟩,⟨408860251339,408990804495⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27875869611001,27875895095921⟩,⟨-242111706946679,-242111074503757⟩,⟨-83497643568297,-83497211085905⟩,⟨3376776133162550,3376798503140814⟩,⟨1289389939219180,1289407669905793⟩,⟨300680944802859,300696901385952⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13970857947,13970858069⟩,⟨176160329070,176160332168⟩,⟨42052747340,42052748934⟩,⟨545298742190,545298830217⟩,⟨114524889818,114524931474⟩,⟨28431444246,28431459398⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354202542880,354202869796⟩,⟨1389811649633,1389823874244⟩,⟨5205196653,5211716351⟩,⟨-20849093856135,-20848590347755⟩,⟨-3350642944085,-3350319730698⟩,⟨-1845627487686,-1845390335915⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354202869796,-354202542880⟩,⟨-1389823874244,-1389811649633⟩,⟨-5211716351,-5205196653⟩,⟨20848590347755,20849093856135⟩,⟨3350319730698,3350642944085⟩,⟨1845390335915,1845627487686⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83535257256,83535748542⟩,⟨-530009939135,-529994344824⟩,⟨-79667947217,-79658495137⟩,⟨2344706722911,2345307148326⟩,⟨-2162906394807,-2162480322034⟩,⟨574489467664,574836441156⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239526012545,239526012551⟩,⟨1556468968991,1556468969002⟩,⟨307741583422,307741583427⟩,⟨-3904517942808,-3904517942803⟩,⟨-1543985210332,-1543985210320⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1658807525004,-1658806034022⟩,⟨-4198816766125,-4198774329823⟩,⟨470817915421,470842368911⟩,⟨43134282416444,43135824352329⟩,⟨-7827315273117,-7826229225180⟩,⟨1883142504135,1884047415795⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186985368197,-186985199316⟩,⟨-1652163413086,-1652157552316⟩,⟨-228344202316,-228341183245⟩,⟨2677361319351,2677599323356⟩,⟨-252242755575,-252094626214⟩,⟨605294194795,605404783916⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52540644348,52540813235⟩,⟨-95694444095,-95688583314⟩,⟨79397381106,79400400182⟩,⟨-1227156623457,-1226918619447⟩,⟨-1796227965907,-1796079836534⟩,⟨255851545174,255962134297⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4405013144,4405055442⟩,⟨-34261742835,-34260232122⟩,⟨5954879787,5955722822⟩,⟨65107073701,65169703410⟩,⟨-307741874522,-307700173573⟩,⟨41985191538,42016514434⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2510677685,2510693826⟩,⟨-9145631184,-9145041664⟩,⟨7588077210,7588390140⟩,⟨-100625587924,-100600424407⟩,⟨-185488634526,-185472553910⟩,⟨35918763690,35930283490⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4375989811,4376018034⟩,⟨-33384001757,-33382861784⟩,⟨5329797860,5330394313⟩,⟨36781054648,36833655725⟩,⟨-288935442643,-288903005269⟩,⟨32310096026,32332256104⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4376018034,-4375989811⟩,⟨33382861784,33384001757⟩,⟨-5330394313,-5329797860⟩,⟨-36833655725,-36781054648⟩,⟨288903005269,288935442643⟩,⟨-32332256104,-32310096026⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨28995110,29065631⟩,⟨-878881051,-876230365⟩,⟨624485474,625924962⟩,⟨28273417976,28388648762⟩,⟨-18838869253,-18764730930⟩,⟨9652935434,9706418408⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57979867812,57980083539⟩,⟨-83092139674,-83084936402⟩,⟨133675458371,133679002185⟩,⟨-1824714529918,-1824446138019⟩,⟨-1780405391906,-1780232007434⟩,⟨408860251339,408990804495⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨28995110,29065631⟩,⟨-878881051,-876230365⟩,⟨624485474,625924962⟩,⟨28273417976,28388648762⟩,⟨-18838869253,-18764730930⟩,⟨9652935434,9706418408⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111239652966,111669149696⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨129278515609,133143986176⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111669149696,-111239652966⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438086664192,438516160922⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨51509408562,53101566362⟩,⟨-133143986176,-129278515609⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨162749061528,164770716058⟩,⟨966367641600,970233112167⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨51079911832,53531063092⟩,⟨-133143986176,-129278515609⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2100520102144,-2086946160000⟩,⟨6448551563444,6554769523494⟩,⟨2923343375428,2962558514161⟩,⟨-39076443050475,-37820261483282⟩,⟨-25089534455370,-24482203873495⟩,⟨-7982410306638,-7772483959942⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-314779937366,-308908537589⟩,⟨-899034094535,-851944760873⟩,⟨-405034934609,-387554240515⟩,⟨5479423298107,5970011266516⟩,⟨3465765892802,3705131627139⟩,⟨1133310464105,1212624831217⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨308908537589,314779937366⟩,⟨851944760873,899034094535⟩,⟨387554240515,405034934609⟩,⟨-5970011266516,-5479423298107⟩,⟨-3705131627139,-3465765892802⟩,⟨-1212624831217,-1133310464105⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164770716058,-162749061528⟩,⟨-970233112167,-966367641600⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨934740911718,936762566248⟩,⟨-970233112167,-966367641600⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-178507905600,-176132453312⟩,⟨-1141260187832,-1134260160395⟩,⟨-515815250898,-514197939379⟩,⟨-1184593944646,-1170106871959⟩,⟨755135200164,762878723069⟩,⟨-241985047122,-240469963374⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152085270880,-149737579697⟩,⟨-817527615068,-806762814733⟩,⟨-369286807849,-365947243335⟩,⟨984565639350,1019389022407⟩,⟨1367327738626,1384158733597⟩,⟨203584919524,207009665550⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149737579697,152085270880⟩,⟨806762814733,817527615068⟩,⟨365947243335,369286807849⟩,⟨-1019389022407,-984565639350⟩,⟨-1384158733597,-1367327738626⟩,⟨-207009665550,-203584919524⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨458646117286,466865208246⟩,⟨1658707575606,1716561709603⟩,⟨753501483850,774321742458⟩,⟨-6989400288923,-6463988937457⟩,⟨-5089290360736,-4833093631428⟩,⟨-1419634496767,-1336895383629⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨818426887465,828534004626⟩,⟨4050900917591,4122900097276⟩,⟨753501483850,774321742458⟩,⟨-19165465124157,-18428398484659⟩,⟨-5089290360736,-4833093631428⟩,⟨-1419634496767,-1336895383629⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨102159823664,107062126184⟩,⟨-266287972352,-258557031218⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11291815908241,11833671753299⟩,⟨27269945987035,30845437508089⟩,⟨-101590940954154,-92409783743872⟩,⟨131714856171737,160802333358650⟩,⟨-297679828043581,-191619089009364⟩,⟨1512523441930529,1744297036306240⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8405118703748,8917231250226⟩,⟨61900649997796,67616874990406⟩,⟨-68815233226131,-60451913986180⟩,⟨92711029477900,163241050034789⟩,⟨-641343110317402,-511007968265842⟩,⟨967486098777511,1174022703563449⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨93480623616,99111729408⟩,⟨-788521050891,-641748472999⟩,⟨626728854897,802495827092⟩,⟨6845795772025,11530689361922⟩,⟨-7415430246965,-1065586125097⟩,⟨-5346292389128,2908255296120⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1192992251392,1198623357184⟩,⟨-788521050891,-641748472999⟩,⟨626728854897,802495827092⟩,⟨6845795772025,11530689361922⟩,⟨-7415430246965,-1065586125097⟩,⟨-5346292389128,2908255296120⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨89718545216,94896198208⟩,⟨-726734027979,-588683596010⟩,⟨574905919605,739613767064⟩,⟨5799388165784,10311982370796⟩,⟨-6526563832883,-488619305290⟩,⟨-5424886541820,2379766600827⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨97346427763,103450292664⟩,⟨-860298341953,-691099292410⟩,⟨674924657209,875545210481⟩,⟨7538250046985,13279069817683⟩,⟨-8815723086154,-1288219095008⟩,⟨-5719919758123,3924924500895⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-99111729408,-93480623616⟩,⟨641748472999,788521050891⟩,⟨-802495827092,-626728854897⟩,⟨-11530689361922,-6845795772025⟩,⟨1065586125097,7415430246965⟩,⟨-2908255296120,5346292389128⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1000399898368,1006031004160⟩,⟨641748472999,788521050891⟩,⟨-802495827092,-626728854897⟩,⟨-11530689361922,-6845795772025⟩,⟨1065586125097,7415430246965⟩,⟨-2908255296120,5346292389128⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-103866782144,-97695144128⟩,⟨701379883176,866641495682⟩,⟨-882000782456,-684964638835⟩,⟨-13356150989646,-7929319761270⟩,⟨1601540448859,8845290748036⟩,⟨-3903901298282,5449247267888⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-95036014627,-88888748229⟩,⟨563667726634,735938105741⟩,⟨-751326085299,-547412033330⟩,⟨-10793593946044,-4882263017438⟩,⟨-508396936707,7198999920731⟩,⟨-3296166799036,6548167871113⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2310413136,14561544435⟩,⟨-296630615319,44838813331⟩,⟨-76401428090,328133177151⟩,⟨-3255343899059,8396806800245⟩,⟨-9324120022861,5910780825723⟩,⟨-9016086557159,10473092372008⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1155206568,7280772218⟩,⟨-148315307660,22419406666⟩,⟨-38200714045,164066588576⟩,⟨-1627671949530,4198403400123⟩,⟨-4662060011431,2955390412862⟩,⟨-4508043278580,5236546186004⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7280772218,-1155206568⟩,⟨-22419406666,148315307660⟩,⟨-164066588576,38200714045⟩,⟨-4198403400123,1627671949530⟩,⟨-2955390412862,4662060011431⟩,⟨-5236546186004,4508043278580⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754842611398,760968196312⟩,⟨-22419406666,148315307660⟩,⟨-164066588576,38200714045⟩,⟨-4198403400123,1627671949530⟩,⟨-2955390412862,4662060011431⟩,⟨-5236546186004,4508043278580⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7947734949,8934089153⟩,⟨-142157086936,-109123079638⟩,⟨106569139814,144676504108⟩,⟨1913195520523,3209774170729⟩,⟨-2487906329400,-912794241420⟩,⟨-249367489319,1695737891094⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8934089153,-7947734949⟩,⟨109123079638,142157086936⟩,⟨-144676504108,-106569139814⟩,⟨-3209774170729,-1913195520523⟩,⟨912794241420,2487906329400⟩,⟨-1695737891094,249367489319⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090577538623,1091563892827⟩,⟨109123079638,142157086936⟩,⟨-144676504108,-106569139814⟩,⟨-3209774170729,-1913195520523⟩,⟨912794241420,2487906329400⟩,⟨-1695737891094,249367489319⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8970584000,-7976598912⟩,⟨109917610603,143321647954⟩,⟨-145861704372,-107345075407⟩,⟨-3254750887041,-1938114006060⟩,⟨930171576846,2527300549819⟩,⟨-1728979576062,240930249806⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4485292000,-3988299456⟩,⟨54958805301,71660823977⟩,⟨-72930852186,-53672537703⟩,⟨-1627375443521,-969057003030⟩,⟨465085788423,1263650274910⟩,⟨-864489788031,120465124903⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3988299456,4485292000⟩,⟨-71660823977,-54958805301⟩,⟨53672537703,72930852186⟩,⟨969057003030,1627375443521⟩,⟨-1263650274910,-465085788423⟩,⟨-120465124903,864489788031⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766111683072,766608694880⟩,⟨-71660823977,-54958805301⟩,⟨53672537703,72930852186⟩,⟨969057003030,1627375443521⟩,⟨-1263650274910,-465085788423⟩,⟨-120465124903,864489788031⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272644384655,272890973207⟩,⟨27280769909,35539271734⟩,⟨-36169126027,-26642284953⟩,⟨-802443542683,-478298880130⟩,⟨228198560355,621976582350⟩,⟨-423934472774,62341872330⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532223366144,1533217389760⟩,⟨-143321647954,-109917610602⟩,⟨107345075406,145861704372⟩,⟨1938114006060,3254750887042⟩,⟨-2527300549820,-930171576846⟩,⟨-240930249806,1728979576062⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1201678491632,1208442565405⟩,⟨-952501497821,-766552257187⟩,⟨748611704708,969382461555⟩,⟨9155098580760,15430140309568⟩,⟨-10485685297396,-2227896312311⟩,⟨-5525376877097,5068283453126⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1303845355488,1317373503034⟩,⟨-1905002995643,-1533104514375⟩,⟨1497223409417,1938764923109⟩,⟨18310197161527,30860280619127⟩,⟨-20971370594786,-4455792624621⟩,⟨-11045976825107,10136566906250⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨187413689408,198762980288⟩,⟨-1606458109348,-1279565921332⟩,⟨1249618687668,1634928994848⟩,⟨12934991238690,24534868182550⟩,⟨-16230562194691,-1330173992401⟩,⟨-11745965794093,7127783762692⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨64176818382,68594885271⟩,⟨-547753614245,-427207220653⟩,⟨415476026443,558848060723⟩,⟨4108631266166,8159227596492⟩,⟨-5442356252648,-85394830119⟩,⟨-4411674244992,2474918419391⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379943318708,380533661546⟩,⟨2445675917,22301728803⟩,⟨-23817939080,-925491869⟩,⟨-647643525875,135818611753⟩,⟨-303925324013,646093114834⟩,⟨-660550337541,510851101136⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176922153754,3181858345939⟩,⟨-186767179279,-20417962421⟩,⟨7726558564,199464774121⟩,⟨-1137158743330,5445655491451⟩,⟨-5434162114776,2545141726287⟩,⟨-4278115919139,5556826979548⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨185432105422,198505593461⟩,⟨-1596786825976,-1235561688555⟩,⟨1200924870050,1629685020290⟩,⟨11816376917985,24137675912172⟩,⟨-16282860467760,-98673843613⟩,⟨-13027928604918,7711560776253⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨372845794830,397268573749⟩,⟨-3203244935324,-2515127609887⟩,⟨2450543557718,3264614015138⟩,⟨24751368156675,48672544094722⟩,⟨-32513422662451,-1428847836014⟩,⟨-24773894399011,14839344538945⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518218592316,526663457821⟩,⟨-31032787690,205297023342⟩,⟨-227099837474,52877164244⟩,⟨-5817449353308,2293025351006⟩,⟨-4135093510624,6463497172544⟩,⟨-7259791467556,6288965611176⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355770203440,364501958358⟩,⟨-32216527609,213128040142⟩,⟨-235762518567,54894153847⟩,⟨-6045633989260,2422031761807⟩,⟨-4338776806381,6720745129511⟩,⟨-7548550176517,6579688006342⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711540406880,729003916716⟩,⟨-64433055218,426256080284⟩,⟨-471525037134,109788307694⟩,⟨-12091267978520,4844063523614⟩,⟨-8677553612762,13441490259022⟩,⟨-15097100353034,13159376012684⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523289276991,1525269654811⟩,⟨-34198568316,32239476334⟩,⟨-37331428702,39292564558⟩,⟨-1271660164669,1341555366519⟩,⟨-1614506308400,1557734752554⟩,⟨-1936668140900,1978347065381⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨985784819882,1011292217668⟩,⟨-112057636343,612688535473⟩,⟨-678862841928,178353009360⟩,⟨-17642964005031,7634286485750⟩,⟨-13136473257578,19709083170793⟩,⟨-22260831028816,19598724133441⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67607252716,67729600467⟩,⟨13529549914,17641189426⟩,⟨-17953840146,-13212901442⟩,⟨-396967805319,-234908773597⟩,⟨110833992344,307418254716⟩,⟨-209143908259,33325231726⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50323791047,51037456712⟩,⟨259154357524,267262932245⟩,⟨32802561841,37862908766⟩,⟨-1380028051018,-1175688636717⟩,⟨-289049636890,-101781463766⟩,⟨-270336581435,-75201222027⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135228390905,2137999730860⟩,⟨-399710630468,-306351160024⟩,⟨299181252152,406794609524⟩,⟨5423690613417,9114558914230⟩,⟨-7086430363376,-2613941867392⟩,⟨-650971712291,4860661991846⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2975545460320,2981340336789⟩,⟨-836066587234,-640373044417⟩,⟨625385617139,850884001988⟩,⟨11383206869316,19142890887752⟩,⟨-14902080790673,-5508847737473⟩,⟨-1317820252211,10247896052603⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136188398751,138388739636⟩,⟨662525835466,695377603872⟩,⟨117395110549,142162364311⟩,⟨-3627416286489,-2594989792223⟩,⟨-1356878920132,-339857795480⟩,⟨-756876987051,330779387730⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8735723894837,8876863453142⟩,⟨-45325241316855,-41821630770321⟩,⟨-9266251073794,-7410510963950⟩,⟨564243422358476,699298878171445⟩,⟨92407907129581,183069307387815⟩,⟨-8987785408037,68679256622134⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7832153647733,8164627549799⟩,⟨-42593259553869,-32549338618439⟩,⟨-14003544810378,-5204086760645⟩,⟨312927938151119,714064400046667⟩,⟨-35722756607834,356430411805779⟩,⟨-190994762635890,232840668833425⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15664307295466,16329255099598⟩,⟨-85186519107738,-65098677236878⟩,⟨-28007089620756,-10408173521290⟩,⟨625855876302238,1428128800093334⟩,⟨-71445513215668,712860823611558⟩,⟨-381989525271780,465681337666850⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10825960642717,10867759718598⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790014,2123491006166466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9726449014941,9768248090822⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790024,2123491006166451⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2396916401408,2401631448192⟩,⟨-12142992897062,-11998203029636⟩,⟨0,0⟩,⟨102165241571294,109118793444233⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7337018667741,7428158468408⟩,⟨-44283175834065,-43031053065424⟩,⟨-20014662473039,-19507410722992⟩,⟨504747667076467,527990798874534⟩,⟨277778718340214,288819626288709⟩,⟨103731253891626,107856264944627⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6237507039965,6328646840632⟩,⟨-44283175834065,-43031053065424⟩,⟨-20014662473040,-19507410722992⟩,⟨504747667076468,527990798874532⟩,⟨277778718340213,288819626288710⟩,⟨103731253891625,107856264944628⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1908438254464,1924387648576⟩,⟨-7805981850214,-7476028350481⟩,⟨-3528068822077,-3389132852218⟩,⟨32274107042031,42238592840920⟩,⟨23212547063397,27867353925115⟩,⟨6701091961473,8565620341917⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99941875711,100371372442⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138359797487,140381452018⟩,⟨676152345229,683578612781⟩,⟨306720636271,308761928666⟩,⟨-1712309844053,-1698693120000⟩,⟨-1547926010598,-1540044410060⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4305354655872,4326019096768⟩,⟨-19948974747276,-19474231380117⟩,⟨-3528068822077,-3389132852218⟩,⟨134439348613325,151357386285153⟩,⟨23212547063397,27867353925115⟩,⟨6701091961473,8565620341917⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨745691589660,794537147498⟩,⟨-6406489870648,-5030255219774⟩,⟨4901087115436,6529228030276⟩,⟨49502736313350,97345088189444⟩,⟨-65026845324902,-2857695672028⟩,⟨-49547788798022,29678689077890⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5051046245532,5120556244266⟩,⟨-26355464617924,-24504486599891⟩,⟨1373018293359,3140095178058⟩,⟨183942084926675,248702474474597⟩,⟨-41814298261505,25009658253087⟩,⟨-42846696836549,38244309419807⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459122962712,467441403001⟩,⟨1619135078473,1857069017128⟩,⟨124802703452,286650595281⟩,⟨-35566603334711,-26452757661165⟩,⟨-2722987570617,4787779005703⟩,⟨-3911356330801,3491217125486⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37654771073,39735973067⟩,⟨-804256656212,-762185055152⟩,⟨322945996948,325509439814⟩,⟨9387435314787,10111501779339⟩,⟨-6594864009033,-6530061933853⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨496777733785,507177376068⟩,⟨814878422261,1094883961976⟩,⟨447748700400,612160035095⟩,⟨-26179168019924,-16341255881826⟩,⟨-9317851579650,-1742282928150⟩,⟨-3911356330801,3491217125486⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503376910943,504367118897⟩,⟨2514798172912,2555168940688⟩,⟨0,0⟩,⟨2165995870996,4475808627517⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227434103233,232652011562⟩,⟨1509294379736,1680880221263⟩,⟨204987698167,280809575275⟩,⟨-7302681746528,-327922902796⟩,⟨-3250188767060,624956837824⟩,⟨-1794214334537,1601488404982⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-794537147498,-745691589660⟩,⟨5030255219774,6406489870648⟩,⟨-6529228030276,-4901087115436⟩,⟨-97345088189444,-49502736313350⟩,⟨2857695672028,65026845324902⟩,⟨-29678689077890,49547788798022⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3510817508374,3580327507108⟩,⟨-14918719527502,-13067741509469⟩,⟨-10057296852353,-8290219967654⟩,⟨37094260423881,101854649971803⟩,⟨26070242735425,92894199250017⟩,⟨-22977597116417,58113409139939⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441792507874,457122563738⟩,⟨254236494981,581517489763⟩,⟨-304696873636,-37802537458⟩,⟨-19458194286322,-8491830181965⟩,⟨-12202048505606,-1800608486288⟩,⟨-9721220168131,1679704098743⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨325498123056,329541432116⟩,⟨1932735283200,1940466224334⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-329541432116,-325498123056⟩,⟨-1940466224334,-1932735283200⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨769970195660,774013504720⟩,⟨-1940466224334,-1932735283200⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1336448418619,1354694203032⟩,⟨-8891351721334,-8590018262103⟩,⟨-4018623332221,-3894141612153⟩,⟨48883946925579,57287006289200⟩,⟨31987167670548,35919291115988⟩,⟨10094096716454,11658236510131⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1354694203032,-1336448418619⟩,⟨8590018262103,8891351721334⟩,⟨3894141612153,4018623332221⟩,⟨-57287006289200,-48883946925579⟩,⟨-35919291115988,-31987167670548⟩,⟨-11658236510131,-10094096716454⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-255182575256,-236936790843⟩,⟨8590018262103,8891351721334⟩,⟨3894141612153,4018623332221⟩,⟨-57287006289200,-48883946925579⟩,⟨-35919291115988,-31987167670548⟩,⟨-11658236510131,-10094096716454⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12423874556,-11007350973⟩,⟨426924281851,463787305527⟩,⟨79135795179,101247070067⟩,⟨-4942461936810,-4290993564533⟩,⟨1424117575906,1857412898417⟩,⟨2535548649896,2736539482953⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429368633318,446115212765⟩,⟨681160776832,1045304795290⟩,⟨-225561078457,63444532609⟩,⟨-24400656223132,-12782823746498⟩,⟨-10777930929700,56804412129⟩,⟨-7185671518235,4416243581696⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100371372442,-99941875711⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4642990643,4886702547⟩,⟨28549958859,30948408690⟩,⟨39820591103,40030926275⟩,⟨-319468391631,-308197457915⟩,⟨248728938086,249843280775⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10121639592,10673883039⟩,⟨8269735490,16933997524⟩,⟨86808202403,87438394478⟩,⟨-949972390287,-809985851132⟩,⟨100123741306,111191132797⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1459114306552,1477133557231⟩,⟨-7441195029237,-7133958836061⟩,⟨-1397530613176,-1326976067312⟩,⟨102213138136826,109562088523717⟩,⟨21487269201396,23265755399771⟩,⟨4767987831596,5206654984715⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13431989950,14339776338⟩,⟨-61263523138,-42922314788⟩,⟨101632405624,105253105334⟩,⟨-564514181634,-118598955142⟩,⟨-282610515807,-197978604937⟩,⟨-178384481561,-158988393866⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14339776338,-13431989950⟩,⟨42922314788,61263523138⟩,⟨-105253105334,-101632405624⟩,⟨118598955142,564514181634⟩,⟨197978604937,282610515807⟩,⟨158988393866,178384481561⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114711148780,-113373865661⟩,⟨-834110007056,-814909805246⟩,⟨-105253105334,-101632405624⟩,⟨2317622210694,2763537437186⟩,⟨197978604937,282610515807⟩,⟨158988393866,178384481561⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨88660142659,93691157081⟩,⟨-613075052933,-571703761729⟩,⟨588625038296,610051280548⟩,⟨3257390051444,3946948579501⟩,⟨-3560761676828,-3103185140839⟩,⟨-2502874125714,-2283687580091⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨117657039095,125868930027⟩,⟨-1457708918810,-1333936730567⟩,⟨662052984231,712568481228⟩,⟨19983561323995,22936720701468⟩,⟨-6489726325877,-5175517735131⟩,⟨-4528810277061,-4007712383685⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-125868930027,-117657039095⟩,⟨1333936730567,1457708918810⟩,⟨-712568481228,-662052984231⟩,⟨-22936720701468,-19983561323995⟩,⟨5175517735131,6489726325877⟩,⟨4007712383685,4528810277061⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨973642697749,981854588681⟩,⟨1333936730567,1457708918810⟩,⟨-712568481228,-662052984231⟩,⟨-22936720701468,-19983561323995⟩,⟨5175517735131,6489726325877⟩,⟨4007712383685,4528810277061⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122520765658,125359449912⟩,⟨766607635704,796544638730⟩,⟨180630113115,192410697899⟩,⟨-2816923858256,-2206365360274⟩,⟨-801906318782,-532945205108⟩,⟨-208237838068,-100288735353⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11690311489,11967720325⟩,⟨168055475634,174044029552⟩,⟨20959230280,21961940776⟩,⟨631315627413,787589150974⟩,⟨91681917088,118865625472⟩,⟨-18432807214,-12636360451⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166547244174,177737054535⟩,⟨1467000562911,1892645325549⟩,⟨-6247493654,215502352985⟩,⟨-11320333186285,7341270152348⟩,⟨-5606338362775,6692732649579⟩,⟨-5550389599967,4491912082191⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177737054535,-166547244174⟩,⟨-1892645325549,-1467000562911⟩,⟨-215502352985,6247493654⟩,⟨-7341270152348,11320333186285⟩,⟨-6692732649579,5606338362775⟩,⟨-4491912082191,5550389599967⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49697048698,66104767388⟩,⟨-383350945813,213879658352⟩,⟨-10514654818,287057068929⟩,⟨-14643951898876,10992410283489⟩,⟨-9942921416639,6231295200599⟩,⟨-6286126416728,7151878004949⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27188765009074,28579794911014⟩,⟨-265024713490758,-219500735861777⟩,⟨-101415237753262,-66349252819627⟩,⟨2431368502323348,4336404367767077⟩,⟨477084061562381,2133711341855814⟩,⟨-508933767372178,1121992221127691⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13652732393,14292701674⟩,⟨170849224532,181634091390⟩,⟨40255944912,43874932538⟩,⟨426660775345,662399158006⟩,⟨69023169904,160010777586⟩,⟨11864643843,44991655203⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337605281642,371512653662⟩,⟨779673656890,1995686283397⟩,⟨-322859988933,316584173970⟩,⟨-46820644448549,5372480735779⟩,⟨-19698063824353,13549330970847⟩,⟨-14416061208078,10895972666384⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371512653662,-337605281642⟩,⟨-1995686283397,-779673656890⟩,⟨-316584173970,322859988933⟩,⟨-5372480735779,46820644448549⟩,⟨-13549330970847,19698063824353⟩,⟨-10895972666384,14416061208078⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57855979656,108509931123⟩,⟨-1314525506565,265631138400⟩,⟨-542145252427,386304521542⟩,⟨-29773136958911,34037820702051⟩,⟨-24327261900547,19754868236482⟩,⟨-18081644184619,18832304789774⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238301673198,240752824460⟩,⟨1552325673613,1560610934625⟩,⟨306720636271,308761928666⟩,⟨-3911333099605,-3897716375552⟩,⟨-1547926010598,-1540044410060⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1703617828022,-1615192623820⟩,⟨-5675161809070,-2722257831958⟩,⟨-489935646734,1474040065215⟩,⟨-19480692557090,105756647693967⟩,⟨-57820242057783,41052367571374⟩,⟨-44394967267182,47863986109385⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-194235866531,-179984123820⟩,⟨-1881237776528,-1429500218766⟩,⟨-353986577839,-97286442377⟩,⟨-7202673508233,12626287210780⟩,⟨-7157470491670,6543688040002⟩,⟨-5085785932633,6295706787595⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44065806667,60768700640⟩,⟨-328912102915,131110715859⟩,⟨-47265941568,211475486289⟩,⟨-11114006607838,8728570835228⟩,⟨-8705396502268,5003643629942⟩,⟨-5435571089119,5946606477067⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2615044139,6523827102⟩,⟨-116864419001,37077872196⟩,⟨-33632504959,51554810231⟩,⟨-3746627987745,4047885427205⟩,⟨-2921740588006,2061034659955⟩,⟨-1990559468612,2039758150715⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1766052552,3358613847⟩,⟨-36357161880,14492666820⟩,⟨-5224664808,23375997480⟩,⟨-1306957786676,1161619510723⟩,⟨-1088797000028,603525448700⟩,⟨-619016973907,738672370300⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3065362988,5878314372⟩,⟨-87477521440,13357248533⟩,⟨-19921300213,35469469460⟩,⟨-2441406323763,2678349167669⟩,⟨-2080811699397,1295181216671⟩,⟨-1222668646802,1352533718882⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5878314372,-3065362988⟩,⟨-13357248533,87477521440⟩,⟨-35469469460,19921300213⟩,⟨-2678349167669,2441406323763⟩,⟨-1295181216671,2080811699397⟩,⟨-1352533718882,1222668646802⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3263270233,3458464114⟩,⟨-130221667534,124555393636⟩,⟨-69101974419,71476110444⟩,⟨-6424977155414,6489291750968⟩,⟨-4216921804677,4141846359352⟩,⟨-3343093187494,3262426797517⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49697048698,66104767388⟩,⟨-383350945813,213879658352⟩,⟨-10514654818,287057068929⟩,⟨-14643951898876,10992410283489⟩,⟨-9942921416639,6231295200599⟩,⟨-6286126416728,7151878004949⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3263270233,3458464114⟩,⟨-130221667534,124555393636⟩,⟨-69101974419,71476110444⟩,⟨-6424977155414,6489291750968⟩,⟨-4216921804677,4141846359352⟩,⟨-3343093187494,3262426797517⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (519/5120) u, BivariateJet2.affineZ (611/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000027

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000028Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2085925931520,-2085925892736⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2085925931456,-2085925892736⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-178687850560,-178687850496⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-178687850560,-178687850496⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨94840999744,94840999808⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-103800650176,-103800650112⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨94841122112,94841122176⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-103800796800,-103800796736⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8959674624,-8959674560⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8959650432,-8959650368⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨198641649920,198641649984⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨198641918848,198641918912⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1907238042176,1907238080768⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1907238042240,1907238080832⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2518909148864,-2518909091008⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2092693238080,-2092693199360⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2079195019264,-2079194980608⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-179879921728,-179879921664⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-177497957696,-177497957632⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨92256767424,92256767488⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-100712684544,-100712684480⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨97446999872,97446999936⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-106930823744,-106930823680⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9483823872,-9483823808⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8455917120,-8455917056⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨192969451968,192969452032⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨204377823616,204377823680⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1899315058880,1899315097472⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1915195241664,1915195280256⟩



end LaneCBRB2Cell000028Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000028
open Set LaneCBRB2Cell000028Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111024904601,111024904602⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨135076721459,135076721460⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111024904602,-111024904601⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438730909286,438730909287⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨53898777722,53898777724⟩,⟨-135076721460,-135076721459⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨164923682323,164923682326⟩,⟨964434906316,964434906317⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨53898777721,53898777725⟩,⟨-135076721460,-135076721459⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2085925931520,-2085925892736⟩,⟨6429685408256,6429685408381⟩,⟨2924927029407,2924927029468⟩,⟨-37599288089718,-37599288088263⟩,⟨-24434498966441,-24434498965623⟩,⟨-7780907369769,-7780907369447⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312883080993,-312883075169⟩,⟨-865231765276,-865231731217⟩,⟨-393602426290,-393602410793⟩,⟨5639788509245,5639788509799⟩,⟨3552009438480,3552009477568⟩,⟨1167114437661,1167114437786⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨312883075169,312883080993⟩,⟨865231731217,865231765276⟩,⟨393602410793,393602426290⟩,⟨-5639788509799,-5639788509245⟩,⟨-3552009477568,-3552009438480⟩,⟨-1167114437786,-1167114437661⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164923682326,-164923682323⟩,⟨-964434906317,-964434906316⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨934587945450,934587945453⟩,⟨-964434906317,-964434906316⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-178687850560,-178687850496⟩,⟨-1134625584346,-1134625584340⟩,⟨-516152319934,-516152319930⟩,⟨-1170860938740,-1170860938726⟩,⟨760902715203,760902715216⟩,⟨-242301409684,-242301409679⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151885170574,-151885170518⟩,⟨-807699137459,-807699137393⟩,⟨-367430268945,-367430268913⟩,⟨995235058440,995235058469⟩,⟨1373565978145,1373565978232⟩,⟨205956872967,205956872978⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151885170518,151885170574⟩,⟨807699137393,807699137459⟩,⟨367430268913,367430268945⟩,⟨-995235058469,-995235058440⟩,⟨-1373565978232,-1373565978145⟩,⟨-205956872978,-205956872967⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨464768245687,464768251567⟩,⟨1672930868610,1672930902735⟩,⟨761032679706,761032695235⟩,⟨-6635023568268,-6635023567685⟩,⟨-4925575455800,-4925575416625⟩,⟨-1373071310764,-1373071310628⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨824554197831,824554209615⟩,⟨4076925814134,4076925906203⟩,⟨761032679706,761032695235⟩,⟨-18746810732470,-18746810731380⟩,⟨-4925575455800,-4925575416625⟩,⟨-1373071310764,-1373071310628⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨107797555442,107797555450⟩,⟨-270153442920,-270153442918⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11214779542708,11214779543541⟩,⟨28105565960019,28105565964403⟩,⟨-91287235715443,-91287235701672⟩,⟨140871754977406,140871755010885⟩,⟨-228776626026097,-228776625885715⟩,⟨1486138781474523,1486138781812474⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8410273539711,8410273660530⟩,⟨62660898595129,62660899841812⟩,⟨-60696457481378,-60696456333710⟩,⟨122857875048607,122857881348249⟩,⟨-540840132935002,-540840121879405⟩,⟨974121700621555,974121719402758⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨99051556864,99051690240⟩,⟨-729373448712,-729371439900⟩,⟨706505376487,706507321624⟩,⟨9248436854016,9248486007891⟩,⟨-4048405672322,-4048344586347⟩,⟨-1319336759194,-1319263174599⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1198563184640,1198563318016⟩,⟨-729373448712,-729371439900⟩,⟨706505376487,706507321624⟩,⟨9248436854016,9248486007891⟩,⟨-4048405672322,-4048344586347⟩,⟨-1319336759194,-1319263174599⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨94840999744,94841122176⟩,⟨-669096630139,-669094712881⟩,⟨648118347072,648120203583⟩,⟨8076955420939,8077003790220⟩,⟨-3319432969609,-3319374258712⟩,⟨-1592346403820,-1592276577037⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨103384928195,103385073162⟩,⟨-792287458766,-792285033131⟩,⟨767446605387,767448954220⟩,⟨10490029632951,10490093597714⟩,⟨-4827551735716,-4827476781856⟩,⟨-1016685177413,-1016597693848⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-99051690240,-99051556864⟩,⟨729371439900,729373448712⟩,⟨-706507321624,-706505376487⟩,⟨-9248486007891,-9248436854016⟩,⟨4048344586347,4048405672322⟩,⟨1319263174599,1319336759194⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1000459937536,1000460070912⟩,⟨729371439900,729373448712⟩,⟨-706507321624,-706505376487⟩,⟨-9248486007891,-9248436854016⟩,⟨4048344586347,4048405672322⟩,⟨1319263174599,1319336759194⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-103800796800,-103800650112⟩,⟨801583593842,801585908403⟩,⟨-776455894025,-776453652793⟩,⟨-10748529731176,-10748470980934⟩,⟨5015217708899,5015288704344⟩,⟨901558572513,901642801160⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-94449708311,-94449562245⟩,⟨660513912483,660516402721⟩,⟨-639808969399,-639806557994⟩,⟨-7843643014899,-7843576379378⟩,⟨3151075393199,3151152718918⟩,⟨1693626824699,1693716325179⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8935219884,8935510917⟩,⟨-131773546283,-131768630410⟩,⟨127637635988,127642396226⟩,⟨2646386618052,2646517218336⟩,⟨-1676476342517,-1676324062938⟩,⟨676941647286,677118631331⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4467609942,4467755459⟩,⟨-65886773142,-65884315205⟩,⟨63818817994,63821198113⟩,⟨1323193309026,1323258609168⟩,⟨-838238171259,-838162031469⟩,⟨338470823643,338559315666⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4467755459,-4467609942⟩,⟨65884315205,65886773142⟩,⟨-63821198113,-63818817994⟩,⟨-1323258609168,-1323193309026⟩,⟨838162031469,838238171259⟩,⟨-338559315666,-338470823643⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757655628157,757655792938⟩,⟨65884315205,65886773142⟩,⟨-63821198113,-63818817994⟩,⟨-1323258609168,-1323193309026⟩,⟨838162031469,838238171259⟩,⟨-338559315666,-338470823643⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8923244347,8923268379⟩,⟨-131414113478,-131413574588⟩,⟨127293710600,127294232470⟩,⟨2633996275634,2634012705910⟩,⟨-1666756554796,-1666739404288⟩,⟨670238134281,670256711877⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8923268379,-8923244347⟩,⟨131413574588,131414113478⟩,⟨-127294232470,-127293710600⟩,⟨-2634012705910,-2633996275634⟩,⟨1666739404288,1666756554796⟩,⟨-670256711877,-670238134281⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090588359397,1090588383429⟩,⟨131413574588,131414113478⟩,⟨-127294232470,-127293710600⟩,⟨-2634012705910,-2633996275634⟩,⟨1666739404288,1666756554796⟩,⟨-670256711877,-670238134281⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8959674624,-8959650368⟩,⟨132488806503,132489352723⟩,⟨-128335762567,-128335233598⟩,⟨-2671529127913,-2671512373046⟩,⟨1695840864784,1695858320145⟩,⟨-690720237575,-690701369600⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4479837312,-4479825184⟩,⟨66244403251,66244676362⟩,⟨-64167881284,-64167616799⟩,⟨-1335764563957,-1335756186523⟩,⟨847920432392,847929160073⟩,⟨-345360118788,-345350684800⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4479825184,4479837312⟩,⟨-66244676362,-66244403251⟩,⟨64167616799,64167881284⟩,⟨1335756186523,1335764563957⟩,⟨-847929160073,-847920432392⟩,⟨345350684800,345360118788⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766603208800,766603240192⟩,⟨-66244676362,-66244403251⟩,⟨64167616799,64167881284⟩,⟨1335756186523,1335764563957⟩,⟨-847929160073,-847920432392⟩,⟨345350684800,345360118788⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272647089849,272647095858⟩,⟨32853393647,32853528370⟩,⟨-31823558118,-31823427650⟩,⟨-658503176478,-658499068908⟩,⟨416684851072,416689138699⟩,⟨-167564177970,-167559533570⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533206417600,1533206480384⟩,⟨-132489352724,-132488806502⟩,⟨128335233598,128335762568⟩,⟨2671512373046,2671529127914⟩,⟨-1695858320146,-1695840864784⟩,⟨690701369600,690720237576⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1208369883780,1208370044874⟩,⟨-880947845970,-880945184809⟩,⟨853327228638,853329805528⟩,⟨12454874956580,12454944892819⟩,⟨-6133943119546,-6133860685338⟩,⟨-388308032348,-388211612616⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1317228139784,1317228461972⟩,⟨-1761895691939,-1761890369618⟩,⟨1706654457276,1706659611056⟩,⟨24909749913166,24909889785630⟩,⟨-12267886239090,-12267721370677⟩,⟨-776615918498,-776423371430⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨198641649920,198641918912⟩,⟨-1470682823809,-1470678021457⟩,⟨1424571723541,1424576373931⟩,⟨18825412618328,18825547304955⟩,⟨-8334733103493,-8334580538091⟩,⟨-2493998642864,-2493825711703⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨68254821176,68254927929⟩,⟨-496664210586,-496662487614⟩,⟨481091935645,481093604052⟩,⟨6166325971510,6166370773644⟩,⟨-2629514264834,-2629461212459⟩,⟨-1021652040788,-1021589839507⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380190856864,380190880813⟩,⟨12958659433,12958985345⟩,⟨-12552716335,-12552400715⟩,⟨-263705031959,-263695032148⟩,⟨168188796761,168199200164⟩,⟨-69813692214,-69802462727⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179786472072,3179786672375⟩,⟨-108384534093,-108381794621⟩,⟨104983985676,104986638641⟩,⟨2212843347814,2212927633715⟩,⟨-1413917788669,-1413830239634⟩,⟨590736233152,590830576233⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨197392871113,197393192278⟩,⟨-1443080705969,-1443075452071⟩,⟨1397834505000,1397839592560⟩,⟨18068290480227,18068429433005⟩,⟨-7787173201939,-7787010997381⟩,⟨-2826073841230,-2825885214905⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨396034521033,396035111190⟩,⟨-2913763529778,-2913753473528⟩,⟨2822406228541,2822415966491⟩,⟨36893703098555,36893976737960⟩,⟨-16121906305432,-16121591535472⟩,⟨-5320072484094,-5319710926608⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522088203868,522088430965⟩,⟨90799625872,90803033072⟩,⟨-87956323956,-87953024622⟩,⟨-1815776718652,-1815685738342⟩,⟨1147478920114,1147584675338⟩,⟨-459183111595,-459060500672⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359762512794,359762747527⟩,⟨93852824070,93856366252⟩,⟨-90913933998,-90910503947⟩,⟨-1868672569116,-1868577509427⟩,⟨1178157667571,1178267829502⟩,⟨-466965985001,-466838574013⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨719525025588,719525495054⟩,⟨187705648140,187712732504⟩,⟨-181827867996,-181821007894⟩,⟨-3737345138232,-3737155018854⟩,⟨2356315335142,2356535659004⟩,⟨-933931970002,-933677148026⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524283149221,1524283236037⟩,⟨-1075778136,-1074693024⟩,⟨1041001128,1042051968⟩,⟨37499667136,37532852280⟩,⟨-29118915858,-29084309988⟩,⟨20444657723,20482103295⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨997497292652,997498000299⟩,⟨259517498013,259528044645⟩,⟨-251391743103,-251381530278⟩,⟨-5157011825799,-5156725846107⟩,⟨3247924506302,3248253164315⟩,⟨-1281701180031,-1281322965753⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67608594329,67608597310⟩,⟨16293383248,16293450424⟩,⟨-15782644734,-15782579680⟩,⟨-324616181764,-324614121343⟩,⟨204749805304,204751951872⟩,⟨-81259997290,-81257676996⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50701555904,50701558865⟩,⟨262907634378,262907701647⟩,⟨34959797229,34959849204⟩,⟨-1275343845296,-1275341744857⟩,⟨-196568009519,-196566092522⟩,⟨-167216890521,-167215055362⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137969130644,2137969305742⟩,⟨-369497746176,-369496207692⟩,⟨357912365428,357913855322⟩,⟨7482473299933,7482520595729⟩,⟨-4760484604734,-4760435475048⟩,⟨1956246168807,1956299115296⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2981276331169,2981276697416⟩,⟨-772865413080,-772862163438⟩,⟨748632649827,748635796844⟩,⟨15717610305556,15717710426819⟩,⟨-10022029920177,-10021926213595⟩,⟨4154474410067,4154585843069⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137474988669,137475013587⟩,⟨677223239488,677223661393⟩,⟨129313462973,129313762682⟩,⟨-3102859526245,-3102847098347⟩,⟨-840695234270,-840684223594⟩,⟨-214220027645,-214209575415⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8793785780203,8793787374120⟩,⟨-43319595372745,-43319552681210⟩,⟨-8271742697219,-8271720527316⟩,⟨625275721373661,625277352154016⟩,⟨135271124760498,135272132536093⟩,⟨29263519715790,29264273869515⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7977885168578,7977892274302⟩,⟨-37224770925909,-37224619587661⟩,⟨-9514890130887,-9514782648635⟩,⟨505566162233254,505571190055202⟩,⟨156648747449455,156652878777999⟩,⟨20079814534250,20083708131338⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15955770337156,15955784548604⟩,⟨-74449541851818,-74449239175322⟩,⟨-19029780261774,-19029565297270⟩,⟨1011132324466508,1011142380110404⟩,⟨313297494898910,313305757555998⟩,⟨40159629068500,40167416262676⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10888780530353,10888780530452⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239700,2135836853297982⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9789268902577,9789268902676⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239713,2135836853297977⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2403994945600,2403995003456⟩,⟨-12111787164150,-12111787163733⟩,⟨0,0⟩,⟨106474359377039,106474359411671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7330213602828,7330213602962⟩,⟨-42865365179095,-42865365177481⟩,⟨-19499875542417,-19499875541658⟩,⟨501333148351915,501333148380465⟩,⟨276930370027113,276930370042173⟩,⟨103747357646842,103747357653010⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6230701975052,6230701975186⟩,⟨-42865365179096,-42865365177481⟩,⟨-19499875542418,-19499875541658⟩,⟨501333148351919,501333148380465⟩,⟨276930370027114,276930370042175⟩,⟨103747357646842,103747357653012⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1907238042176,1907238080832⟩,⟨-7564310992898,-7564310992417⟩,⟨-3441079349479,-3441079349255⟩,⟨36428427142308,36428427158138⟩,⟨25195401677310,25195401685131⟩,⟨7538605958233,7538605961599⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99813991382,99813991384⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨140185589242,140185589246⟩,⟨675109805797,675109805805⟩,⟨307114079992,307114079997⟩,⟨-1691905142294,-1691905142289⟩,⟨-1539328526260,-1539328526248⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4311232987776,4311233084288⟩,⟨-19676098157048,-19676098156150⟩,⟨-3441079349479,-3441079349255⟩,⟨142902786519347,142902786569809⟩,⟨25195401677310,25195401685131⟩,⟨7538605958233,7538605961599⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨792069042066,792070222380⟩,⟨-5827527059556,-5827506947056⟩,⟨5644812457082,5644831932982⟩,⟨73787406197110,73787953475920⟩,⟨-32243812610864,-32243183070944⟩,⟨-10640144968188,-10639421853216⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5103302029842,5103303306668⟩,⟨-25503625216604,-25503605103206⟩,⟨2203733107603,2203752583727⟩,⟨216690192716457,216690740045729⟩,⟨-7048410933554,-7047781385813⟩,⟨-3101539009955,-3100815891617⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463279270503,463279386424⟩,⟨1757447582527,1757450427452⟩,⟨200055544528,200057312582⟩,⟨-31241583518492,-31241499174769⟩,⟨1118825486675,1118898180083⟩,⟨-281558630393,-281492985489⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨40147376669,40147378936⟩,⟨-810127441851,-810127430432⟩,⟨326795816458,326795834885⟩,⟨10096519701112,10096519731591⟩,⟨-6594360098773,-6594360006268⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨503426647172,503426765360⟩,⟨947320140676,947322997020⟩,⟨526851360986,526853147467⟩,⟨-21145063817380,-21144979443178⟩,⟨-5475534612098,-5475461826185⟩,⟨-281558630393,-281492985489⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502882001783,502882013886⟩,⟨2533615820870,2533615942923⟩,⟨0,0⟩,⟨3256741201878,3256744126778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨230251498652,230251558250⟩,⟨1593325547759,1593327192816⟩,⟨240965225252,240966048133⟩,⟨-3814103711715,-3814049825451⟩,⟨-1290308254642,-1290270729292⟩,⟨-128776056117,-128746029104⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-792070222380,-792069042066⟩,⟨5827506947056,5827527059556⟩,⟨-5644831932982,-5644812457082⟩,⟨-73787953475920,-73787406197110⟩,⟨32243183070944,32243812610864⟩,⟨10639421853216,10640144968188⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3519162765396,3519164042222⟩,⟨-13848591209992,-13848571096594⟩,⟨-9085911282461,-9085891806337⟩,⟨69114833043427,69115380372699⟩,⟨57438584748254,57439214295995⟩,⟨18178027811449,18178750929787⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨448686392615,448686555422⟩,⟨395128492631,395131841110⟩,⟨-175468259779,-175465419920⟩,⟨-13609521910401,-13609425462155⟩,⟨-7050560180504,-7050460549884⟩,⟨-3878705958742,-3878602475725⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨329847364646,329847364652⟩,⟨1928869812632,1928869812634⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-329847364652,-329847364646⟩,⟨-1928869812634,-1928869812632⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨769664263124,769664263130⟩,⟨-1928869812634,-1928869812632⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1335077251800,1335077278870⟩,⟨-8640921629248,-8640921561050⟩,⟨-3930840099884,-3930840068853⟩,⟨52040196157138,52040196170135⟩,⟨33524747081171,33524747164895⟩,⟨10769351399285,10769351402055⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1335077278870,-1335077251800⟩,⟨8640921561050,8640921629248⟩,⟨3930840068853,3930840099884⟩,⟨-52040196170135,-52040196157138⟩,⟨-33524747164895,-33524747081171⟩,⟨-10769351402055,-10769351399285⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-235565651094,-235565624024⟩,⟨8640921561050,8640921629248⟩,⟨3930840068853,3930840099884⟩,⟨-52040196170135,-52040196157138⟩,⟨-33524747164895,-33524747081171⟩,⟨-10769351402055,-10769351399285⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11547581988,-11547580659⟩,⟨452523220432,452523227135⟩,⟨98696130249,98696142589⟩,⟨-4674145833891,-4674145816290⟩,⟨1557181010195,1557181072531⟩,⟨2609073997400,2609074022348⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437138810627,437138974763⟩,⟨847651713063,847655068245⟩,⟨-76772129530,-76769277331⟩,⟨-18283667744292,-18283571278445⟩,⟨-5493379170309,-5493279477353⟩,⟨-1269631961342,-1269528453377⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99813991384,-99813991382⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4892947013,4892947014⟩,⟨30751446325,30751446330⟩,⟨39828121951,39828121953⟩,⟨-323392666344,-323392666333⟩,⟨250313839737,250313839741⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10698040467,10698040728⟩,⟨13336820025,13336821669⟩,⟨87081028926,87081031027⟩,⟨-910741529196,-910741511768⟩,⟨108560442911,108560456131⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1466156870606,1466156891560⟩,⟨-7249266366583,-7249265995658⟩,⟨-1353207992582,-1353207926288⟩,⟨105020632589549,105020639855772⟩,⟨22139869858207,22139871327221⟩,⟨4939407011812,4939407290887⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14265429429,14265429982⟩,⟨-52749852809,-52749845031⟩,⟨102952776288,102952781717⟩,⟨-368472081094,-368471914189⟩,⟨-230376117674,-230376032367⟩,⟨-166287935174,-166287915611⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14265429982,-14265429429⟩,⟨52749845031,52749852809⟩,⟨-102952781717,-102952776288⟩,⟨368471914189,368472081094⟩,⟨230376032367,230376117674⟩,⟨166287915611,166287935174⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114079421366,-114079420811⟩,⟨-824711973543,-824711965763⟩,⟨-102952781717,-102952776288⟩,⟨2567495169741,2567495336646⟩,⟨230376032367,230376117674⟩,⟨166287915611,166287935174⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨93494053813,93494055716⟩,⟨-605114640942,-605114636138⟩,⟨592348723764,592348739215⟩,⟨3644320127179,3644320128221⟩,⟨-3267738443795,-3267738404431⟩,⟨-2376595236440,-2376595236061⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨124670759176,124670763497⟩,⟨-1423319476616,-1423319414589⟩,⟨674808004703,674808044576⟩,⟨21768959030317,21768960372414⟩,⟨-5635519233507,-5635518611405⟩,⟨-4207139132625,-4207138945084⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-124670763497,-124670759176⟩,⟨1423319414589,1423319476616⟩,⟨-674808044576,-674808004703⟩,⟨-21768960372414,-21768959030317⟩,⟨5635518611405,5635519233507⟩,⟨4207138945084,4207139132625⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨974840864279,974840868600⟩,⟨1423319414589,1423319476616⟩,⟨-674808044576,-674808004703⟩,⟨-21768960372414,-21768959030317⟩,⟨5635518611405,5635519233507⟩,⟨4207138945084,4207139132625⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124290309919,124290310474⟩,⟨780031311823,780031322399⟩,⟨186254503036,186254509335⟩,⟨-2527703171330,-2527702917288⟩,⟨-663048882198,-663048754978⟩,⟨-150998649173,-150998601585⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11836267960,11836268077⟩,⟨171135367764,171135370212⟩,⟨21363654176,21363655408⟩,⟨704406273339,704406333910⟩,⟨106638639976,106638667516⟩,⟨-15226318793,-15226312528⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171764234636,171764389321⟩,⟨1682012124582,1682017638315⟩,⟨105166672227,105169282361⟩,⟨-2068665668956,-2068452775796⟩,⟨511674353934,511804578303⟩,⟨-528142725041,-528050207497⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171764389321,-171764234636⟩,⟨-1682017638315,-1682012124582⟩,⟨-105169282361,-105166672227⟩,⟨2068452775796,2068665668956⟩,⟨-511804578303,-511674353934⟩,⟨528050207497,528142725041⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58487109331,58487323614⟩,⟨-88692090556,-88684931766⟩,⟨135795942891,135799375906⟩,⟨-1745650935919,-1745384156495⟩,⟨-1802112832945,-1801945083226⟩,⟨399274151380,399396695937⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27677244524281,27677269736750⟩,⟨-238912905644248,-238912280219722⟩,⟨-82945409576549,-82944991545143⟩,⟨3306948245758392,3306970359846025⟩,⟨1272998118072971,1273015213636643⟩,⟨298171222303128,298186174579977⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14049947949,14049948075⟩,⟨176351629294,176351632474⟩,⟨42108931494,42108933108⟩,⟨535291902402,535291992403⟩,⟨114366763060,114366805016⟩,⟨28963897263,28963912446⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353669606682,353669932028⟩,⟨1386263872951,1386276016125⟩,⟨73210689,79568161⟩,⟨-20907015151672,-20906515644239⟩,⟨-3307842946652,-3307529077547⟩,⟨-1814036647172,-1813812238248⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353669932028,-353669606682⟩,⟨-1386276016125,-1386263872951⟩,⟨-79568161,-73210689⟩,⟨20906515644239,20907015151672⟩,⟨3307529077547,3307842946652⟩,⟨1813812238248,1814036647172⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83468878599,83469368081⟩,⟨-538624303062,-538608804706⟩,⟨-76851697691,-76842488020⟩,⟨2622847899947,2623443873227⟩,⟨-2185850092762,-2185436530701⟩,⟨544180276906,544508193795⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239999580624,239999580630⟩,⟨1552571624369,1552571624379⟩,⟨307114079992,307114079997⟩,⟨-3890928397846,-3890928397841⟩,⟨-1539328526260,-1539328526248⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1655486511250,-1655485028692⟩,⟨-4243520815696,-4243478601527⟩,⟨480385445954,480409168597⟩,⟨44032442390914,44033976939883⟩,⟨-7919194467321,-7918142722587⟩,⟨1809229928890,1810080784141⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187138477913,-187138309486⟩,⟨-1654152449438,-1654146607645⟩,⟨-226131825826,-226128883316⟩,⟨2762337263281,2762574521840⟩,⟨-274913918186,-274769928357⟩,⟨594621795114,594726295751⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52861102711,52861271144⟩,⟨-101580825069,-101574983266⟩,⟨80982254166,80985196681⟩,⟨-1128591134565,-1128353876001⟩,⟨-1814242444446,-1814098454605⟩,⟨244493963991,244598464630⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4440019827,4440062133⟩,⟨-35384588658,-35383076329⟩,⟨6220839129,6221665077⟩,⟨93884756605,93947513467⟩,⟨-313408067562,-313367266656⟩,⟨40273945935,40303730691⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2541397570,2541413767⟩,⟨-9767412008,-9766819172⟩,⟨7786750310,7787058058⟩,⟨-89751274118,-89725956261⟩,⟨-189410829762,-189395024514⟩,⟨35438180989,35449170977⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4408366408,4408394594⟩,⟨-34426943084,-34425802960⟩,⟨5553356444,5553941238⟩,⟨62901184413,62953798250⟩,⟨-293325996570,-293294230004⟩,⟨30155090313,30176192393⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4408394594,-4408366408⟩,⟨34425802960,34426943084⟩,⟨-5553941238,-5553356444⟩,⟨-62953798250,-62901184413⟩,⟨293294230004,293325996570⟩,⟨-30176192393,-30155090313⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨31625233,31695725⟩,⟨-958785698,-956133245⟩,⟨666897891,668308633⟩,⟨30930958355,31046329054⟩,⟨-20113837558,-20041270086⟩,⟨10097753542,10148640378⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58487109331,58487323614⟩,⟨-88692090556,-88684931766⟩,⟨135795942891,135799375906⟩,⟨-1745650935919,-1745384156495⟩,⟨-1802112832945,-1801945083226⟩,⟨399274151380,399396695937⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨31625233,31695725⟩,⟨-958785698,-956133245⟩,⟨666897891,668308633⟩,⟨30930958355,31046329054⟩,⟨-20113837558,-20041270086⟩,⟨10097753542,10148640378⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110810156236,111239652967⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨133143986176,137009456743⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111239652967,-110810156236⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438516160921,438945657652⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨53101566361,54696744060⟩,⟨-137009456743,-133143986176⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163911722597,165936397027⟩,⟨962502171033,966367641600⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52672069630,55126240791⟩,⟨-137009456743,-133143986176⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2092693238080,-2079194980608⟩,⟨6377638346806,6482345751793⟩,⟨2905653169158,2944425492598⟩,⟨-38217700826669,-36993033866255⟩,⟨-24734797942008,-24139509926485⟩,⟨-7884992993657,-7678700366743⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-315825651351,-309959824232⟩,⟨-888522974084,-841803361709⟩,⟨-402276776575,-384873822573⟩,⟨5398100194628,5879943680416⟩,⟨3433425056819,3669799236594⟩,⟨1127722878176,1206223318235⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309959824232,315825651351⟩,⟨841803361709,888522974084⟩,⟨384873822573,402276776575⟩,⟨-5879943680416,-5398100194628⟩,⟨-3669799236594,-3433425056819⟩,⟨-1206223318235,-1127722878176⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-165936397027,-163911722597⟩,⟨-966367641600,-962502171033⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨933575230749,935599905179⟩,⟨-966367641600,-962502171033⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-179879921728,-177497957632⟩,⟨-1138132657819,-1131127015887⟩,⟨-516965145019,-515341670334⟩,⟨-1178110275572,-1163651473753⟩,⟨757015874094,764782227086⟩,⟨-243065152213,-241540908230⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-153063990831,-150710272240⟩,⟨-813083385913,-802321691599⟩,⟨-369106435491,-365755757461⟩,⟨977874656104,1012588610692⟩,⟨1365138957075,1382000743239⟩,⟨204235737611,207676386700⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150710272240,153063990831⟩,⟨802321691599,813083385913⟩,⟨365755757461,369106435491⟩,⟨-1012588610692,-977874656104⟩,⟨-1382000743239,-1365138957075⟩,⟨-207676386700,-204235737611⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨460670096472,468889642182⟩,⟨1644125053308,1701606359997⟩,⟨750629580034,771383212066⟩,⟨-6892532291108,-6375974850732⟩,⟨-5051799979833,-4798564013894⟩,⟨-1413899704935,-1331958615787⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨819511995681,829621039209⟩,⟨4041017137387,4112692039847⟩,⟨750629580034,771383212066⟩,⟨-19110833620753,-18381003073383⟩,⟨-5051799979833,-4798564013894⟩,⟨-1413899704935,-1331958615787⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨105344139260,110252481582⟩,⟨-274018913486,-266287972352⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10965066747413,11475966561661⟩,⟨26483443719143,29851037850972⟩,⟨-95635613428260,-87224503345832⟩,⟨127928594942752,155295757615236⟩,⟨-278828622193671,-181782099360656⟩,⟨1387700441626980,1593969537407869⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8172722785227,8659029212880⟩,⟨60038948916979,65449208133109⟩,⟨-64674726263628,-56960888160875⟩,⟨90552776238048,157182470261598⟩,⟨-602755743589867,-482976528555630⟩,⟨885363878516151,1070328893851727⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨96237827072,101895692544⟩,⟨-806470151678,-659486296958⟩,⟨625675930080,796926926808⟩,⟨7034913856094,11711774938199⟩,⟨-7250912249055,-1084565717560⟩,⟨-5113285473751,2682385588086⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1195749454848,1201407320320⟩,⟨-806470151678,-659486296958⟩,⟨625675930080,796926926808⟩,⟨7034913856094,11711774938199⟩,⟨-7250912249055,-1084565717560⟩,⟨-5113285473751,2682385588086⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨92256767424,97446999936⟩,⟨-741562796144,-603552883022⟩,⟨572610095432,732787641225⟩,⟨5938112287141,10437865818286⟩,⟨-6353013315663,-498353038821⟩,⟨-5190129932567,2168291188552⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨100331798742,106477763499⟩,⟨-881761542209,-711716079206⟩,⟨675228009838,871327369709⟩,⟨7772162146764,13531009477113⟩,⟨-8659370968719,-1319877741958⟩,⟨-5472609441829,3669217895179⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-101895692544,-96237827072⟩,⟨659486296958,806470151678⟩,⟨-796926926808,-625675930080⟩,⟨-11711774938199,-7034913856094⟩,⟨1084565717560,7250912249055⟩,⟨-2682385588086,5113285473751⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨997615935232,1003273800704⟩,⟨659486296958,806470151678⟩,⟨-796926926808,-625675930080⟩,⟨-11711774938199,-7034913856094⟩,⟨1084565717560,7250912249055⟩,⟨-2682385588086,5113285473751⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-106930823744,-100712684480⟩,⟨722746723133,888842366996⟩,⟨-878324404782,-685693137665⟩,⟨-13626544128742,-8184815689885⟩,⟨1639331002760,8701549804082⟩,⟨-3657995410904,5207930613056⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-97571404650,-91379278198⟩,⟨577335531934,750636558605⟩,⟨-744136160670,-544643942763⟩,⟨-10922455238704,-4983397175657⟩,⟨-506232136203,7018022154290⟩,⟨-3054715674159,6286182522476⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2760394092,15098485301⟩,⟨-304426010275,38920479399⟩,⟨-68908150832,326683426946⟩,⟨-3150293091940,8547612301456⟩,⟨-9165603104922,5698144412332⟩,⟨-8527325115988,9955400417655⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1380197046,7549242651⟩,⟨-152213005138,19460239700⟩,⟨-34454075416,163341713473⟩,⟨-1575146545970,4273806150728⟩,⟨-4582801552461,2849072206166⟩,⟨-4263662557994,4977700208828⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7549242651,-1380197046⟩,⟨-19460239700,152213005138⟩,⟨-163341713473,34454075416⟩,⟨-4273806150728,1575146545970⟩,⟨-2849072206166,4582801552461⟩,⟨-4977700208828,4263662557994⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754574140965,760743205834⟩,⟨-19460239700,152213005138⟩,⟨-163341713473,34454075416⟩,⟨-4273806150728,1575146545970⟩,⟨-2849072206166,4582801552461⟩,⟨-4977700208828,4263662557994⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8423484686,9443039889⟩,⟨-149476972404,-115446761270⟩,⟨109528067626,147708162540⟩,⟨2022619808528,3353804502322⟩,⟨-2512996624744,-940419250032⟩,⟨-235652614798,1652399194137⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9443039889,-8423484686⟩,⟨115446761270,149476972404⟩,⟨-147708162540,-109528067626⟩,⟨-3353804502322,-2022619808528⟩,⟨940419250032,2512996624744⟩,⟨-1652399194137,235652614798⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090068587887,1091088143090⟩,⟨115446761270,149476972404⟩,⟨-147708162540,-109528067626⟩,⟨-3353804502322,-2022619808528⟩,⟨940419250032,2512996624744⟩,⟨-1652399194137,235652614798⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9483823872,-8455917056⟩,⟨116338040340,150771860661⟩,⟨-148987727961,-110373652839⟩,⟨-3403532594256,-2050544552413⟩,⟨959358038828,2555196319683⟩,⟨-1686901954294,226614248282⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4741911936,-4227958528⟩,⟨58169020170,75385930331⟩,⟨-74493863981,-55186826419⟩,⟨-1701766297128,-1025272276206⟩,⟨479679019414,1277598159842⟩,⟨-843450977147,113307124141⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4227958528,4741911936⟩,⟨-75385930331,-58169020170⟩,⟨55186826419,74493863981⟩,⟨1025272276206,1701766297128⟩,⟨-1277598159842,-479679019414⟩,⟨-113307124141,843450977147⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766351342144,766865314816⟩,⟨-75385930331,-58169020170⟩,⟨55186826419,74493863981⟩,⟨1025272276206,1701766297128⟩,⟨-1277598159842,-479679019414⟩,⟨-113307124141,843450977147⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272517146971,272772035773⟩,⟨28861690317,37369243101⟩,⟨-36927040635,-27382016906⟩,⟨-838451125581,-505654952132⟩,⟨235104812508,628249156186⟩,⟨-413099798535,58913153700⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532702684288,1533730629632⟩,⟨-150771860662,-116338040340⟩,⟨110373652838,148987727962⟩,⟨2050544552412,3403532594256⟩,⟨-2555196319684,-959358038828⟩,⟨-226614248282,1686901954294⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1204980952125,1211814864739⟩,⟨-979628014407,-792075329251⟩,⟨751467423369,968035755957⟩,⟨9490592539492,15810277194157⟩,⟨-10372876742183,-2290547172684⟩,⟨-5273881475363,4804917483162⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1310450276474,1324118101702⟩,⟨-1959256028814,-1584150658502⟩,⟨1502934846738,1936071511915⟩,⟨18981185078986,31620554388310⟩,⟨-20745753484365,-4581094345367⟩,⟨-10542939887878,9609834966323⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨192969451968,204377823680⟩,⟨-1643881362115,-1315435584584⟩,⟨1247996185274,1624428776715⟩,⟨13303690093744,24956940056922⟩,⟨-15913301505871,-1375330321514⟩,⟨-11245825606651,6646440092052⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨66046209841,70500805857⟩,⟨-559793628053,-438486910236⟩,⟨414252154265,554580280543⟩,⟨4208569545439,8277804286607⟩,⟨-5320257503236,-89480315929⟩,⟨-4235922654678,2300994512152⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379884807150,380495135844⟩,⟨2828567495,23292379331⟩,⟨-24153833067,-1208541062⟩,⟨-671587333475,133381388074⟩,⟨-300378073305,648704895385⟩,⟨-642468144831,495176284026⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177243821877,3182348430000⟩,⟨-195123535872,-23619352132⟩,⟨10091665466,202340054913⟩,⟨-1117003468965,5649909232282⟩,⟨-5459104783754,2516159303186⟩,⟨-4148097231390,5407776328985⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨190852835817,204052529474⟩,⟨-1632738294466,-1268508454093⟩,⟨1197665018564,1618111875382⟩,⟨12108662755012,24519648335040⟩,⟨-15950049362653,-110157046161⟩,⟨-12518526108565,7210698159827⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨383822287785,408430353154⟩,⟨-3276619656581,-2583944038677⟩,⟨2445661203838,3242540652097⟩,⟨25412352848756,49476588391962⟩,⟨-31863350868524,-1485487367675⟩,⟨-23764351715216,13857138251879⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517850034350,526352073596⟩,⟨-26928765030,210629895262⟩,⟨-226029621908,47676992448⟩,⟨-5919411876282,2221806120313⟩,⟨-3987725098058,6351146117740⟩,⟨-6898297946937,5948518880038⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355390734346,364178744226⟩,⟨-27947692213,218599682421⟩,⟨-234582101962,49480988418⟩,⟨-6148981732166,2349612968882⟩,⟨-4185548400188,6601360359984⟩,⟨-7169939094536,6223966086286⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨710781468692,728357488452⟩,⟨-55895384426,437199364842⟩,⟨-469164203924,98961976836⟩,⟨-12297963464332,4699225937764⟩,⟨-8371096800376,13202720719968⟩,⟨-14339878189072,12447932172572⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523259644399,1525307144946⟩,⟨-35325099392,33138932064⟩,⟨-37334509702,39459660336⟩,⟨-1303259949910,1380912785728⟩,⟨-1614777069652,1553638585916⟩,⟨-1879013442419,1922554569092⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨984714213013,1010420311296⟩,⟨-100942024717,628461115674⟩,⟨-675583925948,163425419891⟩,⟨-17951878277366,7460164585675⟩,⟨-12711551749927,19375541847572⟩,⟨-21171525342100,18573936296008⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67544165534,67670574481⟩,⟨14306907362,18541476522⟩,⟨-18322069172,-13573424666⟩,⟨-414498614653,-248115947353⟩,⟨114032731624,310280502188⟩,⟨-203603664294,31711292103⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50343491141,51059880502⟩,⟨258907505355,267110073784⟩,⟨32287311606,37358732489⟩,⟨-1383786134922,-1175387973167⟩,⟨-284690809628,-97541148878⟩,⟨-266354583792,-76429301981⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136564506530,2139431348289⟩,⟨-420629332046,-324346959520⟩,⟨307718426446,415651887698⟩,⟨5741475760011,9536660113971⟩,⟨-7169448539906,-2698018389820⟩,⟨-610057887499,4746562880556⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2978338811147,2984335323041⟩,⟨-880116327081,-678202180321⟩,⟨643432292534,869701622960⟩,⟨12056774538182,20040834153721⟩,⟨-15086704613698,-5690334619944⟩,⟨-1230148046585,10016095856039⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136369611531,138588625280⟩,⟨660452894596,693947152174⟩,⟨116920256170,141788264893⟩,⟨-3631501016536,-2572600615945⟩,⟨-1351717178079,-333396347161⟩,⟨-742287017849,317204650549⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8723124406293,8865067561917⟩,⟨-45111871474565,-41570603304687⟩,⟨-9217321466651,-7359261542034⟩,⟨558140797122969,695198954345065⟩,⟨91126879730740,181680741002569⟩,⟨-8203449923433,67421476792215⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7812363569207,8146748155534⟩,⟨-42270411620329,-32163201164769⟩,⟨-13917511726435,-5273243049534⟩,⟨303555177964096,707300727506533⟩,⟨-32850935978585,351744046144396⟩,⟨-180979099453733,223042096121945⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15624727138414,16293496311068⟩,⟨-84540823240658,-64326402329538⟩,⟨-27835023452870,-10546486099068⟩,⟨607110355928192,1414601455013066⟩,⟨-65701871957170,703488092288792⟩,⟨-361958198907466,446084192243890⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10867759718499,10909882818322⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108414,2148278590204846⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9768248090723,9810371190546⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108424,2148278590204831⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2401631390336,2406362620352⟩,⟨-12184942684160,-12039116462039⟩,⟨0,0⟩,⟨102958094106835,109987257462969⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7285477094081,7375468944262⟩,⟨-43483250718343,-42258887415294⟩,⟨-19751058770768,-19253156649256⟩,⟨490239291817803,512724847009286⟩,⟨271627429151640,282365295770402⟩,⟨101759716261263,105784276366538⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6185965466305,6275957316486⟩,⟨-43483250718343,-42258887415293⟩,⟨-19751058770769,-19253156649255⟩,⟨490239291817806,512724847009285⟩,⟨271627429151641,282365295770403⟩,⟨101759716261263,105784276366538⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1899315058880,1915195280256⟩,⟨-7728840395051,-7403514037264⟩,⟨-3510611059448,-3373042316841⟩,⟨31558462249544,41281974792870⟩,⟨22910286809115,27476200346429⟩,⟨6618749634547,8454709063586⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99599284960,100028781692⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139174448346,141199122777⟩,⟨671400468279,678817818874⟩,⟨306091137824,308136419659⟩,⟨-1698693120000,-1685130754127⟩,⟨-1543272346424,-1535384706082⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4300946449216,4321557900608⟩,⟨-19913783079211,-19442630499303⟩,⟨-3510611059448,-3373042316841⟩,⟨134516556356379,151269232255839⟩,⟨22910286809115,27476200346429⟩,⟨6618749634547,8454709063586⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨767644575570,816860706308⟩,⟨-6553239313162,-5167888077354⟩,⟨4891322407676,6485081304194⟩,⟨50824705697512,98953176783924⟩,⟨-63726701737048,-2970974735350⟩,⟨-47528703430432,27714276503758⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5068591024786,5138418606916⟩,⟨-26467022392373,-24610518576657⟩,⟨1380711348228,3112038987353⟩,⟨185341262053891,250222409039763⟩,⟨-40816414927933,24505225611079⟩,⟨-40909953795885,36168985567344⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459138429344,467470957186⟩,⟨1635138823995,1873361740471⟩,⟨125071767815,283119760282⟩,⟨-35752221301355,-26634504416637⟩,⟨-2611966718857,4714147383174⟩,⟨-3721809514244,3290496862371⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨39098342176,41203535149⟩,⟨-831480866449,-788967664930⟩,⟨325509421405,328085365043⟩,⟨9730172790739,10470647203514⟩,⟨-6627114036394,-6561817940510⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨498236771520,508674492335⟩,⟨803657957546,1084394075541⟩,⟨450581189220,611205125325⟩,⟨-26022048510616,-16163857213123⟩,⟨-9239080755251,-1847670557336⟩,⟨-3721809514244,3290496862371⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502387216868,503376923070⟩,⟨2513460839922,2553938535635⟩,⟨0,0⟩,⟨2096765778922,4420352332343⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227653604256,232880666587⟩,⟨1506165152776,1678001664196⟩,⟨205878886504,279821102005⟩,⟨-7288951827799,-302900958447⟩,⟨-3199804148848,575468451422⟩,⟨-1703913786999,1506450813351⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-816860706308,-767644575570⟩,⟨5167888077354,6553239313162⟩,⟨-6485081304194,-4891322407676⟩,⟨-98953176783924,-50824705697512⟩,⟨2970974735350,63726701737048⟩,⟨-27714276503758,47528703430432⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3484085742908,3553913325038⟩,⟨-14745895001857,-12889391186141⟩,⟨-9995692363642,-8264364724517⟩,⟨35563379572455,100444526558327⟩,⟨25881261544465,91202902083477⟩,⟨-21095526869211,55983412494018⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441010080302,456393030546⟩,⟨233839601140,562600493071⟩,⟨-313716758659,-50111588014⟩,⟨-19196747367473,-8182130435683⟩,⟨-12015923163867,-1787765500492⟩,⟨-9444453097828,1479592950630⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨327823445194,331872794054⟩,⟨1925004342066,1932735283200⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-331872794054,-327823445194⟩,⟨-1932735283200,-1925004342066⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨767638833722,771688182582⟩,⟨-1932735283200,-1925004342066⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1326032358219,1344172747041⟩,⟨-8791012342310,-8494148111189⟩,⟨-3993073161716,-3869935395589⟩,⟨47956832069630,56145306335366⟩,⟨31604673533606,35456452487938⟩,⟨10002025664818,11539913423384⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1344172747041,-1326032358219⟩,⟨8494148111189,8791012342310⟩,⟨3869935395589,3993073161716⟩,⟨-56145306335366,-47956832069630⟩,⟨-35456452487938,-31604673533606⟩,⟨-11539913423384,-10002025664818⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-244661119265,-226520730443⟩,⟨8494148111189,8791012342310⟩,⟨3869935395589,3993073161716⟩,⟨-56145306335366,-47956832069630⟩,⟨-35456452487938,-31604673533606⟩,⟨-11539913423384,-10002025664818⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12266580391,-10851468402⟩,⟨434342140363,471242265318⟩,⟨87715826086,109857966460⟩,⟨-5005843674381,-4354547013818⟩,⟨1338970537290,1771552206003⟩,⟨2508301239946,2709072630557⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428743499911,445541562144⟩,⟨668181741503,1033842758389⟩,⟨-226000932573,59746378446⟩,⟨-24202591041854,-12536677449501⟩,⟨-10676952626577,-16213294489⟩,⟨-6936151857882,4188665581187⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100028781692,-99599284960⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4771300584,5015145422⟩,⟨29549681571,31954006969⟩,⟨39722996071,39933365192⟩,⟨-329039457819,-317750404706⟩,⟨249756374792,250871388573⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10421813617,10976017147⟩,⟨8965965494,17690294531⟩,⟨86765789348,87397126939⟩,⟨-981581001062,-839483046718⟩,⟨102988436616,114103164432⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1457202460496,1475177698418⟩,⟨-7403127238675,-7097915599055⟩,⟨-1388542592875,-1318456523220⟩,⟨101432384280116,108705474665377⟩,⟨21272712798108,23030289860301⟩,⟨4725384385836,5159107158367⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13812216316,14726152325⟩,⟨-62019921220,-43543719104⟩,⟨101130949056,104760678751⟩,⟨-593739969980,-143175329869⟩,⟨-272666991181,-187878127210⟩,⟨-175952837856,-156585332008⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14726152325,-13812216316⟩,⟨43543719104,62019921220⟩,⟨-104760678751,-101130949056⟩,⟨143175329869,593739969980⟩,⟨187878127210,272666991181⟩,⟨156585332008,175952837856⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114754934017,-113411501276⟩,⟨-834347596200,-815012400622⟩,⟨-104760678751,-101130949056⟩,⟨2342198585421,2792763225532⟩,⟨187878127210,272666991181⟩,⟨156585332008,175952837856⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨90986627611,96022191594⟩,⟨-626152342700,-584660287877⟩,⟨581488673026,602996380665⟩,⟨3304845688294,3995927300202⟩,⟨-3494722376255,-3037014716559⟩,⟨-2485932526621,-2266634334913⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨120586207801,128829738599⟩,⟨-1486614995766,-1362226442755⟩,⟨649393607267,699915199480⟩,⟨20322257659855,23286531069061⟩,⟨-6287349491762,-4976795696690⟩,⟨-4467272219169,-3948017749392⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-128829738599,-120586207801⟩,⟨1362226442755,1486614995766⟩,⟨-699915199480,-649393607267⟩,⟨-23286531069061,-20322257659855⟩,⟨4976795696690,6287349491762⟩,⟨3948017749392,4467272219169⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨970681889177,978925419975⟩,⟨1362226442755,1486614995766⟩,⟨-699915199480,-649393607267⟩,⟨-23286531069061,-20322257659855⟩,⟨4976795696690,6287349491762⟩,⟨3948017749392,4467272219169⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122867383148,125713459570⟩,⟨765160974547,795281040826⟩,⟨180343442241,192143103936⟩,⟨-2839199343944,-2224427048547⟩,⟨-796949463178,-527984269950⟩,⟨-204600097470,-96681518913⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11698074214,11976858224⟩,⟨168132428212,174160056030⟩,⟨20862740270,21867535504⟩,⟨625299168851,783081583771⟩,⟨93010557946,120233889956⟩,⟨-18124387575,-12339619875⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166236730036,177483248346⟩,⟨1468369973588,1896461255538⟩,⟨-6731630019,211844082500⟩,⟨-11437003315152,7340449449639⟩,⟨-5484331372361,6611459179873⟩,⟨-5318541662422,4283562459426⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177483248346,-166236730036⟩,⟨-1896461255538,-1468369973588⟩,⟨-211844082500,6731630019⟩,⟨-7340449449639,11437003315152⟩,⟨-6611459179873,5484331372361⟩,⟨-4283562459426,5318541662422⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50170355910,66643936551⟩,⟨-390296102762,209631690608⟩,⟨-5965195996,286552732024⟩,⟨-14629401277438,11134102356705⟩,⟨-9811263328721,6059799823783⟩,⟨-5987476246425,6824992475773⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26990419014401,28380988836786⟩,⟨-261790790432372,-216326944906297⟩,⟨-100507926517333,-66151156436892⟩,⟨2363475730999495,4264321245020303⟩,⟨479478148922499,2098134105615578⟩,⟨-471715783849509,1080053146204847⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13730090214,14373539596⟩,⟨171009244930,181858069432⟩,⟨40305761678,43937642348⟩,⟨415722288439,653312606008⟩,⟨68765966532,159954146682⟩,⟨12374168504,45547434936⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337041354197,371014963839⟩,⟨775572410792,1992815095171⟩,⟨-324494308303,308075315257⟩,⟨-46881070122619,5318027461299⟩,⟨-19409842123513,13338275399949⟩,⟨-13895627636210,10444930388153⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371014963839,-337041354197⟩,⟨-1992815095171,-775572410792⟩,⟨-308075315257,324494308303⟩,⟨-5318027461299,46881070122619⟩,⟨-13338275399949,19409842123513⟩,⟨-10444930388153,13895627636210⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57728536072,108500207947⟩,⟨-1324633353668,258270347597⟩,⟨-534076247830,384240686749⟩,⟨-29520618503153,34344392673118⟩,⟨-24015228026526,19393628829024⟩,⟨-17381082246035,18084293217397⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238773733306,241227904469⟩,⟨1548432790121,1556709134178⟩,⟨306091137824,308136419659⟩,⟨-3897716375552,-3884154009679⟩,⟨-1543272346424,-1535384706082⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1700535989661,-1611646222768⟩,⟨-5728984998275,-2758378997365⟩,⟨-464592550173,1467981560789⟩,⟨-18992661041238,107068850147784⟩,⟨-57018294745598,40075020960221⟩,⟨-42392099807025,45688837460159⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-194432015982,-180097007570⟩,⟨-1885031957298,-1429801708195⟩,⟨-350293521643,-96501741515⟩,⟨-7198605071545,12793814955215⟩,⟨-7082517043946,6423954902416⟩,⟨-4867595298240,6053375470680⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44341717324,61130896899⟩,⟨-336599167177,126907425983⟩,⟨-44202383819,211634678144⟩,⟨-11096321447097,8909660945536⟩,⟨-8625789390370,4888570196334⟩,⟨-5218065971773,5703590314196⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2634134217,6576447936⟩,⟨-118803645352,36340893241⟩,⟨-32960241315,51566842523⟩,⟨-3738053752335,4120826286678⟩,⟨-2905415743256,2030368033944⟩,⟨-1922733805312,1969903705408⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1788237473,3398769473⟩,⟨-37428633706,14111655718⟩,⟨-4915148326,23533025688⟩,⟨-1311573244012,1196812379952⟩,⟨-1088734822234,592446109128⟩,⟨-597246635526,715690163716⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3089031780,5920180460⟩,⟨-89086542555,12539508312⟩,⟨-19413370480,35505344440⟩,⟨-2431641706942,2738486008989⟩,⟨-2069640953588,1270947027787⟩,⟨-1179831671719,1304153901300⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5920180460,-3089031780⟩,⟨-12539508312,89086542555⟩,⟨-35505344440,19413370480⟩,⟨-2738486008989,2431641706942⟩,⟨-1270947027787,2069640953588⟩,⟨-1304153901300,1179831671719⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3286046243,3487416156⟩,⟨-131343153664,125427435796⟩,⟨-68465585755,70980213003⟩,⟨-6476539761324,6552467993620⟩,⟨-4176362771043,4100008987532⟩,⟨-3226887706612,3149735377127⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50170355910,66643936551⟩,⟨-390296102762,209631690608⟩,⟨-5965195996,286552732024⟩,⟨-14629401277438,11134102356705⟩,⟨-9811263328721,6059799823783⟩,⟨-5987476246425,6824992475773⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3286046243,3487416156⟩,⟨-131343153664,125427435796⟩,⟨-68465585755,70980213003⟩,⟨-6476539761324,6552467993620⟩,⟨-4176362771043,4100008987532⟩,⟨-3226887706612,3149735377127⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (517/5120) u, BivariateJet2.affineZ (629/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000028

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000029Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2075690771712,-2075690732992⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2075690771648,-2075690732992⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-180503947584,-180503947520⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-180503947584,-180503947520⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨97109762432,97109762496⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-106524833280,-106524833216⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨97109884992,97109885056⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-106524980800,-106524980736⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-9415095744,-9415095680⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-9415070784,-9415070720⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨203634595648,203634595712⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨203634865728,203634865792⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1895186785408,1895186824000⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1895186785408,1895186824000⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2518909148864,-2518909091008⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2082400200512,-2082400161792⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2069017080448,-2069017041728⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-181698881088,-181698881024⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-179311200064,-179311200000⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨94526839232,94526839296⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-103424400256,-103424400192⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨99714198400,99714198464⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-109667381568,-109667381504⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9953183168,-9953183104⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8897561024,-8897560960⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨197951239488,197951239552⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨209381579904,209381579968⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1887318160704,1887318199296⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1903088961728,1903089000320⟩



end LaneCBRB2Cell000029Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000029
open Set LaneCBRB2Cell000029Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111024904601,111024904602⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨138942192025,138942192026⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111024904602,-111024904601⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438730909286,438730909287⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨55441191075,55441191077⟩,⟨-138942192026,-138942192025⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨166466095676,166466095679⟩,⟨960569435750,960569435751⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨55441191074,55441191078⟩,⟨-138942192026,-138942192025⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2075690771712,-2075690732992⟩,⟨6344578813993,6344578814116⟩,⟨2897825735967,2897825736027⟩,⟨-36610508985654,-36610508984245⟩,⟨-23983794631343,-23983794630547⟩,⟨-7637385348407,-7637385348093⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-314259649353,-314259643484⟩,⟨-852822131041,-852822097174⟩,⟨-389518357640,-389518342169⟩,⟨5542832233180,5542832233722⟩,⟨3507814752940,3507814791959⟩,⟨1156300386392,1156300386516⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨314259643484,314259649353⟩,⟨852822097174,852822131041⟩,⟨389518342169,389518357640⟩,⟨-5542832233722,-5542832233180⟩,⟨-3507814791959,-3507814752940⟩,⟨-1156300386516,-1156300386392⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-166466095679,-166466095676⟩,⟨-960569435751,-960569435750⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨933045532097,933045532100⟩,⟨-960569435751,-960569435750⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-180503947584,-180503947520⟩,⟨-1131946113628,-1131946113622⟩,⟨-517005569002,-517005568998⟩,⟨-1165337384152,-1165337384138⟩,⟨763420484221,763420484234⟩,⟨-243103166557,-243103166553⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-153175644137,-153175644081⟩,⟨-802875264416,-802875264350⟩,⟨-366705603669,-366705603636⟩,⟨988905266831,988905266860⟩,⟨1370680709504,1370680709592⟩,⟨206297339345,206297339355⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨153175644081,153175644137⟩,⟨802875264350,802875264416⟩,⟨366705603636,366705603669⟩,⟨-988905266860,-988905266831⟩,⟨-1370680709592,-1370680709504⟩,⟨-206297339355,-206297339345⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨467435287565,467435293490⟩,⟨1655697361524,1655697395457⟩,⟨756223945805,756223961309⟩,⟨-6531737500582,-6531737500011⟩,⟨-4878495501551,-4878495462444⟩,⟨-1362597725871,-1362597725737⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨827221239709,827221251538⟩,⟨4059692307048,4059692398925⟩,⟨756223945805,756223961309⟩,⟨-18643524664784,-18643524663706⟩,⟨-4878495501551,-4878495462444⟩,⟨-1362597725871,-1362597725737⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨110882382148,110882382156⟩,⟨-277884384052,-277884384050⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10902776402420,10902776403208⟩,⟨27323649132633,27323649136781⟩,⟨-86278539700708,-86278539688038⟩,⟨136952602597182,136952602628851⟩,⟨-216224240511019,-216224240381890⟩,⟨1365521246321843,1365521246624167⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8202740183951,8202740301841⟩,⟨60813017985528,60813019196573⟩,⟨-57413218201713,-57413217109679⟩,⟨119939738653954,119939744772277⟩,⟨-510823125785728,-510823115326565⟩,⟨895161321533843,895161338905068⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨101527258624,101527392512⟩,⟨-743470238948,-743468232349⟩,⟨701904040483,701905934274⟩,⟨9355146394892,9355195299223⟩,⟨-3971473458210,-3971414217682⟩,⟨-1298477869544,-1298408334355⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1201038886400,1201039020288⟩,⟨-743470238948,-743468232349⟩,⟨701904040483,701905934274⟩,⟨9355146394892,9355195299223⟩,⟨-3971473458210,-3971414217682⟩,⟨-1298477869544,-1298408334355⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨97109762432,97109885056⟩,⟨-680622569249,-680620656399⟩,⟨642570009014,642571814351⟩,⟨8143007341908,8143055435144⟩,⟨-3237989173574,-3237932300074⟩,⟨-1564242845874,-1564176946052⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨106076732599,106076878372⟩,⟨-809134301748,-809131869247⟩,⟨763896698736,763898994566⟩,⟨10641619325199,10641683284619⟩,⟨-4756736158449,-4756663177105⟩,⟨-1002960525986,-1002877545875⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-101527392512,-101527258624⟩,⟨743468232349,743470238948⟩,⟨-701905934274,-701904040483⟩,⟨-9355195299223,-9355146394892⟩,⟨3971414217682,3971473458210⟩,⟨1298408334355,1298477869544⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨997984235264,997984369152⟩,⟨743468232349,743470238948⟩,⟨-701905934274,-701904040483⟩,⟨-9355195299223,-9355146394892⟩,⟨3971414217682,3971473458210⟩,⟨1298408334355,1298477869544⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-106524980800,-106524833216⟩,⟨819102975574,819105296201⟩,⟨-773312552513,-773310362315⟩,⟨-10917132793209,-10917074073361⟩,⟨4951528252271,4951597370273⟩,⟨886609395994,886689277917⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-96688623456,-96688476527⟩,⟨671437832125,671440332414⟩,⟨-633902917828,-633900558008⟩,⟨-7894976435118,-7894909686195⟩,⟨3063738646186,3063814041929⟩,⟨1666268149736,1666353134815⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨9388109143,9388401845⟩,⟨-137696469623,-137691536833⟩,⟨129993780908,129998436558⟩,⟨2746642890081,2746773598424⟩,⟨-1692997512263,-1692849135176⟩,⟨663307623750,663475588940⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4694054571,4694200923⟩,⟨-68848234812,-68845768416⟩,⟨64996890454,64999218279⟩,⟨1373321445040,1373386799212⟩,⟨-846498756132,-846424567588⟩,⟨331653811875,331737794470⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4694200923,-4694054571⟩,⟨68845768416,68848234812⟩,⟨-64999218279,-64996890454⟩,⟨-1373386799212,-1373321445040⟩,⟨846424567588,846498756132⟩,⟨-331737794470,-331653811875⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757429182693,757429348309⟩,⟨68845768416,68848234812⟩,⟨-64999218279,-64996890454⟩,⟨-1373386799212,-1373321445040⟩,⟨846424567588,846498756132⟩,⟨-331737794470,-331653811875⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨9374875156,9374899883⟩,⟨-137302040040,-137301488400⟩,⟨129625537824,129626058508⟩,⟨2733117762566,2733134499746⟩,⟨-1682673459650,-1682656429032⟩,⟨656360879868,656378873478⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9374899883,-9374875156⟩,⟨137301488400,137302040040⟩,⟨-129626058508,-129625537824⟩,⟨-2733134499746,-2733117762566⟩,⟨1682656429032,1682673459650⟩,⟨-656378873478,-656360879868⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090136727893,1090136752620⟩,⟨137301488400,137302040040⟩,⟨-129626058508,-129625537824⟩,⟨-2733134499746,-2733117762566⟩,⟨1682656429032,1682673459650⟩,⟨-656378873478,-656360879868⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9415095744,-9415070720⟩,⟨138482243300,138482802826⟩,⟨-130740809796,-130740281667⟩,⟨-2774080587058,-2774063502467⟩,⟨1713593400138,1713610748763⟩,⟨-677569703485,-677551414519⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4707547872,-4707535360⟩,⟨69241121650,69241401413⟩,⟨-65370404898,-65370140833⟩,⟨-1387040293529,-1387031751233⟩,⟨856796700069,856805374382⟩,⟨-338784851743,-338775707259⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4707535360,4707547872⟩,⟨-69241401413,-69241121650⟩,⟨65370140833,65370404898⟩,⟨1387031751233,1387040293529⟩,⟨-856805374382,-856796700069⟩,⟨338775707259,338784851743⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766830918976,766830950752⟩,⟨-69241401413,-69241121650⟩,⟨65370140833,65370404898⟩,⟨1387031751233,1387040293529⟩,⟨-856805374382,-856796700069⟩,⟨338775707259,338784851743⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272534181973,272534188155⟩,⟨34325372100,34325510010⟩,⟨-32406514627,-32406384456⟩,⟨-683283624937,-683279440641⟩,⟨420664107258,420668364913⟩,⟨-164094718370,-164090219967⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533661837952,1533661901504⟩,⟨-138482802826,-138482243300⟩,⟨130740281666,130740809796⟩,⟨2774063502466,2774080587058⟩,⟨-1713610748764,-1713593400138⟩,⟨677551414518,677569703486⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1211367489294,1211367651810⟩,⟨-902434893982,-902432216203⟩,⟨851981014459,851983541773⟩,⟨12699978037044,12700048243780⟩,⟨-6090039378688,-6089958816301⟩,⟨-377677724727,-377585949747⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1323223350812,1323223675844⟩,⟨-1804869787964,-1804864432405⟩,⟨1703962028918,1703967083546⟩,⟨25399956074092,25400096487549⟩,⟨-12180078757372,-12179917632601⟩,⟨-755355303519,-755172045429⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨203634595648,203634865792⟩,⟨-1499728157965,-1499723339458⟩,⟨1415880095167,1415884643026⟩,⟨19060067320051,19060202323580⟩,⟨-8189597937278,-8189449158934⟩,⟨-2450941304164,-2450777161701⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨69939877467,69939984993⟩,⟨-505803160595,-505801430178⟩,⟨477524192832,477525826014⟩,⟨6224628377865,6224673264817⟩,⟨-2569803783468,-2569752036501⟩,⟨-1008113389489,-1008054301455⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380146297565,380146321942⟩,⟨13553485606,13553819424⟩,⟨-12796082165,-12795767078⟩,⟨-274127088935,-274116892940⟩,⟨170179547513,170189886238⟩,⟨-68651939030,-68641055758⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3180159190910,3180159394840⟩,⟨-113386100176,-113383293039⟩,⟨107044508730,107047158357⟩,⟨2301242399657,2301328389400⟩,⟨-1431377248236,-1431290198376⟩,⟨581431161597,581522636849⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨202289760761,202290084736⟩,⟨-1470166257833,-1470160969418⟩,⟨1387970433406,1387975424702⟩,⟨18254428706199,18254568323400⟩,⟨-7622280218429,-7622121619924⟩,⟨-2785839894563,-2785660309909⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨405924356409,405924950528⟩,⟨-2969894415798,-2969884308876⟩,⟨2803850528573,2803860067728⟩,⟨37314496026250,37314770646980⟩,⟨-15811878155707,-15811570778858⟩,⟨-5236781198727,-5236437471610⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨521776170712,521776398892⟩,⟨94852646912,94856065746⟩,⟨-89553060284,-89549833526⟩,⟨-1883570309428,-1883479235864⟩,⟨1158026110706,1158129162530⟩,⟨-449369228057,-449252870181⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359440035509,359440271292⟩,⟨98012828166,98016382338⟩,⟨-92536696807,-92533342309⟩,⟨-1937416385425,-1937321210436⟩,⟨1188196438303,1188303790764⟩,⟨-456400331944,-456279424196⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨718880071018,718880542584⟩,⟨196025656332,196032764676⟩,⟨-185073393614,-185066684618⟩,⟨-3874832770850,-3874642420872⟩,⟨2376392876606,2376607581528⟩,⟨-912800663888,-912558848392⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524286938069,1524287026348⟩,⟨-1181314426,-1180203260⟩,⟨1114223158,1115271972⟩,⟨40929002720,40962824492⟩,⟨-30954319732,-30919940488⟩,⟨21172541040,21208823618⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨996605651644,996606363110⟩,⟨270984058731,270994655996⟩,⟨-255844479385,-255834477423⟩,⟨-5345461822944,-5345175081459⟩,⟨3274625665649,3274946388001⟩,⟨-1251976305992,-1251616898446⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67552610147,67552613213⟩,⟨17016349748,17016418504⟩,⟨-16065101872,-16065036976⟩,⟨-336585647952,-336583548735⟩,⟨206515284324,206517415990⟩,⟨-79437535713,-79435288494⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50823431512,50823434546⟩,⟨262224691749,262224760628⟩,⟨34374814020,34374866080⟩,⟨-1273008204613,-1273006059007⟩,⟨-191969312227,-191967401744⟩,⟨-165579954052,-165578168963⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2139239434827,2139239612120⟩,⟨-386327517314,-386325940386⟩,⟨364728076736,364729565184⟩,⟨7773728905697,7773777169407⟩,⟨-4813418623912,-4813369762000⟩,⟨1921267119444,1921318469970⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2983933776191,2983934147139⟩,⟨-808307679300,-808304346420⟩,⟨763115439239,763118585120⟩,⟨16337849925712,16337952174002⟩,⟨-10139954882030,-10139851671998⟩,⟨4084893652934,4085001787769⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137928285685,137928311067⟩,⟨674281311356,674281743043⟩,⟨128562818523,128563118926⟩,⟨-3085136659154,-3085123944395⟩,⟨-832959700902,-832948712058⟩,⟨-212828548298,-212818369303⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8764885252799,8764886865742⟩,⟨-42848377068249,-42848333865780⟩,⟨-8169761458987,-8169739362523⟩,⟨614989179552531,614990827398915⟩,⟨132808883705935,132809883373656⟩,⟨28753908418343,28754639819043⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7944558255031,7944565388551⟩,⟨-36677939583605,-36677787823590⟩,⟨-9444633335218,-9444527913247⟩,⟨493697335979519,493702368433620⟩,⟨154439405107039,154443442651036⟩,⟨19884354475789,19888061844177⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15889116510062,15889130777102⟩,⟨-73355879167210,-73355575647180⟩,⟨-18889266670436,-18889055826494⟩,⟨987394671959038,987404736867240⟩,⟨308878810214078,308886885302072⟩,⟨39768708951578,39776123688354⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10888780530353,10888780530452⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239700,2135836853297982⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9789268902577,9789268902676⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239713,2135836853297977⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2403994945600,2403995003456⟩,⟨-12111787164150,-12111787163733⟩,⟨0,0⟩,⟨106474359377039,106474359411671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7262294551232,7262294551364⟩,⟨-41906059916483,-41906059914915⟩,⟨-19140192356235,-19140192355495⟩,⟨483626172197762,483626172225147⟩,⟨268859221230493,268859221245019⟩,⟨100890141764688,100890141770651⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6162782923456,6162782923588⟩,⟨-41906059916484,-41906059914915⟩,⟨-19140192356236,-19140192355494⟩,⟨483626172197770,483626172225146⟩,⟨268859221230497,268859221245020⟩,⟨100890141764689,100890141770652⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1895186785408,1895186824000⟩,⟨-7476524927913,-7476524927441⟩,⟨-3414831305106,-3414831304886⟩,⟨35445171593680,35445171608996⟩,⟨24747215111612,24747215119217⟩,⟨7394282180163,7394282183438⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99813991382,99813991384⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨141263123456,141263123460⟩,⟨669708949041,669708949049⟩,⟨305883161835,305883161841⟩,⟨-1678369955515,-1678369955510⟩,⟨-1533158872848,-1533158872838⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4299181731008,4299181827456⟩,⟨-19588312092063,-19588312091174⟩,⟨-3414831305106,-3414831304886⟩,⟨141919530970719,141919531020667⟩,⟨24747215111612,24747215119217⟩,⟨7394282180163,7394282183438⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨811848712818,811849901056⟩,⟨-5939788831596,-5939768617752⟩,⟨5607701057146,5607720135456⟩,⟨74628992052500,74629541293960⟩,⟨-31623756311414,-31623141557716⟩,⟨-10473562397454,-10472874943220⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5111030443826,5111031728512⟩,⟨-25528100923659,-25528080708926⟩,⟨2192869752040,2192888830570⟩,⟨216548523023219,216549072314627⟩,⟨-6876541199802,-6875926438499⟩,⟨-3079280217291,-3078592759782⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463980858215,463980974849⟩,⟨1761393307216,1761396167613⟩,⟨199069365891,199071097851⟩,⟨-31308966701970,-31308882002664⟩,⟨1125758405075,1125829438868⟩,⟨-279537970599,-279475562996⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨41296268211,41296270543⟩,⟨-833310739072,-833310727329⟩,⟨326795816458,326795834885⟩,⟨10385450312592,10385450343928⟩,⟨-6594360098773,-6594360006268⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨505277126426,505277245392⟩,⟨928082568144,928085440284⟩,⟨525865182349,525866932736⟩,⟨-20923516389378,-20923431658736⟩,⟨-5468601693698,-5468530567400⟩,⟨-279537970599,-279475562996⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502882001783,502882013886⟩,⟨2533615820870,2533615942923⟩,⟨0,0⟩,⟨3256741201878,3256744126778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨231097849602,231097909576⟩,⟨1588790965910,1588792619978⟩,⟨240514178192,240514984553⟩,⟨-3795952459790,-3795898337186⟩,⟨-1289409817422,-1289373134486⟩,⟨-127851869923,-127823323572⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-811849901056,-811848712818⟩,⟨5939768617752,5939788831596⟩,⟨-5607720135456,-5607701057146⟩,⟨-74629541293960,-74628992052500⟩,⟨31623141557716,31623756311414⟩,⟨10472874943220,10473562397454⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3487331829952,3487333114638⟩,⟨-13648543474311,-13648523259578⟩,⟨-9022551440562,-9022532362032⟩,⟨67289989676759,67290538968167⟩,⟨56370356669328,56370971430631⟩,⟨17867157123383,17867844580892⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨448045636245,448045801313⟩,⟨370584032619,370587412343⟩,⟨-189027297492,-189024488867⟩,⟨-13304583642715,-13304486483867⟩,⟨-6913002043160,-6912904023681⟩,⟨-3835098216160,-3834998868423⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨332932191352,332932191358⟩,⟨1921138871500,1921138871502⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-332932191358,-332932191352⟩,⟨-1921138871502,-1921138871500⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨766579436418,766579436424⟩,⟨-1921138871502,-1921138871500⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1321324105324,1321324132242⟩,⟨-8524027491145,-8524027423339⟩,⟨-3893268089520,-3893268058544⟩,⟨50839321363776,50839321376327⟩,⟨32977365068985,32977365152390⟩,⟨10605683965138,10605683967828⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1321324132242,-1321324105324⟩,⟨8524027423339,8524027491145⟩,⟨3893268058544,3893268089520⟩,⟨-50839321376327,-50839321363776⟩,⟨-32977365152390,-32977365068985⟩,⟨-10605683967828,-10605683965138⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-221812504466,-221812477548⟩,⟨8524027423339,8524027491145⟩,⟨3893268058544,3893268089520⟩,⟨-50839321376327,-50839321363776⟩,⟨-32977365152390,-32977365068985⟩,⟨-10605683967828,-10605683965138⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11184556064,-11184554705⟩,⟨457840856094,457840862947⟩,⟨107803695354,107803707674⟩,⟨-4717809733594,-4717809715622⟩,⟨1468284695241,1468284757469⟩,⟨2572235025094,2572235049998⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨436861080181,436861246608⟩,⟨828424888713,828428275290⟩,⟨-81223602138,-81220781193⟩,⟨-18022393376309,-18022296199489⟩,⟨-5444717347919,-5444619266212⟩,⟨-1262863191066,-1262763818425⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99813991384,-99813991382⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨5032967754,5032967755⟩,⟨31631455917,31631455923⟩,⟨39828121951,39828121953⟩,⟨-332647146461,-332647146450⟩,⟨250313839737,250313839741⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨11004184709,11004184977⟩,⟨13718477833,13718479525⟩,⟨87081028926,87081031027⟩,⟨-936804084903,-936804066961⟩,⟨108560442911,108560456131⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1461429837987,1461429858886⟩,⟨-7172151058130,-7172150690681⟩,⟨-1336000847188,-1336000781586⟩,⟨103333483076911,103333490227351⟩,⟨21731892151347,21731893595138⟩,⟨4849938914654,4849939188698⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14626351800,14626352366⟩,⟨-53546577047,-53546569110⟩,⟨102373827342,102373832773⟩,⟨-389950166286,-389949996636⟩,⟨-222908950753,-222908865686⟩,⟨-163082439766,-163082420343⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14626352366,-14626351800⟩,⟨53546569110,53546577047⟩,⟨-102373832773,-102373827342⟩,⟨389949996636,389950166286⟩,⟨222908865686,222908950753⟩,⟨163082420343,163082439766⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114440343750,-114440343182⟩,⟨-823915249464,-823915241525⟩,⟨-102373832773,-102373827342⟩,⟨2588973252188,2588973421838⟩,⟨222908865686,222908950753⟩,⟨163082420343,163082439766⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨95561893150,95561895103⟩,⟨-616481755746,-616481750815⟩,⟨584036303501,584036318927⟩,⟨3676843384957,3676843385993⟩,⟨-3199132426088,-3199132386794⟩,⟨-2352350089402,-2352350089026⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨127017303406,127017307819⟩,⟨-1442757995744,-1442757932794⟩,⟨660163375493,660163415174⟩,⟨21910811420451,21910812773108⟩,⟨-5423993112490,-5423992496785⟩,⟨-4124441464783,-4124441279955⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-127017307819,-127017303406⟩,⟨1442757932794,1442757995744⟩,⟨-660163415174,-660163375493⟩,⟨-21910812773108,-21910811420451⟩,⟨5423992496785,5423993112490⟩,⟨4124441279955,4124441464783⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨972494319957,972494324370⟩,⟨1442757932794,1442757995744⟩,⟨-660163415174,-660163375493⟩,⟨-21910812773108,-21910811420451⟩,⟨5423992496785,5423993112490⟩,⟨4124441279955,4124441464783⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124944185863,124944186435⟩,⟨777705864441,777705875231⟩,⟨185730542791,185730549127⟩,⟨-2541982492427,-2541982235109⟩,⟨-659911319634,-659911192647⟩,⟨-147094048212,-147094000955⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11911281169,11911281288⟩,⟨171510951972,171510954478⟩,⟨21310726758,21310727996⟩,⟨695860429664,695860491453⟩,⟨107024934060,107024961620⟩,⟨-14884444577,-14884438340⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172130725585,172130881864⟩,⟨1683833932243,1683839489997⟩,⟨103330650504,103333231090⟩,⟨-2132702048525,-2132487958222⟩,⟨524497098459,524625295980⟩,⟨-516495365896,-516406536954⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172130881864,-172130725585⟩,⟨-1683839489997,-1683833932243⟩,⟨-103333231090,-103330650504⟩,⟨2132487958222,2132702048525⟩,⟨-524625295980,-524497098459⟩,⟨516406536954,516495365896⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58966967738,58967183991⟩,⟨-95048524087,-95041312265⟩,⟨137180947102,137184334049⟩,⟨-1663464501568,-1663196288661⟩,⟨-1814035113402,-1813870232945⟩,⟨388554667031,388672042324⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27387471747422,27387496896679⟩,⟨-234484630708272,-234484007946797⟩,⟨-81906719512885,-81906311112784⟩,⟨3211770831727341,3211792802888686⟩,⟨1246294993023880,1246311620211124⟩,⟨292733258046385,292747445612628⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14198166883,14198167014⟩,⟨176750883972,176750887234⟩,⟨42211379802,42211381438⟩,⟨522451004393,522451096050⟩,⟨112762153334,112762195494⟩,⟨29317176708,29317191884⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353658737706,353659065727⟩,⟨1374708419555,1374720613407⟩,⟨-6241235921,-6234946169⟩,⟨-20900972831266,-20900472884272⟩,⟨-3266569317468,-3266260677815⟩,⟨-1778601072726,-1778385181434⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353659065727,-353658737706⟩,⟨-1374720613407,-1374708419555⟩,⟨6234946169,6241235921⟩,⟨20900472884272,20900972831266⟩,⟨3266260677815,3266569317468⟩,⟨1778385181434,1778601072726⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83202014454,83202508902⟩,⟨-546295724694,-546280144265⟩,⟨-74988655969,-74979545272⟩,⟨2878079507963,2878676631777⟩,⟨-2178456670104,-2178049948744⟩,⟨515521990368,515837254301⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨241077114838,241077114844⟩,⟨1547170767613,1547170767623⟩,⟨305883161835,305883161841⟩,⟨-3877393211067,-3877393211062⟩,⟨-1533158872848,-1533158872838⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1653786592234,-1653785099070⟩,⟨-4271405393053,-4271362958231⟩,⟨486614966652,486638328524⟩,⟨44578986299790,44580526382890⟩,⟨-7944094583295,-7943063069341⟩,⟨1734162823872,1734976437743⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187929818189,-187929647650⟩,⟨-1655141041673,-1655135144949⟩,⟨-224062188025,-224059271262⟩,⟨2846703276196,2846942261276⟩,⟨-287495180120,-287353149784⟩,⟨582707755617,582808381474⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨53147296649,53147467194⟩,⟨-107970274060,-107964377326⟩,⟨81820973810,81823890579⟩,⟨-1030689934871,-1030450949786⟩,⟨-1820654052968,-1820512022622⟩,⟨232579924494,232680550353⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4462136077,4462178960⟩,⟨-36490561055,-36489029552⟩,⟨6359060779,6359882126⟩,⟨122914175374,122977669565⟩,⟨-315782734803,-315742295148⟩,⟨38337713645,38366514927⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2568990695,2569007183⟩,⟨-10437991658,-10437388098⟩,⟨7909991048,7910298410⟩,⟨-78438920773,-78413181162⟩,⟨-192081096326,-192065350362⟩,⟨34662054524,34672722881⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4428072513,4428101024⟩,⟨-35460462190,-35459309371⟩,⟨5655405725,5655987001⟩,⟨89560391144,89613500117⟩,⟨-294634283984,-294602800849⟩,⟨27887145295,27907555247⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4428101024,-4428072513⟩,⟨35459309371,35460462190⟩,⟨-5655987001,-5655405725⟩,⟨-89613500117,-89560391144⟩,⟨294602800849,294634283984⟩,⟨-27907555247,-27887145295⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨34035053,34106447⟩,⟨-1031251684,-1028567362⟩,⟨703073778,704476401⟩,⟨33300675257,33417278421⟩,⟨-21179933954,-21108011164⟩,⟨10430158398,10479369632⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58966967738,58967183991⟩,⟨-95048524087,-95041312265⟩,⟨137180947102,137184334049⟩,⟨-1663464501568,-1663196288661⟩,⟨-1814035113402,-1813870232945⟩,⟨388554667031,388672042324⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨34035053,34106447⟩,⟨-1031251684,-1028567362⟩,⟨703073778,704476401⟩,⟨33300675257,33417278421⟩,⟨-21179933954,-21108011164⟩,⟨10430158398,10479369632⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110810156236,111239652967⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨137009456742,140874927309⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111239652967,-110810156236⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438516160921,438945657652⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨54643224739,56239912387⟩,⟨-140874927309,-137009456742⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨165453380975,167479565354⟩,⟨958636700467,962502171034⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨54213728008,56669409118⟩,⟨-140874927309,-137009456742⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2082400200512,-2069017041728⟩,⟨6293497339501,6396256894693⟩,⟨2878880279401,2916989980538⟩,⟨-37209340246503,-36023365066568⟩,⟨-24275931897539,-23696778190883⟩,⟨-7738736300378,-7537848126162⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-317194899685,-311343560359⟩,⟨-875874594365,-829635014703⟩,⟨-398122256102,-380861089011⟩,⟨5306493145581,5777687648249⟩,⟨3391311435600,3623544710131⟩,⟨1117578780186,1194746540018⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨311343560359,317194899685⟩,⟨829635014703,875874594365⟩,⟨380861089011,398122256102⟩,⟨-5777687648249,-5306493145581⟩,⟨-3623544710131,-3391311435600⟩,⟨-1194746540018,-1117578780186⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-167479565354,-165453380975⟩,⟨-962502171034,-958636700467⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨932032062422,934058246801⟩,⟨-962502171034,-958636700467⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-181698881088,-179311200000⟩,⟨-1135456999261,-1128443758819⟩,⟨-517821085786,-516192239136⟩,⟨-1172577501322,-1158137198960⟩,⟨759522654140,767310960214⟩,⟨-243870705967,-242338890297⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-154357019997,-151998199318⟩,⟨-808257643188,-797499702764⟩,⟨-368385550712,-365027319634⟩,⟨971594561733,1006209142084⟩,⟨1362242149432,1379127042503⟩,⟨204570673253,208022373377⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151998199318,154357019997⟩,⟨797499702764,808257643188⟩,⟨365027319634,368385550712⟩,⟨-1006209142084,-971594561733⟩,⟨-1379127042503,-1362242149432⟩,⟨-208022373377,-204570673253⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨463341759677,471551919682⟩,⟨1627134717467,1684132237553⟩,⟨745888408645,766507806814⟩,⟨-6783896790333,-6278087707314⟩,⟨-5002671752634,-4753553585032⟩,⟨-1402768913395,-1322149453439⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨822183658886,832283316709⟩,⟨4024026801546,4095217917403⟩,⟨745888408645,766507806814⟩,⟨-19002198119978,-18283115929965⟩,⟨-5002671752634,-4753553585032⟩,⟨-1402768913395,-1322149453439⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨108427456016,113338818236⟩,⟨-281749854618,-274018913484⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10666476309090,11149628184916⟩,⟨25788307081457,28972422996640⟩,⟨-90273830190787,-82538750878398⟩,⟨124696621987677,150570275595706⟩,⟨-262201758725428,-172981141795356⟩,⟨1277393808255223,1461818148938797⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨7976088926833,8439792078038⟩,⟨58321267004922,63458557106050⟩,⟨-61097490982481,-53947346850936⟩,⟨89313979430926,152429017343914⟩,⟨-567942958615509,-457345315289672⟩,⟨815108043854167,981722029349424⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨98709143552,104375556352⟩,⟨-820228637789,-673736244874⟩,⟨623208046650,789710861486⟩,⟨7155912729071,11796254433107⟩,⟨-7067414945726,-1100787845731⟩,⟨-4880582771193,2474958054338⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1198220771328,1203887184128⟩,⟨-820228637789,-673736244874⟩,⟨623208046650,789710861486⟩,⟨7155912729071,11796254433107⟩,⟨-7067414945726,-1100787845731⟩,⟨-4880582771193,2474958054338⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨94526839232,99714198464⟩,⟨-752658396737,-615324130914⟩,⟨569176666093,724654667623⟩,⟨6020279894800,10480125457391⟩,⟨-6166672339809,-509296622731⟩,⟨-4956119365649,1976429802775⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨103013028106,109179969156⟩,⟨-898493671260,-728487350410⟩,⟨673852983437,865063932763⟩,⟨7930050351151,13667746975294⟩,⟨-8474184539340,-1347192380499⟩,⟨-5223992984458,3429451946620⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-104375556352,-98709143552⟩,⟨673736244874,820228637789⟩,⟨-789710861486,-623208046650⟩,⟨-11796254433107,-7155912729071⟩,⟨1100787845731,7067414945726⟩,⟨-2474958054338,4880582771193⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨995136071424,1000802484224⟩,⟨673736244874,820228637789⟩,⟨-789710861486,-623208046650⟩,⟨-11796254433107,-7155912729071⟩,⟨1100787845731,7067414945726⟩,⟨-2474958054338,4880582771193⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-109667381568,-103424400192⟩,⟨740186847025,906258903262⟩,⟨-872540248233,-684675052886⟩,⟨-13780485717391,-8359991198731⟩,⟨1670279062587,8527866343172⟩,⟨-3426968198669,4966133314000⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-99821943797,-93606423703⟩,⟨588110473540,761524820266⟩,⟨-735586154041,-540912260435⟩,⟨-10963110020666,-5037677921101⟩,⟨-495015179222,6819646569524⟩,⟨-2829955533372,6020536374469⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨3191084309,15573545453⟩,⟨-310383197720,33037469856⟩,⟨-61733170604,324151672328⟩,⟨-3033059669515,8630069054193⟩,⟨-8969199718562,5472454189025⟩,⟨-8053948517830,9449988321089⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1595542154,7786772727⟩,⟨-155191598860,16518734928⟩,⟨-30866585302,162075836164⟩,⟨-1516529834758,4315034527097⟩,⟨-4484599859281,2736227094513⟩,⟨-4026974258915,4724994160545⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7786772727,-1595542154⟩,⟨-16518734928,155191598860⟩,⟨-162075836164,30866585302⟩,⟨-4315034527097,1516529834758⟩,⟨-2736227094513,4484599859281⟩,⟨-4724994160545,4026974258915⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754336610889,760527860726⟩,⟨-16518734928,155191598860⟩,⟨-162075836164,30866585302⟩,⟨-4315034527097,1516529834758⟩,⟨-2736227094513,4484599859281⟩,⟨-4724994160545,4026974258915⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8861657098,9908268807⟩,⟨-155726994136,-120969939800⟩,⟨111897557034,149932949216⟩,⟨2110527101605,3463384268934⟩,⟨-2520043983342,-961400791510⟩,⟨-220143688523,1604291116782⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9908268807,-8861657098⟩,⟨120969939800,155726994136⟩,⟨-149932949216,-111897557034⟩,⟨-3463384268934,-2110527101605⟩,⟨961400791510,2520043983342⟩,⟨-1604291116782,220143688523⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1089603358969,1090649970678⟩,⟨120969939800,155726994136⟩,⟨-149932949216,-111897557034⟩,⟨-3463384268934,-2110527101605⟩,⟨961400791510,2520043983342⟩,⟨-1604291116782,220143688523⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9953183168,-8897560960⟩,⟨121952834545,157143091936⟩,⟨-151296359077,-112806737620⟩,⟨-3517337446660,-2141201832657⟩,⟨981724294926,2564583310445⟩,⟨-1639698548886,210571909661⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4976591584,-4448780480⟩,⟨60976417272,78571545968⟩,⟨-75648179539,-56403368810⟩,⟨-1758668723330,-1070600916328⟩,⟨490862147463,1282291655223⟩,⟨-819849274443,105285954831⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4448780480,4976591584⟩,⟨-78571545968,-60976417272⟩,⟨56403368810,75648179539⟩,⟨1070600916328,1758668723330⟩,⟨-1282291655223,-490862147463⟩,⟨-105285954831,819849274443⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766572164096,767099994464⟩,⟨-78571545968,-60976417272⟩,⟨56403368810,75648179539⟩,⟨1070600916328,1758668723330⟩,⟨-1282291655223,-490862147463⟩,⟨-105285954831,819849274443⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272400839742,272662492670⟩,⟨30242484950,38931748534⟩,⟨-37483237304,-27974389258⟩,⟨-865846067234,-527631775401⟩,⟨240350197877,630010995836⟩,⟨-401072779196,55035922131⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533144328192,1534199988928⟩,⟨-157143091936,-121952834544⟩,⟨112806737620,151296359078⟩,⟨2141201832656,3517337446660⟩,⟨-2564583310446,-981724294926⟩,⟨-210571909662,1639698548886⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1207956453617,1214834688773⟩,⟨-1001312514465,-813191471703⟩,⟨752204549612,964057254263⟩,⟨9731974343734,16051181281741⟩,⟨-10216929990600,-2341399783189⟩,⟨-5021272849600,4551455823285⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1316401279458,1330157749770⟩,⟨-2002625028930,-1626382943406⟩,⟨1504409099224,1928114508526⟩,⟨19463948687472,32102362563471⟩,⟨-20433859981194,-4682799566378⟩,⟨-10037717790900,9102911646568⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨197951239488,209381579968⟩,⟨-1672673477111,-1344372092557⟩,⟨1243548216603,1610439274779⟩,⟨13544329746924,25169429692929⟩,⟨-15546701354883,-1420872094800⟩,⟨-10742695999246,6196666559908⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨67720903471,72196161077⟩,⟨-568917024205,-447494772850⟩,⟨412175623039,549170025891⟩,⟨4268256488068,8328031138004⟩,⟨-5183141071428,-97121514026⟩,⟨-4057236915057,2138534535773⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379832092626,380458726100⟩,⟨3200572898,24109825638⟩,⟨-24354569361,-1487873147⟩,⟨-688807231355,129815833509⟩,⟨-294631739329,646578704724⟩,⟨-622169927591,477674807838⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177547882807,3182790088265⟩,⟨-202027463083,-26730819766⟩,⟨12426546807,204078284777⟩,⟨-1087337616171,5797484112722⟩,⟨-5443891963181,2468647554286⟩,⟨-4002562595344,5239622440743⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨195710902922,208988445490⟩,⟨-1660127120843,-1294889719521⟩,⟨1191937658684,1603099539260⟩,⟨12285464953941,24697151078595⟩,⟨-15567756387912,-133659333939⟩,⟨-11998107996531,6738386676676⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨393662142410,418370025458⟩,⟨-3332800597954,-2639261812078⟩,⟨2435485875287,3213538814039⟩,⟨25829794700865,49866580771524⟩,⟨-31114457742795,-1554531428739⟩,⟨-22740803995777,12935053236584⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517524060821,526054124694⟩,⟨-22851887728,214690834918⟩,⟨-224214434554,42700590872⟩,⟨-5974047865925,2141764750038⟩,⟨-3831027691926,6212673491822⟩,⟨-6545619596154,5618666718874⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355055222910,363869565335⟩,⟨-23709841055,222751206909⟩,⟨-232632361425,44303745691⟩,⟨-6203176232258,2267629466756⟩,⟨-4022330574357,6454963185790⟩,⟨-6800810482528,5879190651011⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨710110445820,727739130670⟩,⟨-47419682110,445502413818⟩,⟨-465264722850,88607491382⟩,⟨-12406352464516,4535258933512⟩,⟨-8044661148714,12909926371580⟩,⟨-13601620965056,11758381302022⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523236059385,1525338331830⟩,⟨-36173152136,33774159592⟩,⟨-37126211596,39398802044⟩,⟨-1322182436278,1406810345055⟩,⟨-1603182518936,1538319688416⟩,⟨-1814863026444,1859842237409⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨983769348039,1009583130857⟩,⟨-89726815619,640394033563⟩,⟨-670028669597,149001110042⟩,⟨-18115605891826,7250208157379⟩,⟨-12250695737056,18959220452809⟩,⟨-20103909646059,17574654272159⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67486523668,67616233454⟩,⟨14984977126,19308986520⟩,⟨-18590568138,-13861148772⟩,⟨-427770172001,-258681498323⟩,⟨116437709518,310927777698⟩,⟨-197496660374,29851844001⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50464511291,51182599275⟩,⟨258194616712,266458080744⟩,⟨31709347270,36772654128⟩,⟨-1382689463401,-1171791720100⟩,⟨-279655019830,-93676089537⟩,⟨-261682323151,-77361454755⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137795973855,2140740985876⟩,⟨-438538208816,-340098807260⟩,⟨314592416478,422221769300⟩,⟨5998379381897,9860728865653⟩,⟨-7200212829332,-2762830510658⟩,⟨-564494369283,4617533857195⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2980914152565,2987076001618⟩,⟨-917869304127,-711343851492⟩,⟨657995195545,883718667573⟩,⟨12602673461425,20732718485178⟩,⟨-15160706894703,-5831020686062⟩,⟨-1133094778403,9751739993139⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136815629875,139049292552⟩,⟨657270948333,691245912643⟩,⟨116168164841,141038736817⟩,⟨-3622843126258,-2545845205866⟩,⟨-1341665535918,-327947654516⟩,⟨-725713586873,303320945733⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8694224885484,8836167481151⟩,⟨-44643763730470,-41096659541543⟩,⟨-9108914683094,-7263554751879⟩,⟨547700963637202,685094876327846⟩,⟨89173396509471,178694360344658⟩,⟨-7453213709340,65650002463301⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7779009999737,8113461836181⟩,⟨-41713457840714,-31624044849442⟩,⟨-13748551415302,-5301502605555⟩,⟨292456836520997,694613635680553⟩,⟨-30020974112891,344392514801006⟩,⟨-170876435993928,212620026625668⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15558019999474,16226923672362⟩,⟨-83426915681428,-63248089698884⟩,⟨-27497102830604,-10603005211110⟩,⟨584913673041994,1389227271361106⟩,⟨-60041948225782,688785029602012⟩,⟨-341752871987856,425240053251336⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10867759718499,10909882818322⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108414,2148278590204846⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9768248090723,9810371190546⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108424,2148278590204831⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2401631390336,2406362620352⟩,⟨-12184942684160,-12039116462039⟩,⟨0,0⟩,⟨102958094106835,109987257462969⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7218348203014,7306745939494⟩,⟨-42505984395808,-41317121223313⟩,⟨-19384701496018,-18899991383939⟩,⟨472990345760594,494545376127236⟩,⟨263752228204619,274092233135193⟩,⟨98972691332306,102854719515742⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6118836575238,6207234311718⟩,⟨-42505984395809,-41317121223312⟩,⟨-19384701496019,-18899991383938⟩,⟨472990345760595,494545376127238⟩,⟨263752228204618,274092233135194⟩,⟨98972691332305,102854719515743⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1887318160704,1903089000320⟩,⟨-7638024568683,-7318662858502⟩,⟨-3483293667651,-3347829201846⟩,⟨30723232288440,40151197557145⟩,⟨22521915591667,26968328851134⟩,⟨6496215210571,8288684594941⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99599284960,100028781692⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨140251227917,142277412297⟩,⟨666005413033,673411165917⟩,⟨304859617163,306906104007⟩,⟨-1685130754132,-1671622746438⟩,⟨-1537102693014,-1529215052672⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4288949551040,4309451620672⟩,⟨-19822967252843,-19357779320541⟩,⟨-3483293667651,-3347829201846⟩,⟨133681326395275,150138455020114⟩,⟨22521915591667,26968328851134⟩,⟨6496215210571,8288684594941⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨787324284820,836740050916⟩,⟨-6665601195908,-5278523624156⟩,⟨4870971750574,6427077628078⟩,⟨51659589401730,99733161543048⟩,⟨-62228915485590,-3109062857478⟩,⟨-45481607991554,25870106473168⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5076273835860,5146191671588⟩,⟨-26488568448751,-24636302944697⟩,⟨1387678082923,3079248426232⟩,⟨185340915797005,249871616563162⟩,⟨-39706999893923,23859265993656⟩,⟨-38985392780983,34158791068109⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459834376954,468178116774⟩,⟨1639306899847,1877232369251⟩,⟨125702849630,280136617770⟩,⟨-35802205155165,-26722917735936⟩,⟨-2505479908904,4629199575415⟩,⟨-3546721330773,3107618117260⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨40242711235,42356960260⟩,⟨-854779314225,-812036556123⟩,⟨325509421405,328085365043⟩,⟨10014139166459,10764552341627⟩,⟨-6627114036394,-6561817940510⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨500077088189,510535077034⟩,⟨784527585622,1065195813128⟩,⟨451212271035,608221982813⟩,⟨-25788065988706,-15958365394309⟩,⟨-9132593945298,-1932618365095⟩,⟨-3546721330773,3107618117260⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502387216868,503376923070⟩,⟨2513460839922,2553938535635⟩,⟨0,0⟩,⟨2096765778922,4420352332343⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228494479010,233732476952⟩,⟨1501631057546,1673534095891⟩,⟨206167239468,278455363743⟩,⟨-7265784056823,-290715058699⟩,⟨-3149609861880,529725001269⟩,⟨-1623755152170,1422725514152⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-836740050916,-787324284820⟩,⟨5278523624156,6665601195908⟩,⟨-6427077628078,-4870971750574⟩,⟨-99733161543048,-51659589401730⟩,⟨3109062857478,62228915485590⟩,⟨-25870106473168,45481607991554⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3452209500124,3522127335852⟩,⟨-14544443628687,-12692178124633⟩,⟨-9910371295729,-8218800952420⟩,⟨33948164852227,98478865618384⟩,⟨25630978449145,89197244336724⟩,⟨-19373891262597,53770292586495⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨440356071903,455765223820⟩,⟨209042274234,538190132670⟩,⟨-325219585907,-65242190539⟩,⟨-18883615458232,-7881310401096⟩,⟨-11783984910679,-1756703669622⟩,⟨-9162228108746,1302037547845⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨330906761950,334959130708⟩,⟨1917273400934,1925004342068⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-334959130708,-330906761950⟩,⟨-1925004342068,-1917273400934⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨764552497068,768604865826⟩,⟨-1925004342068,-1917273400934⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1312358847397,1330339242255⟩,⟨-8671192915924,-8380090432440⟩,⟨-3954466381119,-3833365739923⟩,⟨46887434311561,54812395983606⟩,⟨31110949830250,34855144455940⟩,⟨9858018890357,11356523673329⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1330339242255,-1312358847397⟩,⟨8380090432440,8671192915924⟩,⟨3833365739923,3954466381119⟩,⟨-54812395983606,-46887434311561⟩,⟨-34855144455940,-31110949830250⟩,⟨-11356523673329,-9858018890357⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-230827614479,-212847219621⟩,⟨8380090432440,8671192915924⟩,⟨3833365739923,3954466381119⟩,⟨-54812395983606,-46887434311561⟩,⟨-34855144455940,-31110949830250⟩,⟨-11356523673329,-9858018890357⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11896976977,-10494878799⟩,⟨439720702448,476492643707⟩,⟨96861429972,118925825141⟩,⟨-5047052978771,-4400358999150⟩,⟨1251944443073,1680866438213⟩,⟨2472386922046,2671323943857⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428459094926,445270345021⟩,⟨648762976682,1014682776377⟩,⟨-228358155935,53683634602⟩,⟨-23930668437003,-12281669400246⟩,⟨-10532040467606,-75837231409⟩,⟨-6689841186700,3973361491702⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100028781692,-99599284960⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4910951742,5155536159⟩,⟨30427731326,32835976694⟩,⟨39722996071,39933365192⟩,⟨-338298467783,-327000354974⟩,⟨249756374792,250871388573⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10726849595,11283272671⟩,⟨9328034216,18091438468⟩,⟨86765789348,87397126939⟩,⟨-1008316343158,-864872196412⟩,⟨102988436616,114103164432⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1452541214444,1470384149027⟩,⟨-7323842364762,-7022926760542⟩,⟨-1370814071850,-1301760630281⟩,⟨99819218730237,106942032859521⟩,⟨20883960400582,22602509480640⟩,⟨4640742911871,5064669560783⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14171010787,15089194935⟩,⟨-62834766371,-44321963941⟩,⟨100557023031,104176760608⟩,⟨-615604502999,-164278932067⟩,⟨-264907365188,-180704673545⟩,⟨-172649262523,-153477712604⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-15089194935,-14171010787⟩,⟨44321963941,62834766371⟩,⟨-104176760608,-100557023031⟩,⟨164278932067,615604502999⟩,⟨180704673545,264907365188⟩,⟨153477712604,172649262523⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115117976627,-113770295747⟩,⟨-833569351363,-814197555471⟩,⟨-104176760608,-100557023031⟩,⟨2363302187619,2814627758551⟩,⟨180704673545,264907365188⟩,⟨153477712604,172649262523⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨93058182236,98086210662⟩,⟨-637501092315,-596039566052⟩,⟨573184770780,594677068011⟩,⟨3338821446462,4026657691374⟩,⟨-3424670408725,-2969947854281⟩,⟨-2460882765243,-2243213711757⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨122937167397,131171336212⟩,⟨-1505886253812,-1381806972350⟩,⟨634933299096,685089850444⟩,⟨20473321677351,23417840040197⟩,⟨-6067764802303,-4773497816099⟩,⟨-4381006235324,-3868885742681⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-131171336212,-122937167397⟩,⟨1381806972350,1505886253812⟩,⟨-685089850444,-634933299096⟩,⟨-23417840040197,-20473321677351⟩,⟨4773497816099,6067764802303⟩,⟨3868885742681,4381006235324⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨968340291564,976574460379⟩,⟨1381806972350,1505886253812⟩,⟨-685089850444,-634933299096⟩,⟨-23417840040197,-20473321677351⟩,⟨4773497816099,6067764802303⟩,⟨3868885742681,4381006235324⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123519307574,126369274893⟩,⟨762811396685,792979103949⟩,⟨179838970740,191600054736⟩,⟨-2852997106572,-2239127685809⟩,⟨-792803178387,-525868023347⟩,⟨-200235487313,-93244921087⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11772208558,12052758887⟩,⟨168495710898,174548071496⟩,⟨20809970464,21814444868⟩,⟨616461705815,774824501983⟩,⟨93455459978,120562127662⟩,⟨-17759373601,-12020622856⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166576006616,177878244814⟩,⟨1469684448767,1898850796801⟩,⟨-6961285037,208420299844⟩,⟨-11502711632284,7278664016310⟩,⟨-5356166487331,6507762510300⟩,⟨-5099457696233,4089999756242⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177878244814,-166576006616⟩,⟨-1898850796801,-1469684448767⟩,⟨-208420299844,6961285037⟩,⟨-7278664016310,11502711632284⟩,⟨-6507762510300,5356166487331⟩,⟨-4089999756242,5099457696233⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50616234196,67156470336⟩,⟨-397219739255,203849647124⟩,⟨-2253060376,285416648780⟩,⟨-14544448073133,11211996573585⟩,⟨-9657372372180,5885891488600⟩,⟨-5713754908412,6522183210385⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26705432619204,28086360498405⟩,⟨-257123690287331,-212124333702850⟩,⟨-99000839701135,-65571692148396⟩,⟨2280734179175052,4156197265287114⟩,⟨477916604774967,2045504717308826⟩,⟨-435032947639002,1032577063998982⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13876178257,14523897005⟩,⟨171388702306,182277643710⟩,⟨40406275984,44042026252⟩,⟨402633397758,640721478666⟩,⟨67297612372,158215672134⟩,⟨12802851517,45825859868⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337030854511,371004177509⟩,⟨766314265862,1979097346459⟩,⟨-326336629355,297491840257⟩,⟨-46689299519182,5137086992059⟩,⟨-19045746968195,13044883094743⟩,⟨-13366719212123,9990898223148⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371004177509,-337030854511⟩,⟨-1979097346459,-766314265862⟩,⟨-297491840257,326336629355⟩,⟨-5137086992059,46689299519182⟩,⟨-13044883094743,19045746968195⟩,⟨-9990898223148,13366719212123⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57454917417,108239490510⟩,⟨-1330334369777,248368510515⟩,⟨-525849996192,380020263957⟩,⟨-29067755429062,34407630118936⟩,⟨-23576923562349,18969909736786⟩,⟨-16680739409848,17340080703825⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239850512877,242306193989⟩,⟨1543037734875,1551302481221⟩,⟨304859617163,306906104007⟩,⟨-3884154009684,-3870646001990⟩,⟨-1537102693014,-1529215052672⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1698945761785,-1609842489940⟩,⟨-5757567459763,-2786113438617⟩,⟨-440342140924,1456048872170⟩,⟨-18338914571614,107512449373858⟩,⟨-55922238496071,38946770638837⟩,⟨-40411170548818,43539861265122⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-195263550267,-180849956141⟩,⟨-1887026985857,-1429857548786⟩,⟨-346666472984,-95963129077⟩,⟨-7134161767738,12899180951603⟩,⟨-6978207600547,6295676322860⟩,⟨-4661487619617,5820991661274⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44586962610,61456237848⟩,⟨-343989250982,121444932435⟩,⟨-41806855821,210942974930⟩,⟨-11018315777422,9028534949613⟩,⟨-8515310293561,4766461270188⟩,⟨-5011958293150,5471206504790⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2644948431,6611100738⟩,⟨-120358365930,35237585012⟩,⟨-32339903354,51308390750⟩,⟨-3700504647045,4166527952393⟩,⟨-2873369486043,1992525160630⟩,⟨-1854319806531,1898465255663⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1808072952,3435042500⟩,⟨-38453954814,13576115914⟩,⟨-4673515060,23580945054⟩,⟨-1307707837344,1224522559050⟩,⟨-1083901316994,579433131594⟩,⟨-576319441259,692556035478⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3103567831,5945541123⟩,⟨-90420360207,11463162540⟩,⟨-18971492766,35309783673⟩,⟨-2401542560057,2779162046929⟩,⟨-2045854529266,1241453915160⟩,⟨-1136250167736,1254217029697⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5945541123,-3103567831⟩,⟨-11463162540,90420360207⟩,⟨-35309783673,18971492766⟩,⟨-2779162046929,2401542560057⟩,⟨-1241453915160,2045854529266⟩,⟨-1254217029697,1136250167736⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3300592692,3507532907⟩,⟨-131821528470,125657945219⟩,⟨-67649687027,70279883516⟩,⟨-6479666693974,6568070512450⟩,⟨-4114823401203,4038379689896⟩,⟨-3108536836228,3034715423399⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50616234196,67156470336⟩,⟨-397219739255,203849647124⟩,⟨-2253060376,285416648780⟩,⟨-14544448073133,11211996573585⟩,⟨-9657372372180,5885891488600⟩,⟨-5713754908412,6522183210385⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3300592692,3507532907⟩,⟨-131821528470,125657945219⟩,⟨-67649687027,70279883516⟩,⟨-6479666693974,6568070512450⟩,⟨-4114823401203,4038379689896⟩,⟨-3108536836228,3034715423399⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (517/5120) u, BivariateJet2.affineZ (647/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000029

end


