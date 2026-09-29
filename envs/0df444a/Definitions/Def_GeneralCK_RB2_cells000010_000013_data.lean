-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000010_000013_data
-- name    : GeneralCK_RB2_cells000010_000013_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T00:43:32.547032+00:00
-- url     : https://prove2.me/theorems/2a1b757c-460a-4e91-a0b6-97b1eba3d8b5
-- title:
--   Exact certificate data for RB2 cells 000010–000013
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000010 through 000013. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000010Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2146700736768,-2146700697472⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2146700736768,-2146700697472⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-168303328064,-168303328000⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-168303328064,-168303328000⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨80571063360,80571063424⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-86945409408,-86945409344⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨80571187328,80571187392⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-86945553728,-86945553664⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6374366400,-6374366336⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6374345984,-6374345920⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨167516472704,167516472768⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨167516741056,167516741120⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1978397369472,1978397408064⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1978397369472,1978397408064⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2518909148928,-2518909091072⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2153816409280,-2153816369856⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2139625533440,-2139625494208⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-169478021888,-169478021824⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-167130766848,-167130766784⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨77988924864,77988924928⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-83945941248,-83945941184⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨83176442496,83176442560⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-89987367936,-89987367872⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-6810925440,-6810925376⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-5957016384,-5957016320⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨161934866048,161934866112⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨173163810368,173163810432⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1970147472384,1970147510976⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1986685603072,1986685641664⟩



end LaneCBRB2Cell000010Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000010
open Set LaneCBRB2Cell000010Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111454401331,111454401332⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111454401332,-111454401331⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438301412556,438301412557⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨44600592957,44600592958⟩,⟨-111883898061,-111883898060⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156054994288,156054994290⟩,⟨987627729715,987627729716⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44600592956,44600592959⟩,⟨-111883898061,-111883898060⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2146700736768,-2146700697472⟩,⟨6958496763760,6958496763858⟩,⟨3088126091500,3088126091548⟩,⟨-44038349381132,-44038349379903⟩,⟨-27290666344375,-27290666343704⟩,⟨-8673416921100,-8673416920835⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-304683791200,-304683785618⟩,⟨-940629436002,-940629400675⟩,⟨-417443939745,-417443924064⟩,⟨6250415354615,6250415355060⟩,⟨3821074205304,3821074244839⟩,⟨1231028389169,1231028389267⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨304683785618,304683791200⟩,⟨940629400675,940629436002⟩,⟨417443924064,417443939745⟩,⟨-6250415355060,-6250415354615⟩,⟨-3821074244839,-3821074205304⟩,⟨-1231028389267,-1231028389169⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-156054994290,-156054994288⟩,⟨-987627729716,-987627729715⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨943456633486,943456633488⟩,⟨-987627729716,-987627729715⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-168303328064,-168303328000⟩,⟨-1150988963557,-1150988963553⟩,⟨-510799842275,-510799842271⟩,⟨-1204876383992,-1204876383981⟩,⟨746664664854,746664664864⟩,⟨-237302155136,-237302155132⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-144415836349,-144415836293⟩,⟨-836450580213,-836450580148⟩,⟨-371210183566,-371210183534⟩,⟨1033866844400,1033866844424⟩,⟨1390030267400,1390030267484⟩,⟨203621577745,203621577755⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144415836293,144415836349⟩,⟨836450580148,836450580213⟩,⟨371210183534,371210183566⟩,⟨-1033866844424,-1033866844400⟩,⟨-1390030267484,-1390030267400⟩,⟨-203621577755,-203621577745⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨449099621911,449099627549⟩,⟨1777079980823,1777080016215⟩,⟨788654107598,788654123311⟩,⟨-7284282199484,-7284282199015⟩,⟨-5211104512323,-5211104472704⟩,⟨-1434649967022,-1434649966914⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨809823711564,809823723128⟩,⟨4176351861643,4176351954979⟩,⟨788654107598,788654123311⟩,⟨-19354640371477,-19354640370502⟩,⟨-5211104512323,-5211104472704⟩,⟨-1434649967022,-1434649966914⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89201185912,89201185918⟩,⟨-223767796122,-223767796120⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13552799855440,13552799856353⟩,⟨33998204437493,33998204442379⟩,⟨-133186823928603,-133186823910353⟩,⟨170574038914868,170574038952391⟩,⟨-334109034126974,-334109033939412⟩,⟨2617721836452469,2617721836993460⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9982048760336,9982048903549⟩,⟨76519257173297,76519258688417⟩,⟨-88375034783903,-88375033175343⟩,⟨145339311379091,145339319038054⟩,⟨-791821282604850,-791821266595334⟩,⟨1719284240468474,1719284272233973⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨83596594176,83596727552⟩,⟨-635494472717,-635492407671⟩,⟨733954623781,733957007609⟩,⟨8414489691745,8414541416899⟩,⟨-4536262436232,-4536185918680⟩,⟨-1444698823188,-1444588773921⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1183108221952,1183108355328⟩,⟨-635494472717,-635492407671⟩,⟨733954623781,733957007609⟩,⟨8414489691745,8414541416899⟩,⟨-4536262436232,-4536185918680⟩,⟨-1444698823188,-1444588773921⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨80571063360,80571187392⟩,⟨-590591417738,-590589432024⟩,⟨682094450159,682096742446⟩,⟨7502703868138,7502754953264⟩,⟨-3849358338704,-3849284289370⟩,⟨-1765766478464,-1765661209660⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨86696934443,86697077679⟩,⟨-682062987070,-682060555726⟩,⟨787737969063,787740775858⟩,⟨9372438594767,9372503727462⟩,⟨-5262916132185,-5262824655100⟩,⟨-1095251193637,-1095123461701⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-83596727552,-83596594176⟩,⟨635492407671,635494472717⟩,⟨-733957007609,-733954623781⟩,⟨-8414541416899,-8414489691745⟩,⟨4536185918680,4536262436232⟩,⟨1444588773921,1444698823188⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1015914900224,1015915033600⟩,⟨635492407671,635494472717⟩,⟨-733957007609,-733954623781⟩,⟨-8414541416899,-8414489691745⟩,⟨4536185918680,4536262436232⟩,⟨1444588773921,1444698823188⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-86945553728,-86945409344⟩,⟨687785167546,687787492817⟩,⟨-794352227708,-794349543433⟩,⟨-9537187886741,-9537127800562⟩,⟨5406350024928,5406436842467⟩,⟨989572612325,989695801048⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-80335025939,-80334881985⟩,⟨585239632565,585242111225⟩,⟨-675918622527,-675915761094⟩,⟨-7351633755726,-7351566614391⟩,⟨3718351578370,3718445184072⟩,⟨1860593750428,1860723613178⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6361908504,6362195694⟩,⟨-96823354505,-96818444501⟩,⟨111819346536,111825014764⟩,⟨2020804839041,2020937113071⟩,⟨-1544564553815,-1544379471028⟩,⟨765342556791,765600151477⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3180954252,3181097847⟩,⟨-48411677253,-48409222250⟩,⟨55909673268,55912507382⟩,⟨1010402419520,1010468556536⟩,⟨-772282276908,-772189735514⟩,⟨382671278395,382800075739⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3181097847,-3180954252⟩,⟨48409222250,48411677253⟩,⟨-55912507382,-55909673268⟩,⟨-1010468556536,-1010402419520⟩,⟨772189735514,772282276908⟩,⟨-382800075739,-382671278395⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758942285769,758942448628⟩,⟨48409222250,48411677253⟩,⟨-55912507382,-55909673268⟩,⟨-1010468556536,-1010402419520⟩,⟨772189735514,772282276908⟩,⟨-382800075739,-382671278395⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6355904186,6355924468⟩,⟨-96634281904,-96633813710⟩,⟨111606108162,111606648716⟩,⟨2014118363451,2014133044501⟩,⟨-1538214412966,-1538196164506⟩,⟨760187132713,760210582546⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6355924468,-6355904186⟩,⟨96633813710,96634281904⟩,⟨-111606648716,-111606108162⟩,⟨-2014133044501,-2014118363451⟩,⟨1538196164506,1538214412966⟩,⟨-760210582546,-760187132713⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1093155703308,1093155723590⟩,⟨96633813710,96634281904⟩,⟨-111606648716,-111606108162⟩,⟨-2014133044501,-2014118363451⟩,⟨1538196164506,1538214412966⟩,⟨-760210582546,-760187132713⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6374366400,-6374345920⟩,⟨97195668940,97196141661⟩,⟨-112255562158,-112255016377⟩,⟨-2034435876739,-2034420989162⟩,⟨1557062879773,1557081359553⟩,⟨-776091493274,-776067781464⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3187183200,-3187172960⟩,⟨48597834470,48598070831⟩,⟨-56127781079,-56127508188⟩,⟨-1017217938370,-1017210494581⟩,⟨778531439886,778540679777⟩,⟨-388045746637,-388033890732⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3187172960,3187183200⟩,⟨-48598070831,-48597834470⟩,⟨56127508188,56127781079⟩,⟨1017210494581,1017217938370⟩,⟨-778540679777,-778531439886⟩,⟨388033890732,388045746637⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765310556576,765310586080⟩,⟨-48598070831,-48597834470⟩,⟨56127508188,56127781079⟩,⟨1017210494581,1017217938370⟩,⟨-778540679777,-778531439886⟩,⟨388033890732,388045746637⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273288925827,273288930898⟩,⟨24158453427,24158570476⟩,⟨-27901662179,-27901527040⟩,⟨-503533261126,-503529590862⟩,⟨384549041126,384553603242⟩,⟨-190052645637,-190046783178⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530621113152,1530621172160⟩,⟨-97196141662,-97195668940⟩,⟨112255016376,112255562158⟩,⟨2034420989162,2034435876740⟩,⟨-1557081359554,-1557062879772⟩,⟨776067781464,776091493274⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1189987134387,1189987290617⟩,⟨-744383555773,-744380941434⟩,⟨859714179469,859717197496⟩,⟨10787547173267,10787616768516⟩,⟨-6389103751517,-6389005315779⟩,⟨-450028845569,-449890937052⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1280462640998,1280462953458⟩,⟨-1488767111546,-1488761882868⟩,⟨1719428358939,1719434394992⟩,⟨21575094346541,21575233537023⟩,⟨-12778207503030,-12778010631561⟩,⟨-900057540451,-899782024793⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨167516472704,167516741120⟩,⟨-1278379155928,-1278374354198⟩,⟨1476443710202,1476449253545⟩,⟨17039819650848,17039954857878⟩,⟨-9255807058076,-9255622437421⟩,⟨-2755473879076,-2755222222472⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57702882501,57702986947⟩,⟨-434972103091,-434970391026⟩,⟨502364034378,502366010802⟩,⟨5675346500531,5675391621120⟩,⟨-3007834806019,-3007770701089⟩,⟨-1100960479791,-1100870438727⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380443270716,380443292443⟩,⟨9472213818,9472496004⟩,⟨-10940149902,-10939824102⟩,⟨-199570589063,-199561701462⟩,⟨153240395306,153251415137⟩,⟨-77372630057,-77358506215⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177676788179,3177676969656⟩,⟨-79119634159,-79117268144⟩,⟨91375576350,91378308054⟩,⟨1670791496479,1670866156542⟩,⟨-1284592714295,-1284500252404⟩,⟨651396936034,651515294050⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨166765958360,166766269742⟩,⟨-1261256578485,-1261251426999⟩,⟨1456667783171,1456673730155⟩,⟨16552488580726,16552626114905⟩,⟨-8832599867732,-8832406682212⟩,⟨-3064180122161,-3063910616441⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨334282431064,334283010862⟩,⟨-2539635734413,-2539625781197⟩,⟨2933111493373,2933122983700⟩,⟨33592308231574,33592580972783⟩,⟨-18088406925808,-18088029119633⟩,⟨-5819654001237,-5819132838913⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523862939306,523863164135⟩,⟨66829317414,66832720908⟩,⟨-77187678948,-77183749866⟩,⟨-1390697485042,-1390605450655⟩,⟨1061090414906,1061218897068⟩,⟨-522772707431,-522594211798⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361598482947,361598715731⟩,⟨69193804275,69197343039⟩,⟨-79918671961,-79914586713⟩,⟨-1435488501854,-1435392452972⟩,⟨1093534955944,1093668738446⟩,⟨-535381897034,-535196370929⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨723196965894,723197431462⟩,⟨138387608550,138394686078⟩,⟨-159837343922,-159829173426⟩,⟨-2870977003708,-2870784905944⟩,⟨2187069911888,2187337476892⟩,⟨-1070763794068,-1070392741858⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524265188684,1524265267974⟩,⟨-562327952,-561387036⟩,⟨648367660,649453996⟩,⟨20287944661,20317513289⟩,⟨-18885195048,-18848466806⟩,⟨15857198918,15904360561⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002575990854,1002576688430⟩,⟨191478411694,191488852452⟩,⟨-221157837897,-221145784714⟩,⟨-3966864822617,-3966578607035⟩,⟨3019700906800,3020096440512⟩,⟨-1474170673975,-1473624850460⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67927282525,67927285047⟩,⟨12009400572,12009458984⟩,⟨-13870186062,-13870118624⟩,⟨-249249634605,-249247795147⟩,⟨189936927388,189939210690⟩,⟨-93060933305,-93058003546⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50030506873,50030509446⟩,⟨266858233020,266858291516⟩,⟨38506845761,38506898359⟩,⟨-1288067756568,-1288065908891⟩,⟨-226115180071,-226113182547⟩,⟨-177071694997,-177069435721⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130765089556,2130765253846⟩,⟨-270611912640,-270610586060⟩,⟨312538574002,312540105610⟩,⟨5681385513727,5681427348999⟩,⟨-4355047173216,-4354995361958⟩,⟨2183636607236,2183702931460⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966220593627,2966220936687⟩,⟨-565074955728,-565072163861⟩,⟨652623575718,652626799087⟩,⟨11899397754223,11899485919818⟩,⟨-9135381016850,-9135272072573⟩,⟨4607596998397,4607736135567⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134970395989,134970418542⟩,⟨694207663811,694208033243⟩,⟨133578293736,133578595848⟩,⟨-3207742812088,-3207731970670⟩,⟨-887081712000,-887070332127⟩,⟨-222328167146,-222315386821⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8956968739327,8956970236001⟩,⟨-46069366884408,-46069326971977⟩,⟨-8864606926656,-8864583915279⟩,⟨686779486111651,686781018671172⟩,⟨150056476331573,150057551679618⟩,⟨32299699484412,32300640713252⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8167300446874,8167307494274⟩,⟨-40447964366866,-40447813430516⟩,⟨-9884708950506,-9884583853714⟩,⟨577869280500087,577874339503815⟩,⟨169148689677195,169153592914335⟩,⟨21008901146619,21014431954252⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16334600893748,16334614988548⟩,⟨-80895928733732,-80895626861032⟩,⟨-19769417901012,-19769167707428⟩,⟨1155738561000174,1155748679007630⟩,⟨338297379354390,338307185828670⟩,⟨42017802293238,42028863908504⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10846819911700,10846819911799⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738054,2111240126795878⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9747308283924,9747308284023⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738069,2111240126795861⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2399271880896,2399271938752⟩,⟨-12070358171930,-12070358171514⟩,⟨0,0⟩,⟨105643681588589,105643681622780⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7746793526954,7746793527054⟩,⟨-49027255671061,-49027255669744⟩,⟨-21757910159731,-21757910159118⟩,⟨620559148799615,620559148824917⟩,⟨329980598331615,329980598344604⟩,⟨122220026348994,122220026354288⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6647281899178,6647281899278⟩,⟨-49027255671061,-49027255669743⟩,⟨-21757910159731,-21757910159117⟩,⟨620559148799615,620559148824912⟩,⟨329980598331613,329980598344603⟩,⟨122220026348993,122220026354288⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1978397369472,1978397408064⟩,⟨-8109485727545,-8109485727192⟩,⟨-3598925933880,-3598925933718⟩,⟨42833472989529,42833473002635⟩,⟨28037331005557,28037331011851⟩,⟨8436114764400,8436114767092⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100156582133,100156582135⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133905923166,133905923169⟩,⟨707277370831,707277370838⟩,⟨313884129998,313884130003⟩,⟨-1774257784753,-1774257784749⟩,⟨-1574803278400,-1574803278392⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4377669250368,4377669346816⟩,⟨-20179843899475,-20179843898706⟩,⟨-3598925933880,-3598925933718⟩,⟨148477154578118,148477154625415⟩,⟨28037331005557,28037331011851⟩,⟨8436114764400,8436114767092⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨668564862128,668566021724⟩,⟨-5079271468826,-5079251562394⟩,⟨5866222986746,5866245967400⟩,⟨67184616463148,67185161945566⟩,⟨-36176813851616,-36176058239266⟩,⟨-11639308002474,-11638265677826⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5046234112496,5046235368540⟩,⟨-25259115368301,-25259095461100⟩,⟨2267297052866,2267320033682⟩,⟨215661771041266,215662316570981⟩,⟨-8139482846059,-8138727227415⟩,⟨-3203193238074,-3202150910734⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459670956252,459671070678⟩,⟨1722288667358,1722291482200⟩,⟨206532352872,206534446243⟩,⟨-30723883198910,-30723799250354⟩,⟨1066197200727,1066284353286⟩,⟨-291784896621,-291689949056⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32992543934,32992545808⟩,⟨-667771224066,-667771214622⟩,⟨324226151534,324226169925⟩,⟨8310101784138,8310101809330⟩,⟨-6562358286202,-6562358193788⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨492663500186,492663616486⟩,⟨1054517443292,1054520267578⟩,⟨530758504406,530760616168⟩,⟨-22413781414772,-22413697441024⟩,⟨-5496161085475,-5496073840502⟩,⟨-291784896621,-291689949056⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503871945521,503871957673⟩,⟨2534900173993,2534900296365⟩,⟨0,0⟩,⟨3319096918590,3319099843609⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225772342970,225772401712⟩,⟨1619077509601,1619079138499⟩,⟨243230097309,243231070931⟩,⟨-3922000463707,-3921946814337⟩,⟨-1295067359623,-1295022389529⟩,⟨-133715936572,-133672421834⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-668566021724,-668564862128⟩,⟨5079251562394,5079271468826⟩,⟨-5866245967400,-5866222986746⟩,⟨-67185161945566,-67184616463148⟩,⟨36176058239266,36176813851616⟩,⟨11638265677826,11639308002474⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3709103228644,3709104484688⟩,⟨-15100592337081,-15100572429880⟩,⟨-9465171901280,-9465148920464⟩,⟨81291992632552,81292538162267⟩,⟨64213389244823,64214144863467⟩,⟨20074380442226,20075422769566⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451719544752,451719697733⟩,⟨546884641517,546887873986⟩,⟨-93872532852,-93869375479⟩,⟨-15512380450209,-15512286373437⟩,⟨-7891589958574,-7891475669134⟩,⟨-4138178472999,-4138038011081⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨312109988576,312109988580⟩,⟨1975255459430,1975255459432⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-312109988580,-312109988576⟩,⟨-1975255459432,-1975255459430⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨787401639196,787401639200⟩,⟨-1975255459432,-1975255459430⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1416804781641,1416804809286⟩,⟨-9361667831530,-9361667761912⟩,⟨-4154634495358,-4154634464455⟩,⟨59811790157275,59811790168117⟩,⟨36966210622240,36966210704629⟩,⟨11780019008861,11780019011093⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1416804809286,-1416804781641⟩,⟨9361667761912,9361667831530⟩,⟨4154634464455,4154634495358⟩,⟨-59811790168117,-59811790157275⟩,⟨-36966210704629,-36966210622240⟩,⟨-11780019011093,-11780019008861⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-317293181510,-317293153865⟩,⟨9361667761912,9361667831530⟩,⟨4154634464455,4154634495358⟩,⟨-59811790168117,-59811790157275⟩,⟨-36966210704629,-36966210622240⟩,⟨-11780019011093,-11780019008861⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12870681565,-12870680441⟩,⟨412033776338,412033782002⟩,⟨42045131503,42045143790⟩,⟨-4331451315125,-4331451300335⟩,⟨2126897103862,2126897165862⟩,⟨2834502516530,2834502541300⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438848863187,438849017292⟩,⟨958918417855,958921655988⟩,⟨-51827401349,-51824231689⟩,⟨-19843831765334,-19843737673772⟩,⟨-5764692854712,-5764578503272⟩,⟨-1303675956469,-1303535469781⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100156582135,-100156582133⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4062751897,4062751898⟩,⟨25366804912,25366804916⟩,⟨39925700025,39925700027⟩,⟨-267603557749,-267603557740⟩,⟨249286067484,249286067488⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8865432742,8865432959⟩,⟨10752947819,10752949177⟩,⟨87122870713,87122872820⟩,⟨-750535474314,-750535459881⟩,⟨105671963339,105671976504⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1492825889250,1492825910568⟩,⟨-7698671107084,-7698670715144⟩,⟨-1453801973126,-1453801902638⟩,⟨115084086952795,115084094924763⟩,⟨24600968907853,24600970531534⟩,⟨5476224232832,5476224542712⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12036750846,12036751314⟩,⟨-47475417600,-47475410865⟩,⟨106566124501,106566129909⟩,⟨-241666756295,-241666608469⟩,⟨-282411678742,-282411592574⟩,⟨-186236967425,-186236947100⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12036751314,-12036750846⟩,⟨47475410865,47475417600⟩,⟨-106566129909,-106566124501⟩,⟨241666608469,241666756295⟩,⟨282411592574,282411678742⟩,⟨186236947100,186236967425⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112193333449,-112193332979⟩,⟨-829127414249,-829127407512⟩,⟨-106566129909,-106566124501⟩,⟨2440689864021,2440690011847⟩,⟨282411592574,282411678742⟩,⟨186236947100,186236967425⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨80251716809,80251718381⟩,⟨-530270595818,-530270591851⟩,⟨642667265282,642667280686⟩,⟨3387904182580,3387904183316⟩,⟨-3707579302480,-3707579263386⟩,⟨-2527097349483,-2527097349214⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨108959139205,108959142897⟩,⟨-1281872092153,-1281872036870⟩,⟨766449579947,766449620547⟩,⟨20425435634552,20425436881243⟩,⟨-7037011608326,-7037010953489⟩,⟨-4730883962995,-4730883760047⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-108959142897,-108959139205⟩,⟨1281872036870,1281872092153⟩,⟨-766449620547,-766449579947⟩,⟨-20425436881243,-20425435634552⟩,⟨7037010953489,7037011608326⟩,⟨4730883760047,4730883962995⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨990552484879,990552488571⟩,⟨1281872036870,1281872092153⟩,⟨-766449620547,-766449579947⟩,⟨-20425436881243,-20425435634552⟩,⟨7037010953489,7037011608326⟩,⟨4730883760047,4730883962995⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120636145704,120636146157⟩,⟨793302766080,793302775199⟩,⟨189435523617,189435529624⟩,⟨-2436813045106,-2436812816115⟩,⟨-688815854858,-688815727881⟩,⟨-176260685830,-176260636735⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11448122645,11448122742⟩,⟨169207064232,169207066318⟩,⟨21747853116,21747854312⟩,⟨752376053319,752376105897⟩,⟨103086107432,103086134724⟩,⟨-17349898000,-17349891595⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170075977065,170076125262⟩,⟨1671490591579,1671495941899⟩,⟨117251855296,117254758616⟩,⟨-1687591258221,-1687382162463⟩,⟨411366485006,411514946299⟩,⟨-602325408804,-602199973468⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170076125262,-170075977065⟩,⟨-1671495941899,-1671490591579⟩,⟨-117254758616,-117251855296⟩,⟨1687382162463,1687591258221⟩,⟨-411514946299,-411366485006⟩,⟨602199973468,602325408804⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨55696217708,55696424647⟩,⟨-52418432298,-52411453080⟩,⟨125975338693,125979215635⟩,⟨-2234618301244,-2234355556116⟩,⟨-1706582305922,-1706388874535⟩,⟨468484036896,468652986970⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29391532225023,29391558159721⟩,⟨-266035952194506,-266035302220989⟩,⟨-89038471411666,-89037974396404⟩,⟨3909209843096293,3909233091697288⟩,⟨1435837848759610,1435858698762967⟩,⟨330350319926610,330371971088825⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13235948836,13235948936⟩,⟨174079083218,174079085876⟩,⟨41568949070,41568950546⟩,⟨610019094898,610019173474⟩,⟨122206319676,122206359922⟩,⟨26598004750,26598019813⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353816009685,353816324561⟩,⟨1450837504050,1450849529783⟩,⟨39350602679,39357613823⟩,⟨-20873897827514,-20873394016392⟩,⟨-3603476002845,-3603117085808⟩,⟨-2044740161521,-2044440644089⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353816324561,-353816009685⟩,⟨-1450849529783,-1450837504050⟩,⟨-39357613823,-39350602679⟩,⟨20873394016392,20873897827514⟩,⟨3603117085808,3603476002845⟩,⟨2044440644089,2044740161521⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨85032538626,85033007607⟩,⟨-491931111928,-491915848062⟩,⟨-91185015172,-91174834368⟩,⟨1029562251058,1030160153742⟩,⟨-2161575768904,-2161102500427⟩,⟨740764687620,741204691740⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234062505299,234062505304⟩,⟨1583880195943,1583880195952⟩,⟨313884129998,313884130003⟩,⟨-3973281040305,-3973281040301⟩,⟨-1574803278400,-1574803278392⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1666771737447,-1666770292241⟩,⟨-4063192215876,-4063150649641⟩,⟨434058267668,434085252113⟩,⟨40332416268707,40333938948147⟩,⟨-7576853060362,-7575628925484⟩,⟨2310293924856,2311474043674⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-182874754436,-182874595184⟩,⟨-1648388656540,-1648383037755⟩,⟨-239545143290,-239541924330⟩,⟨2255975353541,2256206033365⟩,⟨-174002803887,-173840736666⟩,⟨670245806732,670384897066⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51187750863,51187910120⟩,⟨-64508460597,-64502841803⟩,⟨74338986708,74342205673⟩,⟨-1717305686764,-1717075006936⟩,⟨-1748806082287,-1748644015058⟩,⟨320803157111,320942247447⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4307358525,4307398286⟩,⟨-28972955134,-28971527240⟩,⟨5123477900,5124364341⟩,⟨-73768699577,-73709245388⟩,⟨-293496085041,-293451469824⟩,⟨52859236253,52897906234⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2383045137,2383059967⟩,⟨-6006399932,-6005858078⟩,⟨6921701298,6922022554⟩,⟨-152330671960,-152307377317⟩,⟨-171555129424,-171538395242⟩,⟨39922228145,39936142386⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4287913025,4287939794⟩,⟨-28383907965,-28382823391⟩,⟨4654265760,4654892596⟩,⟨-92666292713,-92615801648⟩,⟨-279314374714,-279279736962⟩,⟨44803510208,44830764956⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4287939794,-4287913025⟩,⟨28382823391,28383907965⟩,⟨-4654892596,-4654265760⟩,⟨92615801648,92666292713⟩,⟨279279736962,279314374714⟩,⟨-44830764956,-44803510208⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨19418731,19485261⟩,⟨-590131743,-587619275⟩,⟨468585304,470098581⟩,⟨18847102071,18957047325⟩,⟨-14216348079,-14137095110⟩,⟨8028471297,8094396026⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨55696217708,55696424647⟩,⟨-52418432298,-52411453080⟩,⟨125975338693,125979215635⟩,⟨-2234618301244,-2234355556116⟩,⟨-1706582305922,-1706388874535⟩,⟨468484036896,468652986970⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨19418731,19485261⟩,⟨-590131743,-587619275⟩,⟨468585304,470098581⟩,⟨18847102071,18957047325⟩,⟨-14216348079,-14137095110⟩,⟨8028471297,8094396026⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111239652966,111669149696⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111669149696,-111239652966⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438086664192,438516160922⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨43808666418,45393274471⟩,⟨-113816633344,-109951162777⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨155048319384,157062424167⟩,⟨985694994432,989560464999⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨43379169688,45822771201⟩,⟨-113816633344,-109951162777⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2153816409280,-2139625494208⟩,⟨6900333504760,7017381690925⟩,⟨3066814891004,3109699091336⟩,⟨-44786834947555,-43305228679787⟩,⟨-27644034553048,-26943872342296⟩,⟨-8795021529887,-8554119245389⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-307667165955,-301720626328⟩,⟨-965379926482,-915725795419⟩,⟨-426533741500,-408294470309⟩,⟨5974397502973,6524573155688⟩,⟨3689449116002,3951767775460⟩,⟨1187521782869,1274206444126⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨301720626328,307667165955⟩,⟨915725795419,965379926482⟩,⟨408294470309,426533741500⟩,⟨-6524573155688,-5974397502973⟩,⟨-3951767775460,-3689449116002⟩,⟨-1274206444126,-1187521782869⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157062424167,-155048319384⟩,⟨-989560464999,-985694994432⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨942449203609,944463308392⟩,⟨-989560464999,-985694994432⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-169478021888,-167130766784⟩,⟨-1154474144058,-1147512135397⟩,⟨-511596398040,-510005393510⟩,⟨-1212184133054,-1197608163132⟩,⟨742843397829,750478754227⟩,⟨-238042843637,-236564575433⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145578972708,-143256564164⟩,⟨-841845130087,-831062741771⟩,⟨-372862147334,-369559825621⟩,⟨1016206169093,1051520559548⟩,⟨1381675829182,1398392273342⟩,⟨201935464687,205306133559⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨143256564164,145578972708⟩,⟨831062741771,841845130087⟩,⟨369559825621,372862147334⟩,⟨-1051520559548,-1016206169093⟩,⟨-1398392273342,-1381675829182⟩,⟨-205306133559,-201935464687⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨444977190492,453246138663⟩,⟨1746788537190,1807225056569⟩,⟨777854295930,799395888834⟩,⟨-7576093715236,-6990603672066⟩,⟨-5350160048802,-5071124945184⟩,⟨-1479512577685,-1389457247556⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨804757960671,814914935043⟩,⟨4138981879175,4213563444242⟩,⟨777854295930,799395888834⟩,⟨-19752158550470,-18955013219268⟩,⟨-5350160048802,-5071124945184⟩,⟨-1479512577685,-1389457247556⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨86758339376,91645542402⟩,⟨-227633266688,-219902325554⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13191321562719,13934404788171⟩,⟨31652410065381,36560567019820⟩,⟨-140861656329319,-126115071354942⟩,⟨151899119157028,191852480408119⟩,⟨-422650927634526,-252034179042749⟩,⟨2411435601390030,2847915863716406⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9655032990275,10327634820729⟩,⟨72824304775169,80496875608152⟩,⟨-95068882156831,-82175576364959⟩,⟨99157619901056,194997768994304⟩,⟨-898475638404640,-693474230358662⟩,⟨1541409266600950,1915652404630513⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨80821393920,86403386112⟩,⟨-714367103334,-565155062601⟩,⟨637725868420,843685937503⟩,⟨6130186253342,11005317382284⟩,⟨-8524654480119,-896573489765⟩,⟨-6991337512445,4461643689475⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1180333021696,1185915013888⟩,⟨-714367103334,-565155062601⟩,⟨637725868420,843685937503⟩,⟨6130186253342,11005317382284⟩,⟨-8524654480119,-896573489765⟩,⟨-6991337512445,4461643689475⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨77988924864,83176442560⟩,⟨-665451971757,-523978999800⟩,⟨591262442459,785915907990⟩,⟨5280804996873,10002040679502⟩,⟨-7659172819276,-355594957093⟩,⟨-7074378954746,3838188443455⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨83721627873,89712732037⟩,⟨-771786288775,-602581669092⟩,⟨679958375402,911499473532⟩,⟨6642452647544,12485277107214⟩,⟨-9927174155895,-1053152298567⟩,⟨-7473318046529,5683433619696⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-86403386112,-80821393920⟩,⟨565155062601,714367103334⟩,⟨-843685937503,-637725868420⟩,⟨-11005317382284,-6130186253342⟩,⟨896573489765,8524654480119⟩,⟨-4461643689475,6991337512445⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1013108241664,1018690233856⟩,⟨565155062601,714367103334⟩,⟨-843685937503,-637725868420⟩,⟨-11005317382284,-6130186253342⟩,⟨896573489765,8524654480119⟩,⟨-4461643689475,6991337512445⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-89987367936,-83945941184⟩,⟨609993639061,775292218852⟩,⟨-915640067199,-688322106521⟩,⟨-12490588039270,-6954962189465⟩,⟨1349577776108,9897323359746⟩,⟨-5604674338410,7156689776252⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-83372699817,-77349181872⟩,⟨503592280189,675154422501⟩,⟨-799645109456,-565181582856⟩,⟨-10477336954423,-4500273877818⟩,⟨-643966938236,8393749791185⟩,⟨-4966420826634,8400972411538⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨348928056,12363550165⟩,⟨-268194008586,72572753409⟩,⟨-119686734054,346317890676⟩,⟨-3834884306879,7985003229396⟩,⟨-10571141094131,7340597492618⟩,⟨-12439738873163,14084406031234⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨174464028,6181775083⟩,⟨-134097004293,36286376705⟩,⟨-59843367027,173158945338⟩,⟨-1917442153440,3992501614698⟩,⟨-5285570547066,3670298746309⟩,⟨-6219869436582,7042203015617⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6181775083,-174464028⟩,⟨-36286376705,134097004293⟩,⟨-173158945338,59843367027⟩,⟨-3992501614698,1917442153440⟩,⟨-3670298746309,5285570547066⟩,⟨-7042203015617,6219869436582⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755941608533,761948938852⟩,⟨-36286376705,134097004293⟩,⟨-173158945338,59843367027⟩,⟨-3992501614698,1917442153440⟩,⟨-3670298746309,5285570547066⟩,⟨-7042203015617,6219869436582⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨5940908263,6789873744⟩,⟨-112274822924,-83085287660⟩,⟨93754158340,132599455930⟩,⟨1482204320869,2657938321851⟩,⟨-2436100643200,-787397443278⟩,⟨-359033858832,1995989957390⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6789873744,-5940908263⟩,⟨83085287660,112274822924⟩,⟨-132599455930,-93754158340⟩,⟨-2657938321851,-1482204320869⟩,⟨787397443278,2436100643200⟩,⟨-1995989957390,359033858832⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092721754032,1093570719513⟩,⟨83085287660,112274822924⟩,⟨-132599455930,-93754158340⟩,⟨-2657938321851,-1482204320869⟩,⟨787397443278,2436100643200⟩,⟨-1995989957390,359033858832⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6810925440,-5957016320⟩,⟨83536654968,112972467928⟩,⟨-133423392638,-94263485120⟩,⟨-2686061702160,-1496603304512⟩,⟨798836817549,2464946873692⟩,⟨-2024583136728,353183386582⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3405462720,-2978508160⟩,⟨41768327484,56486233964⟩,⟨-66711696319,-47131742560⟩,⟨-1343030851080,-748301652256⟩,⟨399418408774,1232473436846⟩,⟨-1012291568364,176591693291⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨2978508160,3405462720⟩,⟨-56486233964,-41768327484⟩,⟨47131742560,66711696319⟩,⟨748301652256,1343030851080⟩,⟨-1232473436846,-399418408774⟩,⟨-176591693291,1012291568364⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765101891776,765528865600⟩,⟨-56486233964,-41768327484⟩,⟨47131742560,66711696319⟩,⟨748301652256,1343030851080⟩,⟨-1232473436846,-399418408774⟩,⟨-176591693291,1012291568364⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273180438508,273392679879⟩,⟨20771321915,28068705731⟩,⟨-33149863983,-23438539585⟩,⟨-664484580463,-370551080217⟩,⟨196849360819,609025160800⟩,⟨-498997489348,89758464708⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530203783552,1531057731200⟩,⟨-112972467928,-83536654968⟩,⟨94263485120,133423392638⟩,⟨1496603304512,2686061702160⟩,⟨-2464946873692,-798836817548⟩,⟨-353183386582,2024583136728⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1186745272935,1193283965028⟩,⟨-841413359893,-658389642627⟩,⟨742932576186,993730836786⟩,⟨7872024067014,14149154277948⟩,⟨-11442124602836,-1868819883366⟩,⟨-7304519208831,6910220497414⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1273978918094,1287056302280⟩,⟨-1682826719785,-1316779285254⟩,⟨1485865152372,1987461673572⟩,⟨15744048134034,28298308555884⟩,⟨-22884249205663,-3737639766732⟩,⟨-14604316040310,13820440994822⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨161934866048,173163810432⟩,⟨-1452369046032,-1124903497061⟩,⟨1269350850809,1715285228677⟩,⟨11531422524955,23272065010339⟩,⟨-18451660380782,-927248000157⟩,⟨-15280220635366,10462351545193⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨55566719787,59876554916⟩,⟨-497899711404,-378020369548⟩,⟨424844983684,589367368187⟩,⟨3726662017784,7824389270835⟩,⟨-6262636919417,14341638018⟩,⟨-5664056442830,3672485463225⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380188558299,380696270606⟩,⟨817189742,18330164385⟩,⟨-22740473778,555916739⟩,⟨-559215085650,149030355373⟩,⟨-335387849606,656396998891⟩,⟨-790712557409,624379757816⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175565176118,3179805896905⟩,⟨-153309097632,-6816560831⟩,⟨-4649554245,190195867391⟩,⟨-1246424876552,4691923915051⟩,⟨-5508286993655,2805551857971⟩,⟨-5222718723649,6636082769995⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨160485560906,173163991721⟩,⟨-1448283054737,-1092127691049⟩,⟨1226766959138,1714817795895⟩,⟨10700005165703,23022621911857⟩,⟨-18579922563806,193730952632⟩,⟨-16669945646644,11186172907651⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨322420426954,346327802153⟩,⟨-2900652100769,-2217031188110⟩,⟨2496117809947,3430103024572⟩,⟨22231427690658,46294686922196⟩,⟨-37031582944588,-733517047525⟩,⟨-31950166282010,21648524452844⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519728669597,528021869666⟩,⟨-50292085190,185855369864⟩,⟨-239994323516,82941533044⟩,⟨-5542366603726,2690239890734⟩,⟨-5129186921944,7340276507986⟩,⟨-9779180853457,8675136882362⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357326395256,365913095523⟩,⟨-52277756745,193193457355⟩,⟨-249469967640,86216295708⟩,⟨-5770395142103,2830458577137⟩,⟨-5375606250046,7645264450622⟩,⟨-10184883479980,9074349471839⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714652790512,731826191046⟩,⟨-104555513490,386386914710⟩,⟨-498939935280,172432591416⟩,⟨-11540790284206,5660917154274⟩,⟨-10751212500092,15290528901244⟩,⟨-20369766959960,18148698943678⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523413909808,1525116822937⟩,⟨-29887180268,28738167956⟩,⟨-38335970810,39669234298⟩,⟨-1161335017339,1203857381291⟩,⟨-1677549430414,1637263825652⟩,⟨-2349173343972,2383616995560⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨990177797347,1015105622565⟩,⟨-164920123873,555079648421⟩,⟨-717588551588,265582303319⟩,⟨-16802045889058,8673653111375⟩,⟨-16055929152533,22326526040157⟩,⟨-29854205404950,26795109182592⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67873363135,67978869458⟩,⟨10321525822,13958522106⟩,⟨-16485373912,-11646899150⟩,⟨-329662311520,-182698303145⟩,⟨96124351204,301981656548⟩,⟨-247151357560,46635651764⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49678082450,50383274346⟩,⟨263055835753,270855059594⟩,⟨35798993560,40899152705⟩,⟨-1387829736005,-1196838795615⟩,⟨-316299083691,-122920812119⟩,⟨-298623131253,-67686622306⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2129603325735,2131980887741⟩,⟨-314625813980,-232517969374⟩,⟨262375290878,371581185066⟩,⟨4178375842027,7503837539994⟩,⟨-6892240231374,-2237825495984⟩,⟨-967445066510,5670800356980⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2963795001509,2968759709754⟩,⟨-657169427899,-485397153824⟩,⟨547726353232,776134010490⟩,⟨8749143893445,15722006356495⟩,⟨-14453320729962,-4701515074470⟩,⟨-1987000050575,11912425658465⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨133910045815,136038429377⟩,⟨678968011511,709396761775⟩,⟨121245532780,145995663383⟩,⟨-3675711597370,-2737971761660⟩,⟨-1409731938671,-368373774077⟩,⟨-861687826505,421154421972⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8886649347180,9027894899572⟩,⟨-47825832396843,-44353280641961⟩,⟨-9842678320311,-7920310015795⟩,⟨621591361194918,754528300175597⟩,⟨103124410558954,199325150489537⟩,⟨-14275121535837,79554926374415⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8002973915050,8334852166156⟩,⟨-45508525468029,-35385194682324⟩,⟨-14979079541190,-4952076782678⟩,⟨373533628616444,782170566693763⟩,⟨-55483637290065,400032274291887⟩,⟨-263061762960410,306305145520717⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16005947830100,16669704332312⟩,⟨-91017050936058,-70770389364648⟩,⟨-29958159082380,-9904153565356⟩,⟨747067257232888,1564341133387526⟩,⟨-110967274580130,800064548583774⟩,⟨-526123525920820,612610291041434⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10825960642717,10867759718598⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790014,2123491006166466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9726449014941,9768248090822⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790024,2123491006166451⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2396916401408,2401631448192⟩,⟨-12142992897062,-11998203029636⟩,⟨0,0⟩,⟨102165241571294,109118793444233⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7697104040169,7797090767689⟩,⟨-49763149941697,-48305614562203⟩,⟨-22052159761497,-21469162027645⟩,⟨606314371237450,635203864082700⟩,⟨323356440933089,336778128940669⟩,⟨119765801725916,124738255494415⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6597592412393,6697579139913⟩,⟨-49763149941698,-48305614562202⟩,⟨-22052159761498,-21469162027644⟩,⟨606314371237454,635203864082697⟩,⟨323356440933090,336778128940669⟩,⟨119765801725915,124738255494415⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1970147472384,1986685641664⟩,⟨-8293201303706,-7930116806122⟩,⟨-3675068806896,-3524496358276⟩,⟨36983432003000,48663755859124⟩,⟨25364324223809,30705166911844⟩,⟨7377661944648,9490251322495⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99941875711,100371372442⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨132900063476,134914168260⟩,⟨703534803515,711018581857⟩,⟨312866192423,314901465664⟩,⟨-1781208837000,-1767320322048⟩,⟨-1578744078670,-1570862478130⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4367063873792,4388317089856⟩,⟨-20436194200768,-19928319835758⟩,⟨-3675068806896,-3524496358276⟩,⟨139148673574294,157782549303357⟩,⟨25364324223809,30705166911844⟩,⟨7377661944648,9490251322495⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨644840853908,692655604306⟩,⟨-5801304201538,-4434062376220⟩,⟨4992235619894,6860206049144⟩,⟨44462855381316,92589373844392⟩,⟨-74063165889176,-1467034095050⟩,⟨-63900332564020,43297048905688⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5011904727700,5080972694162⟩,⟨-26237498402306,-24362382211978⟩,⟨1317166812998,3335709690868⟩,⟨183611528955610,250371923147749⟩,⟨-48698841665367,29238132816794⟩,⟨-56522670619372,52787300228183⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨455565131570,463827930302⟩,⟨1598712990678,1838411757612⟩,⟨119725993422,304507702586⟩,⟨-35329289672158,-25995596409851⟩,⟨-3395965126136,5329817880596⟩,⟨-5159798114759,4818806493323⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨31977985971,34014127446⟩,⟨-688331312306,-647398810222⟩,⟨322945996948,325509439814⟩,⟨7976440964520,8651392784523⟩,⟨-6594864009033,-6530061933853⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨487543117541,497842057748⟩,⟨910381678372,1191012947390⟩,⟨442671990370,630017142400⟩,⟨-27352848707638,-17344203625328⟩,⟨-9990829135169,-1200244053257⟩,⟨-5159798114759,4818806493323⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503376910943,504367118897⟩,⟨2514798172912,2555168940688⟩,⟨0,0⟩,⟨2165995870996,4475808627517⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨223206323843,228369721601⟩,⟨1531896176170,1703281970705⟩,⟨202663485718,289000973652⟩,⟨-7422394222820,-378301851212⟩,⟨-3570507936926,914610691740⟩,⟨-2366898578868,2210479167443⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-692655604306,-644840853908⟩,⟨4434062376220,5801304201538⟩,⟨-6860206049144,-4992235619894⟩,⟨-92589373844392,-44462855381316⟩,⟨1467034095050,74063165889176⟩,⟨-43297048905688,63900332564020⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3674408269486,3743476235948⟩,⟨-16002131824548,-14127015634220⟩,⟨-10535274856040,-8516731978170⟩,⟨46559299729902,113319693922041⟩,⟨26831358318859,104768332801020⟩,⟨-35919386961040,73390583886515⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨444132722124,459338464475⟩,⟨387590075124,713225645073⟩,⟨-247164025415,42702534185⟩,⟨-21132841735587,-10080037545905⟩,⟨-13527799337987,-1863500575071⟩,⟨-11632977133497,2991780550918⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨310096638768,314124848334⟩,⟨1971389988864,1979120929998⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-314124848334,-310096638768⟩,⟨-1979120929998,-1971389988864⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨785386779442,789414989008⟩,⟨-1979120929998,-1971389988864⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1407286416325,1426378206795⟩,⟨-9530293528543,-9196935846014⟩,⟨-4223276776322,-4087527042672⟩,⟨54854357875019,64794580657983⟩,⟨34696785129640,39248969294489⟩,⟨10887067732923,12676587085233⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1426378206795,-1407286416325⟩,⟨9196935846014,9530293528543⟩,⟨4087527042672,4223276776322⟩,⟨-64794580657983,-54854357875019⟩,⟨-39248969294489,-34696785129640⟩,⟨-12676587085233,-10887067732923⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-326866579019,-307774788549⟩,⟨9196935846014,9530293528543⟩,⟨4087527042672,4223276776322⟩,⟨-64794580657983,-54854357875019⟩,⟨-39248969294489,-34696785129640⟩,⟨-12676587085233,-10887067732923⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13622350220,-12142677204⟩,⟨393625338390,431016190682⟩,⟨30902130513,53378439591⟩,⟨-4673419510213,-4003563007150⟩,⟨1899280705489,2350166372680⟩,⟨2728944149767,2939194271983⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430510371904,447195787271⟩,⟨781215413514,1144241835755⟩,⟨-216261894902,96080973776⟩,⟨-25806261245800,-14083600553055⟩,⟨-11628518632498,486665797609⟩,⟨-8904032983730,5930974822901⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100371372442,-99941875711⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨3943019315,4183033921⟩,⟨24177770494,26556632270⟩,⟨39820591103,40030926275⟩,⟨-273218640284,-261993005051⟩,⟨248728938086,249843280775⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8595714159,9136880011⟩,⟨6509747849,14979465893⟩,⟨86808202403,87438394478⟩,⟨-816985404482,-683673820137⟩,⟨100123741306,111191132797⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1483499402978,1502222877804⟩,⟨-7865360409413,-7534746122138⟩,⟨-1492213623620,-1416032930546⟩,⟨111044849260023,119234029787479⟩,⟨23615814707423,25612926349945⟩,⟨5232685535935,5726313673647⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11597637078,12483387932⟩,⟨-56577525591,-38438909145⟩,⟨104724440105,108393707955⟩,⟨-462407277478,-20828588576⟩,⟨-326107279729,-238505604521⟩,⟨-196427988872,-176010785750⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12483387932,-11597637078⟩,⟨38438909145,56577525591⟩,⟨-108393707955,-104724440105⟩,⟨20828588576,462407277478⟩,⟨238505604521,326107279729⟩,⟨176010785750,196427988872⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112854760374,-111539512789⟩,⟨-838593412699,-819595802793⟩,⟨-108393707955,-104724440105⟩,⟨2219851844128,2661430533030⟩,⟨238505604521,326107279729⟩,⟨176010785750,196427988872⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨77728474493,82796251815⟩,⟨-551276877661,-509882636841⟩,⟨631820054929,653293714051⟩,⟨3045135326904,3745041480741⟩,⟨-3941096077942,-3469721082699⟩,⟨-2640369784105,-2413071424704⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨104873966397,113121517346⟩,⟨-1345472900267,-1220610019215⟩,⟨740105842244,792467002294⟩,⟨18947026195839,21982487307702⟩,⟨-7731763026210,-6334317455571⟩,⟨-5010772649257,-4452002683059⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-113121517346,-104873966397⟩,⟨1220610019215,1345472900267⟩,⟨-792467002294,-740105842244⟩,⟨-21982487307702,-18947026195839⟩,⟨6334317455571,7731763026210⟩,⟨4452002683059,5010772649257⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨986390110430,994637661379⟩,⟨1220610019215,1345472900267⟩,⟨-792467002294,-740105842244⟩,⟨-21982487307702,-18947026195839⟩,⟨6334317455571,7731763026210⟩,⟨4452002683059,5010772649257⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119226850336,122045742324⟩,⟨778690192931,808294513911⟩,⟨183438798199,195407432293⟩,⟨-2746604080488,-2135507934133⟩,⟨-827656805448,-548750599959⟩,⟨-232226822741,-119537674657⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11315080803,11583503637⟩,⟨166287130064,172147808630⟩,⟨21247457018,22251235238⟩,⟨675540240806,828800182108⟩,⟨89183145334,116952743236⟩,⟨-20373818662,-14339023187⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164717305802,175617588649⟩,⟨1461818817983,1881635759853⟩,⟨-6307123965,235427446178⟩,⟨-10978495539236,7639751231630⟩,⟨-6403208594581,7336433719215⟩,⟨-7064219425330,5862409782748⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-175617588649,-164717305802⟩,⟨-1881635759853,-1461818817983⟩,⟨-235427446178,6307123965⟩,⟨-7639751231630,10978495539236⟩,⟨-7336433719215,6403208594581⟩,⟨-5862409782748,7064219425330⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47588735194,63652415799⟩,⟨-349739583683,241463152722⟩,⟨-32763960460,295308097617⟩,⟨-15062145454450,10600193688024⟩,⟨-10906941656141,7317819286321⟩,⟨-8229308361616,9274698592773⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28680076557595,30120156450529⟩,⟨-290190184334634,-242250407256306⟩,⟨-109848547173452,-69053883590487⟩,⟨2897852445957209,4937382928984865⟩,⟨467020102767142,2441325499348660⟩,⟨-779747348268370,1451062730342813⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨12928505239,13547072031⟩,⟨168876393382,179441310988⟩,⟨39782808268,43380432782⟩,⟨493213670222,725285892924⟩,⟨76088333934,168294627380⟩,⟨9654282102,43531989196⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337232013434,371110153556⟩,⟨829605197481,2067158403665⟩,⟨-315733081387,376405229430⟩,⟨-47779310875820,6286478859957⟩,⟨-21900497825071,15318528842509⟩,⟨-18023422832718,14074000166655⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371110153556,-337232013434⟩,⟨-2067158403665,-829605197481⟩,⟨-376405229430,315733081387⟩,⟨-6286478859957,47779310875820⟩,⟨-15318528842509,21900497825071⟩,⟨-14074000166655,18023422832718⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59400218348,109963773837⟩,⟨-1285942990151,314636638274⟩,⟨-592667124332,411814055163⟩,⟨-32092740105757,33695710322765⟩,⟨-26947047475007,22387163622680⟩,⟨-22978033150385,23954397655619⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨232841939187,235285540702⟩,⟨1579708131899,1588050903701⟩,⟨312866192423,314901465664⟩,⟨-3980232092552,-3966343577600⟩,⟨-1578744078670,-1570862478130⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1710991898953,-1623716909939⟩,⟨-5534647693910,-2589058738463⟩,⟨-638634992198,1550421929671⟩,⟨-22743081693438,103400762701097⟩,⟨-64523912948424,48155641358750⟩,⟨-58429899827559,62886549890115⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-189920025531,-176069673224⟩,⟨-1872163512941,-1430687691560⟩,⟨-374969399988,-98798667069⟩,⟨-7508321395005,12084356853797⟩,⟨-7804892156899,7341049060874⟩,⟨-6536186631505,7892869518819⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨42921913656,59215867478⟩,⟨-292455381042,157363212141⟩,⟨-62103207565,216102798595⟩,⟨-11488553487557,8118013276197⟩,⟨-9383636235569,5770186582744⟩,⟨-6885971787991,7543769208291⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2570942580,6365971654⟩,⟨-109423183299,42363882715⟩,⟨-37587181366,53374744612⟩,⟨-3929095774620,3828919031984⟩,⟨-3127197660651,2300917888416⟩,⟨-2471617268254,2535544070868⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1675553605,3189160417⟩,⟨-31501256830,16950069252⟩,⟨-6689325000,23277088410⟩,⟨-1321179986922,1029994288273⟩,⟨-1125700848380,683382012626⟩,⟨-766120992579,897509848590⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3002321772,5762430383⟩,⟨-80973626580,18541980722⟩,⟨-22746435116,36687901908⟩,⟨-2586550417703,2477430749295⟩,⟨-2227578696081,1479597031298⟩,⟨-1528651146810,1693936903944⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5762430383,-3002321772⟩,⟨-18541980722,80973626580⟩,⟨-36687901908,22746435116⟩,⟨-2477430749295,2586550417703⟩,⟨-1479597031298,2227578696081⟩,⟨-1693936903944,1528651146810⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3191487803,3363649882⟩,⟨-127965164021,123337509295⟩,⟨-74275083274,76121179728⟩,⟨-6406526523915,6415469449687⟩,⟨-4606794691949,4528496584497⟩,⟨-4165554172198,4064195217678⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47588735194,63652415799⟩,⟨-349739583683,241463152722⟩,⟨-32763960460,295308097617⟩,⟨-15062145454450,10600193688024⟩,⟨-10906941656141,7317819286321⟩,⟨-8229308361616,9274698592773⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3191487803,3363649882⟩,⟨-127965164021,123337509295⟩,⟨-74275083274,76121179728⟩,⟨-6406526523915,6415469449687⟩,⟨-4606794691949,4528496584497⟩,⟨-4165554172198,4064195217678⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (519/5120) u, BivariateJet2.affineZ (521/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000010

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000011Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2135897293184,-2135897254016⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2135897293120,-2135897254016⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-170100576832,-170100576768⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-170100576832,-170100576768⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨82958209600,82958209664⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-89731965952,-89731965888⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨82958334720,82958334784⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-89732112320,-89732112256⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6773777536,-6773777472⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6773756288,-6773756224⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨172690175488,172690175552⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨172690447040,172690447104⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1965796677184,1965796715776⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1965796677248,1965796715840⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2518909148928,-2518909091072⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2142948469440,-2142948430208⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2128885814272,-2128885775232⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-171278075648,-171278075584⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-168925218048,-168925217984⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨80376698752,80376698816⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-86719100672,-86719100608⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨85562691648,85562691712⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-92787236864,-92787236800⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7224545216,-7224545152⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6342401920,-6342401856⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨167095799360,167095799424⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨178349928512,178349928576⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1957607699648,1957607738240⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1974023212224,1974023250816⟩



end LaneCBRB2Cell000011Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000011
open Set LaneCBRB2Cell000011Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111454401331,111454401332⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨115749368627,115749368628⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111454401332,-111454401331⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438301412556,438301412557⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46141496360,46141496362⟩,⟨-115749368628,-115749368627⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157595897691,157595897694⟩,⟨983762259148,983762259149⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46141496359,46141496363⟩,⟨-115749368628,-115749368627⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2135897293184,-2135897254016⟩,⟨6863491110666,6863491110806⟩,⟨3057931752206,3057931752272⟩,⟨-42844030966171,-42844030964440⟩,⟨-26759603075594,-26759603074651⟩,⟨-8504636390673,-8504636390307⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-306143784930,-306143779309⟩,⟨-927281783855,-927281748769⟩,⟨-413137332647,-413137317011⟩,⟨6140947807942,6140947808572⟩,⟨3772398391112,3772398430615⟩,⟨1218991934760,1218991934895⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306143779309,306143784930⟩,⟨927281748769,927281783855⟩,⟨413137317011,413137332647⟩,⟨-6140947808572,-6140947807942⟩,⟨-3772398430615,-3772398391112⟩,⟨-1218991934895,-1218991934760⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157595897694,-157595897691⟩,⟨-983762259149,-983762259148⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941915730082,941915730085⟩,⟨-983762259149,-983762259148⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-170100576832,-170100576768⟩,⟨-1148359676304,-1148359676297⟩,⟨-511635472460,-511635472456⟩,⟨-1199377899104,-1199377899089⟩,⟨749109637760,749109637773⟩,⟨-238079207229,-238079207224⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145719613115,-145719613059⟩,⟨-831568754824,-831568754755⟩,⟨-370493741236,-370493741203⟩,⟨1027467905672,1027467905705⟩,⟨1387184898458,1387184898545⟩,⟨203954687355,203954687366⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145719613059,145719613115⟩,⟨831568754755,831568754824⟩,⟨370493741203,370493741236⟩,⟨-1027467905705,-1027467905672⟩,⟨-1387184898545,-1387184898458⟩,⟨-203954687366,-203954687355⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨451863392368,451863398045⟩,⟨1758850503524,1758850538679⟩,⟨783631058214,783631073883⟩,⟨-7168415714277,-7168415713614⟩,⟨-5159583329160,-5159583289570⟩,⟨-1422946622261,-1422946622115⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨812587482021,812587493624⟩,⟨4158122384344,4158122477443⟩,⟨783631058214,783631073883⟩,⟨-19238773886270,-19238773885101⟩,⟨-5159583329160,-5159583289570⟩,⟨-1422946622261,-1422946622115⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92282992718,92282992726⟩,⟨-231498737256,-231498737254⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13100201715435,13100201716571⟩,⟨32862828407616,32862828413600⟩,⟨-124439763992068,-124439763970201⟩,⟨164877688818485,164877688864229⟩,⟨-312166385013789,-312166384790403⟩,⟨2364124643777714,2364124644403545⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9681625602672,9681625741757⟩,⟨73829291959741,73829293424492⟩,⟨-82629841014199,-82629839497341⟩,⟨141190914417117,141190921835116⟩,⟨-739362375970475,-739362360942123⟩,⟨1552859859571881,1552859888563824⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨86168027136,86168162048⟩,⟨-651285678035,-651283600063⟩,⟨728917451489,728919776077⟩,⟨8555980558144,8556032384982⟩,⟨-4447632018572,-4447557710370⟩,⟨-1421096629277,-1420993085441⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1185679654912,1185679789824⟩,⟨-651285678035,-651283600063⟩,⟨728917451489,728919776077⟩,⟨8555980558144,8556032384982⟩,⟨-4447632018572,-4447557710370⟩,⟨-1421096629277,-1420993085441⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨82958209600,82958334784⟩,⟨-603954173488,-603952177809⟩,⟨675944062198,675946294763⟩,⟨7602434856294,7602486011887⟩,⟨-3753114823112,-3753042992681⟩,⟨-1733371135610,-1733272221753⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨89459591736,89459736911⟩,⟨-700425364634,-700422907512⟩,⟨783914228239,783916977091⟩,⟨9559270859094,9559336488106⟩,⟨-5183600317148,-5183511084137⟩,⟨-1080206936747,-1080086265883⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-86168162048,-86168027136⟩,⟨651283600063,651285678035⟩,⟨-728919776077,-728917451489⟩,⟨-8556032384982,-8555980558144⟩,⟨4447557710370,4447632018572⟩,⟨1420993085441,1421096629277⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1013343465728,1013343600640⟩,⟨651283600063,651285678035⟩,⟨-728919776077,-728917451489⟩,⟨-8556032384982,-8555980558144⟩,⟨4447557710370,4447632018572⟩,⟨1420993085441,1421096629277⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-89732112320,-89731965888⟩,⟨706664443133,706666791885⟩,⟨-790902390570,-790899763016⟩,⟨-9737763541532,-9737703052577⟩,⟨5334065818628,5334150466258⟩,⟨972911803677,973028137590⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-82699863735,-82699717767⟩,⟨598131515559,598134023274⟩,⟨-669432375002,-669429569532⟩,⟨-7439191439204,-7439123673201⟩,⟨3616095025622,3616186452920⟩,⟨1829336811998,1829459615935⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6759728001,6760019144⟩,⟨-102293849075,-102288884238⟩,⟨114481853237,114487407559⟩,⟨2120079419890,2120212814905⟩,⟨-1567505291526,-1567324631217⟩,⟨749129875251,749373350052⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3379864000,3380009572⟩,⟨-51146924538,-51144442119⟩,⟨57240926618,57243703780⟩,⟨1060039709945,1060106407453⟩,⟨-783752645763,-783662315608⟩,⟨374564937625,374686675026⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3380009572,-3379864000⟩,⟨51144442119,51146924538⟩,⟨-57243703780,-57240926618⟩,⟨-1060106407453,-1060039709945⟩,⟨783662315608,783752645763⟩,⟨-374686675026,-374564937625⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758743374044,758743538880⟩,⟨51144442119,51146924538⟩,⟨-57243703780,-57240926618⟩,⟨-1060106407453,-1060039709945⟩,⟨783662315608,783752645763⟩,⟨-374686675026,-374564937625⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6752933496,6752954643⟩,⟨-102081848754,-102081363226⟩,⟨114249594370,114250137604⟩,⟨2112614843316,2112629989737⟩,⟨-1560655231702,-1560636984194⟩,⟨743725407023,743748149418⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6752954643,-6752933496⟩,⟨102081363226,102081848754⟩,⟨-114250137604,-114249594370⟩,⟨-2112629989737,-2112614843316⟩,⟨1560636984194,1560655231702⟩,⟨-743748149418,-743725407023⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092758673133,1092758694280⟩,⟨102081363226,102081848754⟩,⟨-114250137604,-114249594370⟩,⟨-2112629989737,-2112614843316⟩,⟨1560636984194,1560655231702⟩,⟨-743748149418,-743725407023⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6773777536,-6773756224⟩,⟨102712196602,102712687119⟩,⟨-114956172721,-114955623904⟩,⟨-2135280549372,-2135265176565⟩,⟨1581019987942,1581038481160⟩,⟨-760363214133,-760340201952⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3386888768,-3386878112⟩,⟨51356098301,51356343560⟩,⟨-57478086361,-57477811952⟩,⟨-1067640274686,-1067632588282⟩,⟨790509993971,790519240580⟩,⟨-380181607067,-380170100976⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3386878112,3386888768⟩,⟨-51356343560,-51356098301⟩,⟨57477811952,57478086361⟩,⟨1067632588282,1067640274686⟩,⟨-790519240580,-790509993971⟩,⟨380170100976,380181607067⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765510261728,765510291648⟩,⟨-51356343560,-51356098301⟩,⟨57477811952,57478086361⟩,⟨1067632588282,1067640274686⟩,⟨-790519240580,-790509993971⟩,⟨380170100976,380181607067⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273189668283,273189673570⟩,⟨25520340806,25520462189⟩,⟨-28562534401,-28562398592⟩,⟨-528157497435,-528153710829⟩,⟨390159246048,390163807926⟩,⟨-185937037355,-185931351755⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531020523456,1531020583296⟩,⟨-102712687120,-102712196602⟩,⟨114955623904,114956172722⟩,⟨2135265176564,2135280549372⟩,⟨-1581038481160,-1581019987942⟩,⟨760340201952,760363214134⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1193006813139,1193006971971⟩,⟨-766757156798,-766754506239⟩,⟨858152639728,858155604964⟩,⟨11058531738138,11058602118831⟩,⟨-6339276991718,-6339180636705⟩,⟨-438482605238,-438351890407⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1286501998502,1286502316166⟩,⟨-1533514313596,-1533509012479⟩,⟨1716305279456,1716311209928⟩,⟨22117063476284,22117204237660⟩,⟨-12678553983435,-12678361273412⟩,⟨-876965058992,-876703932300⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨172690175488,172690447104⟩,⟨-1310621220273,-1310616366042⟩,⟨1466843539930,1466848970617⟩,⟨17340125460195,17340262002105⟩,⟨-9087277212815,-9087096887889⟩,⟨-2706410573100,-2706172725572⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59462235771,59462341789⟩,⟨-445426653185,-445424920771⟩,⟨498520150174,498522088259⟩,⟨5760579021971,5760624560288⟩,⟨-2939964605108,-2939901977899⟩,⟨-1085924016664,-1085838840073⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380404334407,380404356638⟩,⟨10015464862,10015757643⟩,⟨-11209648909,-11209321329⟩,⟨-209665963676,-209656786937⟩,⟨155783563917,155794590736⟩,⟨-75963928895,-75950223550⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178002035252,3178002220977⟩,⟨-83674388422,-83671932668⟩,⟨93645736111,93648483751⟩,⟨1755936046833,1756013174924⟩,⟨-1306482159790,-1306389597474⟩,⟨640027831083,640142727001⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨171868219968,171868536445⟩,⟨-1291975757512,-1291970534065⟩,⟨1445975100711,1445980944339⟩,⟨16812994424278,16813133614040⟩,⟨-8644135591475,-8643946425294⟩,⟨-3019197609430,-3018942136547⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨344558395456,344558983549⟩,⟨-2602596977785,-2602586900107⟩,⟨2912818640641,2912829914956⟩,⟨34153119884473,34153395616145⟩,⟨-17731412804290,-17731043313183⟩,⟨-5725608182530,-5725114862119⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523588376068,523588603567⟩,⟨70586805262,70590246700⟩,⟨-79004694972,-79000844916⟩,⟨-1458344073802,-1458251241737⟩,⟨1076242824742,1076368245404⟩,⟨-511162525256,-510993819169⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361314242643,361314478130⟩,⟨73065081033,73068659175⟩,⟨-81778537404,-81774534406⟩,⟨-1504621224214,-1504524325004⟩,⟨1108516605204,1108647208379⟩,⟨-522940147835,-522764802718⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722628485286,722628956260⟩,⟨146130162066,146137318350⟩,⟨-163557074808,-163549068812⟩,⟨-3009242448428,-3009048650008⟩,⟨2217033210408,2217294416758⟩,⟨-1045880295670,-1045529605436⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524267568813,1524267649800⟩,⟨-631323894,-630347848⟩,⟨705486300,706578352⟩,⟨22635186827,22665706056⟩,⟨-20401496966,-20364756240⟩,⟨16592052534,16637807111⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001789464155,1001790170300⟩,⟨202167260736,202177834108⟩,⟨-226277692064,-226265863168⟩,⟨-4157044353393,-4156755130991⟩,⟨3060281683044,3060668415445⟩,⟨-1439223289927,-1438706632931⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67877949601,67877952229⟩,⟨12681800288,12681860854⟩,⟨-14193555126,-14193487362⟩,⟨-261272155555,-261270257528⟩,⟨192555573312,192557856608⟩,⟨-90913577746,-90910736503⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50164792038,50164794697⟩,⟨266072578417,266072638999⟩,⟨37887515727,37887568799⟩,⟨-1284870546016,-1284868634232⟩,⟨-220856591384,-220854586298⟩,⟨-175265959861,-175263758688⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131877266259,2131877432909⟩,⟨-286045611842,-286044234610⟩,⟨320141079070,320142619994⟩,⟨5965711541050,5965754768653⟩,⟨-4424527860540,-4424475981386⟩,⟨2141516687450,2141581086595⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2968543274739,2968543622818⟩,⟨-597458510344,-597455610392⟩,⟨668673095502,668676340139⟩,⟨12500559530090,12500650690258⟩,⟨-9286294609341,-9286185458894⟩,⟨4523155463117,4523290628678⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135438636819,135438659880⟩,⟨691103723275,691104104827⟩,⟨132799483967,132799788903⟩,⟨-3187816238477,-3187805011392⟩,⟨-878743016312,-878731579722⟩,⟨-220745977855,-220733513499⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8926002521626,8926004041449⟩,⟨-45546811291319,-45546770634934⟩,⟨-8752092314958,-8752069237913⟩,⟨674913951371268,674915513515043⟩,⟨147230750713732,147231824187884⟩,⟨31710358466193,31711272463406⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8132679143442,8132686260780⟩,⟨-39857516058904,-39857363648498⟩,⟨-9811188323999,-9811065335535⟩,⟨564431302046865,564436403448845⟩,⟨166752667781530,166757470968908⟩,⟨20810311175244,20815558407452⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16265358286884,16265372521560⟩,⟨-79715032117808,-79714727296996⟩,⟨-19622376647998,-19622130671070⟩,⟨1128862604093730,1128872806897690⟩,⟨333505335563060,333514941937816⟩,⟨41620622350488,41631116814904⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10846819911700,10846819911799⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738054,2111240126795878⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9747308283924,9747308284023⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738069,2111240126795861⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2399271880896,2399271938752⟩,⟨-12070358171930,-12070358171514⟩,⟨0,0⟩,⟨105643681588589,105643681622780⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7671048785558,7671048785705⟩,⟨-47885055347468,-47885055345583⟩,⟨-21334511670860,-21334511669992⟩,⟨597826604822667,597826604858264⟩,⟨319872426066670,319872426084919⟩,⟨118669924001519,118669924008886⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6571537157782,6571537157929⟩,⟨-47885055347469,-47885055345583⟩,⟨-21334511670861,-21334511669992⟩,⟨597826604822676,597826604858264⟩,⟨319872426066674,319872426084921⟩,⟨118669924001519,118669924008887⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1965796677184,1965796715840⟩,⟨-8011850787322,-8011850786788⟩,⟨-3569567224827,-3569567224583⟩,⟨41644653056645,41644653075676⟩,⟨27508712708308,27508712717466⟩,⟨8266557181310,8266557185186⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100156582133,100156582135⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135007262571,135007262575⟩,⟨701751787532,701751787539⟩,⟨312655620682,312655620688⟩,⟨-1760396448892,-1760396448888⟩,⟨-1568639664788,-1568639664776⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4365068558080,4365068654592⟩,⟨-20082208959252,-20082208958302⟩,⟨-3569567224827,-3569567224583⟩,⟨147288334645234,147288334698456⟩,⟨27508712708308,27508712717466⟩,⟨8266557181310,8266557185186⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨689116790912,689117967098⟩,⟨-5205193955570,-5205173800214⟩,⟨5825637281282,5825659829912⟩,⟨68306239768946,68306791232290⟩,⟨-35462825608580,-35462086626366⟩,⟨-11451216365060,-11450229724238⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5054185348992,5054186621690⟩,⟨-25287402914822,-25287382758516⟩,⟨2256070056455,2256092605329⟩,⟨215594574414180,215595125930746⟩,⟨-7954112900272,-7953373908900⟩,⟨-3184659183750,-3183672539052⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨460395249339,460395365282⟩,⟨1726051149076,1726053999888⟩,⟨205509664653,205511718678⟩,⟨-30791012149268,-30790927224845⟩,⟨1074131999422,1074217292999⟩,⟨-290096594754,-290006719426⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34132401497,34132403437⟩,⟨-690842014923,-690842005141⟩,⟨324226151534,324226169925⟩,⟨8597207028080,8597207054250⟩,⟨-6562358286202,-6562358193788⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨494527650836,494527768719⟩,⟨1035209134153,1035211994747⟩,⟨529735816187,529737888603⟩,⟨-22193805121188,-22193720170595⟩,⟨-5488226286780,-5488140900789⟩,⟨-290096594754,-290006719426⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503871945521,503871957673⟩,⟨2534900173993,2534900296365⟩,⟨0,0⟩,⟨3319096918590,3319099843609⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226626625172,226626684661⟩,⟨1614526871521,1614528520701⟩,⟨242761431140,242762386719⟩,⟨-3904594635981,-3904540368531⟩,⟨-1293788873819,-1293744846551⟩,⟨-132942240374,-132901050102⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-689117967098,-689116790912⟩,⟨5205173800214,5205193955570⟩,⟨-5825659829912,-5825637281282⟩,⟨-68306791232290,-68306239768946⟩,⟨35462086626366,35462825608580⟩,⟨11450229724238,11451216365060⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3675950590982,3675951863680⟩,⟨-14877035159038,-14877015002732⟩,⟨-9395227054739,-9395204505865⟩,⟨78981543412944,78982094929510⟩,⟨62970799334674,62971538326046⟩,⟨19716786905548,19717773550246⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451364054820,451364211106⟩,⟨519409792147,519413079472⟩,⟨-108336528058,-108333397359⟩,⟨-15177668201048,-15177572713942⟩,⟨-7739103876505,-7738991197609⟩,⟨-4090512470539,-4090378093422⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨315191795382,315191795388⟩,⟨1967524518296,1967524518298⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-315191795388,-315191795382⟩,⟨-1967524518298,-1967524518296⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨784319832388,784319832394⟩,⟨-1967524518298,-1967524518296⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1402271045988,1402271073574⟩,⟨-9232832510938,-9232832441334⟩,⟨-4113558427163,-4113558396145⟩,⟨58380240284452,58380240300197⟩,⟨36329660013098,36329660097978⟩,⟨11588608840486,11588608843701⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1402271073574,-1402271045988⟩,⟨9232832441334,9232832510938⟩,⟨4113558396145,4113558427163⟩,⟨-58380240300197,-58380240284452⟩,⟨-36329660097978,-36329660013098⟩,⟨-11588608843701,-11588608840486⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-302759445798,-302759418212⟩,⟨9232832441334,9232832510938⟩,⟨4113558396145,4113558427163⟩,⟨-58380240300197,-58380240284452⟩,⟨-36329660097978,-36329660013098⟩,⟨-11588608843701,-11588608840486⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12705435318,-12705434158⟩,⟨419332460276,419332466137⟩,⟨51937465286,51937477601⟩,⟨-4393896882049,-4393896866503⟩,⟨2025630539385,2025630601693⟩,⟨2793277561531,2793277586447⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438658619502,438658776948⟩,⟨938742252423,938745545609⟩,⟨-56399062772,-56395919758⟩,⟨-19571565083097,-19571469580445⟩,⟨-5713473337120,-5713360595916⟩,⟨-1297234909008,-1297100506975⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100156582135,-100156582133⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4203115686,4203115687⟩,⟨26243201243,26243201248⟩,⟨39925700025,39925700027⟩,⟨-276848978172,-276848978161⟩,⟨249286067484,249286067488⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9171724084,9171724308⟩,⟨11124450817,11124452224⟩,⟨87122870713,87122872820⟩,⟨-776465682677,-776465667726⟩,⟨105671963339,105671976504⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1487748493670,1487748514915⟩,⟨-7613014816903,-7613014429019⟩,⟨-1434732865331,-1434732795665⟩,⟨113137537813720,113137545648671⟩,⟨24130018646959,24130020240651⟩,⟨5372454148901,5372454452790⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12410254103,12410254584⟩,⟨-48452500877,-48452493969⟩,⟨105917884293,105917889704⟩,⟨-260934598499,-260934447525⟩,⟨-273486113141,-273486027207⟩,⟨-182555077851,-182555057681⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12410254584,-12410254103⟩,⟨48452493969,48452500877⟩,⟨-105917889704,-105917884293⟩,⟨260934447525,260934598499⟩,⟨273486027207,273486113141⟩,⟨182555057681,182555077851⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112566836719,-112566836236⟩,⟨-828150331145,-828150324235⟩,⟨-105917889704,-105917884293⟩,⟨2459957703077,2459957854051⟩,⟨273486027207,273486113141⟩,⟨182555057681,182555077851⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨82495535228,82495536858⟩,⟨-543167073079,-543167068953⟩,⟨633832575918,633832591354⟩,⟨3434506604747,3434506605826⟩,⟨-3629387305775,-3629387266382⟩,⟨-2498983481597,-2498983481201⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨111624656956,111624660756⟩,⟨-1306157856337,-1306157799868⟩,⟨749991524650,749991565140⟩,⟨20657627129045,20657628392816⟩,⟨-6780350370663,-6780349721603⟩,⟨-4632435214180,-4632435013986⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-111624660756,-111624656956⟩,⟨1306157799868,1306157856337⟩,⟨-749991565140,-749991524650⟩,⟨-20657628392816,-20657627129045⟩,⟨6780349721603,6780350370663⟩,⟨4632435013986,4632435214180⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨987886967020,987886970820⟩,⟨1306157799868,1306157856337⟩,⟨-749991565140,-749991524650⟩,⟨-20657628392816,-20657627129045⟩,⟨6780349721603,6780350370663⟩,⟨4632435013986,4632435214180⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121301050191,121301050662⟩,⟨790889529554,790889538926⟩,⟨188823928213,188823934275⟩,⟨-2450911264744,-2450911031304⟩,⟨-684096972163,-684096845094⟩,⟨-171690432539,-171690383692⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11524473502,11524473602⟩,⟨169570306618,169570308764⟩,⟨21687521684,21687522888⟩,⟨743827123074,743827176969⟩,⟨103555909982,103555937304⟩,⟨-16973080034,-16973073656⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170484500429,170484651109⟩,⟨1672968218038,1672973647319⟩,⟨115158171734,115161050301⟩,⟨-1752090056582,-1751878254502⟩,⟨428966205250,429112742611⟩,⟨-588933467515,-588813405846⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170484651109,-170484500429⟩,⟨-1672973647319,-1672968218038⟩,⟨-115161050301,-115158171734⟩,⟨1751878254502,1752090056582⟩,⟨-429112742611,-428966205250⟩,⟨588813405846,588933467515⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56141974063,56142184232⟩,⟨-58446775798,-58439697337⟩,⟨127600380839,127604214985⟩,⟨-2152716381479,-2152450311949⟩,⟨-1722901616430,-1722711051801⟩,⟨455871165472,456032417413⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29080535817742,29080561839507⟩,⟨-261042519908382,-261041868390042⟩,⟨-87888060283306,-87887573599273⟩,⟨3796053133601250,3796076396498829⟩,⟨1404986878347683,1405007203405365⟩,⟨324108645610805,324129114152245⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13382254817,13382254922⟩,⟨174506077236,174506079984⟩,⟨41663116996,41663118496⟩,⟨597007122387,597007202962⟩,⟨120703018682,120703059248⟩,⟨26972422364,26972437456⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353941814435,353942133926⟩,⟨1438268266228,1438280423503⟩,⟨32237347813,32244305382⟩,⟨-20869243942770,-20868736072318⟩,⟨-3547798258473,-3547444310507⟩,⟨-2002438451501,-2002151135541⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353942133926,-353941814435⟩,⟨-1438280423503,-1438268266228⟩,⟨-32244305382,-32237347813⟩,⟨20868736072318,20869243942770⟩,⟨3547444310507,3547798258473⟩,⟨2002151135541,2002438451501⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84716485576,84716962513⟩,⟨-499538171080,-499522720619⟩,⟨-88643368154,-88633267571⟩,⟨1297170989221,1297774362325⟩,⟨-2166029026613,-2165562337443⟩,⟨704916226533,705337944526⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235163844704,235163844710⟩,⟨1578354612644,1578354612653⟩,⟨312655620682,312655620688⟩,⟨-3959419704444,-3959419704440⟩,⟨-1568639664788,-1568639664776⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1665231623346,-1665230158868⟩,⟨-4089942182590,-4089900116582⟩,⟨442021007181,442047649959⟩,⟨40899983100806,40901522412886⟩,⟨-7640741981746,-7639538383909⟩,⟨2218902794385,2220027470547⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-183712787028,-183712624748⟩,⟨-1649030814123,-1649025103928⟩,⟨-237212565682,-237209365507⟩,⟨2340272562746,2340506605991⟩,⟨-191303588179,-191143282255⟩,⟨656643833279,656777369997⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51451057676,51451219962⟩,⟨-70676201479,-70670491275⟩,⟨75443055000,75446255181⟩,⟨-1619147141698,-1618913098449⟩,⟨-1759943252967,-1759782947031⟩,⟨307201183658,307334720378⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4325693895,4325734442⟩,⟨-30010230464,-30008775321⟩,⟨5305285882,5306169341⟩,⟨-46531513135,-46470947825⟩,⟨-296611749184,-296567432883⟩,⟨50543036837,50580289686⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2407624684,2407639873⟩,⟨-6614530846,-6613975570⟩,⟨7060634696,7060956470⟩,⟨-142450112257,-142426262291⟩,⟨-174411038028,-174394320608⟩,⟨39103688988,39117155615⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4304548023,4304575264⟩,⟨-29369834399,-29368730716⟩,⟨4807170483,4807795339⟩,⟨-67105154306,-67053840738⟩,⟨-281568908811,-281534486480⟩,⟨42167404368,42193685969⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4304575264,-4304548023⟩,⟨29368730716,29369834399⟩,⟨-4807795339,-4807170483⟩,⟨67053840738,67105154306⟩,⟨281534486480,281568908811⟩,⟨-42193685969,-42167404368⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨21118631,21186419⟩,⟨-641499748,-638940922⟩,⟨497490543,498998858⟩,⟨20522327603,20634206481⟩,⟨-15077262704,-14998524072⟩,⟨8349350868,8412885318⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56141974063,56142184232⟩,⟨-58446775798,-58439697337⟩,⟨127600380839,127604214985⟩,⟨-2152716381479,-2152450311949⟩,⟨-1722901616430,-1722711051801⟩,⟨455871165472,456032417413⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨21118631,21186419⟩,⟨-641499748,-638940922⟩,⟨497490543,498998858⟩,⟨20522327603,20634206481⟩,⟨-15077262704,-14998524072⟩,⟨8349350868,8412885318⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111239652966,111669149696⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨113816633344,117682103911⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111669149696,-111239652966⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438086664192,438516160922⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨45348814848,46934932849⟩,⟨-117682103911,-113816633344⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156588467814,158604082545⟩,⟨981829523865,985694994432⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44919318118,47364429579⟩,⟨-117682103911,-113816633344⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2142948469440,-2128885775232⟩,⟨6806463999291,6921219186499⟩,⟨3037004934069,3079113198005⟩,⟨-43567774835134,-42135027045930⟩,⟨-27102840620544,-26422692661886⟩,⟨-8622862957172,-8388632495152⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309119401152,-303188209449⟩,⟨-951767843411,-902645559009⟩,⟨-422148865714,-404067162794⟩,⟨5871286392905,6408811612869⟩,⟨3643213594726,3900677923917⟩,⟨1176269009345,1261395198342⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨303188209449,309119401152⟩,⟨902645559009,951767843411⟩,⟨404067162794,422148865714⟩,⟨-6408811612869,-5871286392905⟩,⟨-3900677923917,-3643213594726⟩,⟨-1261395198342,-1176269009345⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158604082545,-156588467814⟩,⟨-985694994432,-981829523865⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940907545231,942923159962⟩,⟨-985694994432,-981829523865⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-171278075648,-168925217984⟩,⟨-1151848673457,-1144879056769⟩,⟨-512434638606,-510838424280⟩,⟨-1206676976421,-1192118411043⟩,⟨745277616962,752934456480⟩,⟨-238823539661,-237338004554⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146885271827,-144557827462⟩,⟨-836961612216,-826182623375⟩,⟨-372149409909,-368839686066⟩,⟨1009856033052,1045072836661⟩,⟨1378819061845,1395558330885⟩,⟨202263214102,205644593403⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144557827462,146885271827⟩,⟨826182623375,836961612216⟩,⟨368839686066,372149409909⟩,⟨-1045072836661,-1009856033052⟩,⟨-1395558330885,-1378819061845⟩,⟨-205644593403,-202263214102⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨447746036911,456004672979⟩,⟨1728828182384,1788729455627⟩,⟨772906848860,794298275623⟩,⟨-7453884449530,-6881142425957⟩,⟨-5296236254802,-5022032656571⟩,⟨-1467039791745,-1378532223447⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨807526807090,817673469359⟩,⟨4121021524369,4195067843300⟩,⟨772906848860,794298275623⟩,⟨-19629949284764,-18845551973159⟩,⟨-5296236254802,-5022032656571⟩,⟨-1467039791745,-1378532223447⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89838636236,94728859158⟩,⟨-235364207822,-227633266688⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12761959030861,13456635922644⟩,⟨30666963049642,35254436026415⟩,⟨-131367807236565,-118038876643908⟩,⟨147385306662392,184723026867230⟩,⟨-392074799649927,-237909876130118⟩,⟨2183548210061286,2564905653589558⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9372910452297,10007292240307⟩,⟨70355511173982,77559996183567⟩,⟨-88723177364395,-76971422876978⟩,⟨97882489194701,187652820268148⟩,⟨-836055590050195,-649968379802316⟩,⟨1395930529102382,1725490092404564⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨83387470336,88979949824⟩,⟨-729782803372,-581060044814⟩,⟨635700283886,834820168735⟩,⟨6285554986675,11121575701458⟩,⟨-8279023728059,-941660493474⟩,⟨-6598971875965,4082402904761⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1182899098112,1188491577600⟩,⟨-729782803372,-581060044814⟩,⟨635700283886,834820168735⟩,⟨6285554986675,11121575701458⟩,⟨-8279023728059,-941660493474⟩,⟨-6598971875965,4082402904761⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨80376698752,85562691712⟩,⟨-678337382572,-537557259765⟩,⟨588106695147,775970227801⟩,⟨5396471903379,10074754949334⟩,⟨-7407872374498,-392429910993⟩,⟨-6681416798877,3480050904649⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨86472504756,92487005947⟩,⟨-790023884275,-620802607897⟩,⟨679180056519,903731725833⟩,⟨6833397490521,12656011013074⟩,⟨-9681706557154,-1112624117803⟩,⟨-7055599964607,5257701344811⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-88979949824,-83387470336⟩,⟨581060044814,729782803372⟩,⟨-834820168735,-635700283886⟩,⟨-11121575701458,-6285554986675⟩,⟨941660493474,8279023728059⟩,⟨-4082402904761,6598971875965⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1010531677952,1016124157440⟩,⟨581060044814,729782803372⟩,⟨-834820168735,-635700283886⟩,⟨-11121575701458,-6285554986675⟩,⟨941660493474,8279023728059⟩,⟨-4082402904761,6598971875965⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-92787236864,-86719100608⟩,⟨628744303568,794042082565⟩,⟨-908328261898,-687868553065⟩,⟨-12674298430620,-7160915262963⟩,⟨1412287645907,9663987200065⟩,⟨-5192257036961,6749689185877⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-85750209910,-79701201910⟩,⟨516276037388,687993031200⟩,⟨-789302187446,-561751500211⟩,⟨-10552782216361,-4588796330992⟩,⟨-606442901508,8129759440241⟩,⟨-4559953326398,7961624422033⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨722294846,12785804037⟩,⟨-273747846887,67190423303⟩,⟨-110122130927,341980225622⟩,⟨-3719384725840,8067214682082⟩,⟨-10288149458662,7017135322438⟩,⟨-11615553291005,13219325766844⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨361147423,6392902019⟩,⟨-136873923444,33595211652⟩,⟨-55061065464,170990112811⟩,⟨-1859692362920,4033607341041⟩,⟨-5144074729331,3508567661219⟩,⟨-5807776645503,6609662883422⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6392902019,-361147423⟩,⟨-33595211652,136873923444⟩,⟨-170990112811,55061065464⟩,⟨-4033607341041,1859692362920⟩,⟨-3508567661219,5144074729331⟩,⟨-6609662883422,5807776645503⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755730481597,761762255457⟩,⟨-33595211652,136873923444⟩,⟨-170990112811,55061065464⟩,⟨-4033607341041,1859692362920⟩,⟨-3508567661219,5144074729331⟩,⟨-6609662883422,5807776645503⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6324144314,7200861975⟩,⟨-118117963624,-88135725036⟩,⟨96423607036,135118637858⟩,⟨1567545597345,2768829632219⟩,⟨-2448186058184,-814730304970⟩,⟨-332986629440,1928450219120⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7200861975,-6324144314⟩,⟨88135725036,118117963624⟩,⟨-135118637858,-96423607036⟩,⟨-2768829632219,-1567545597345⟩,⟨814730304970,2448186058184⟩,⟨-1928450219120,332986629440⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092310765801,1093187483462⟩,⟨88135725036,118117963624⟩,⟨-135118637858,-96423607036⟩,⟨-2768829632219,-1567545597345⟩,⟨814730304970,2448186058184⟩,⟨-1928450219120,332986629440⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7224545216,-6342401856⟩,⟨88645594617,118896635024⟩,⟨-136009383141,-96981422429⟩,⟨-2799939632680,-1583760774152⟩,⟨827262464561,2479032775365⟩,⟨-1957987515146,326627625718⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3612272608,-3171200928⟩,⟨44322797308,59448317512⟩,⟨-68004691571,-48490711214⟩,⟨-1399969816340,-791880387076⟩,⟨413631232280,1239516387683⟩,⟨-978993757573,163313812859⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3171200928,3612272608⟩,⟨-59448317512,-44322797308⟩,⟨48490711214,68004691571⟩,⟨791880387076,1399969816340⟩,⟨-1239516387683,-413631232280⟩,⟨-163313812859,978993757573⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765294584544,765735675488⟩,⟨-59448317512,-44322797308⟩,⟨48490711214,68004691571⟩,⟨791880387076,1399969816340⟩,⟨-1239516387683,-413631232280⟩,⟨-163313812859,978993757573⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273077691450,273296870866⟩,⟨22033931259,29529490906⟩,⟨-33779659465,-24105901759⟩,⟨-692207408055,-391886399336⟩,⟨203682576242,612046514546⟩,⟨-482112554780,83246657360⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530589169088,1531471350976⟩,⟨-118896635024,-88645594616⟩,⟨96981422428,136009383142⟩,⟨1583760774152,2799939632680⟩,⟨-2479032775366,-827262464560⟩,⟨-326627625718,1957987515146⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1189742228607,1196326494252⟩,⟨-863959558887,-680341735416⟩,⟨744317972305,988308934381⟩,⟨8137616782227,14414235243753⟩,⟨-11228660525402,-1953816478276⟩,⟨-6880939093359,6465910332617⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1279972829438,1293141360728⟩,⟨-1727919117774,-1360683470832⟩,⟨1488635944610,1976617868762⟩,⟨16275233564459,28828470487497⟩,⟨-22457321050798,-3907632956552⟩,⟨-13757141237771,12931820665231⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨167095799360,178349928576⟩,⟨-1484302727492,-1156940256755⟩,⟨1265733647017,1697937862735⟩,⟨11834488797527,23546624810439⟩,⟨-17959257162139,-1030362396545⟩,⟨-14439612037344,9651500382642⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57314949223,61646976309⟩,⟨-508325951649,-388304899992⟩,⟨423100018482,582834968991⟩,⟨3812145994059,7900331492419⟩,⟨-6081853408878,-13525342351⟩,⟨-5366443621198,3381981782555⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380141279359,380665667802⟩,⟨1119422657,19114336281⟩,⟨-22963938834,249844269⟩,⟨-577190796832,146875427175⟩,⟨-328767592843,654342651736⟩,⟨-761062051364,598380286295⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175820468904,3180201375797⟩,⟨-159907491870,-9339127975⟩,⟨-2090157348,192112653477⟩,⟨-1228681495209,4844767241367⟩,⟨-5493446059161,2750627495076⟩,⟨-5006206664600,6390134513565⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨165548034525,178306253358⟩,⟨-1479235565195,-1122063550806⟩,⟨1221961472045,1696549347294⟩,⟨10948678789339,23270222835669⟩,⟨-18072595087546,112527145523⟩,⟨-15804676263095,10343915649752⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨332643833885,356656181934⟩,⟨-2963538292687,-2279003807561⟩,⟨2487695119062,3394487210029⟩,⟨22783167586866,46816847646108⟩,⟨-36031852249685,-917835251022⟩,⟨-30244288300439,19995416032394⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519438400092,527763162463⟩,⟨-46550784102,189657637086⟩,⟨-236930307430,76294675484⟩,⟨-5597481748133,2610937226115⟩,⟨-4904174607228,7141531372536⟩,⟨-9175722159273,8100655860015⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357027085794,365644206782⟩,⟨-48376883058,197097546414⟩,⟨-246224633940,79287570875⟩,⟨-5825752727742,2748773952303⟩,⟨-5140797871792,7435926541805⟩,⟨-9553465737554,8473698406222⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714054171588,731288413564⟩,⟨-96753766116,394195092828⟩,⟨-492449267880,158575141750⟩,⟨-11651505455484,5497547904606⟩,⟨-10281595743584,14871853083610⟩,⟨-19106931475108,16947396812444⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523388307113,1525147206662⟩,⟨-30760909988,29472369008⟩,⟨-38137215430,39585776106⟩,⟨-1185068858067,1232394035335⟩,⟨-1664302470396,1620923593624⟩,⟨-2255077844838,2290974144586⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989331761631,1014379887431⟩,⟨-154667607778,566395416794⟩,⟨-708448104979,246290304763⟩,⟨-16972207707618,8466523500521⟩,⟨-15395543679316,21734995732856⟩,⟨-28038797099437,25065855010360⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67822316457,67931232139⟩,⟨10944813914,14679821950⟩,⟨-16792683220,-11974014346⟩,⟨-343229884467,-193073796994⟩,⟨99359879752,303296927940⟩,⟨-238612771005,43459506488⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49811513834,50518398222⟩,⟨262239570097,270101216707⟩,⟨35187805539,40279995098⟩,⟨-1386005337483,-1192252565063⟩,⟨-310620827609,-118500838985⟩,⟨-292349751909,-69548294640⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130676152346,2133132965228⟩,⟨-331213942022,-246800458638⟩,⟨270008449244,378885440562⟩,⟨4423682419270,7825590258531⟩,⟨-6935331351254,-2318840314010⟩,⟨-892788111612,5488073543016⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966034882424,2971166417474⟩,⟨-692004500593,-515342583981⟩,⟨563803052466,791604449008⟩,⟨9266911781869,16403711254403⟩,⟨-14551427936451,-4874610016035⟩,⟨-1829583165318,11536521076184⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134371191577,136513852578⟩,⟨675620643529,706537021095⟩,⟨120464521579,145218252802⟩,⟨-3665514781372,-2708347814876⟩,⟨-1398842387561,-362533479416⟩,⟨-837980580047,400446464992⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8855700698387,8996912250510⟩,⟨-47306654841164,-43827744157503⟩,⟨-9723184428885,-7814575061298⟩,⟨609507192776314,742913117374916⟩,⟨100867891356479,195911351444553⟩,⟨-13020458711559,77123714790050⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7968288602944,8300309524111⟩,⟨-44909438754705,-34801241301163⟩,⟨-14767327375904,-5016186197905⟩,⟨360813661556226,767979424970122⟩,⟨-50821549320340,390441123862926⟩,⟨-245799802240195,288787110826177⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15936577205888,16600619048222⟩,⟨-89818877509410,-69602482602326⟩,⟨-29534654751808,-10032372395810⟩,⟨721627323112452,1535958849940244⟩,⟨-101643098640680,780882247725852⟩,⟨-491599604480390,577574221652354⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10825960642717,10867759718598⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790014,2123491006166466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9726449014941,9768248090822⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790024,2123491006166451⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2396916401408,2401631448192⟩,⟨-12142992897062,-11998203029636⟩,⟨0,0⟩,⟨102165241571294,109118793444233⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7622286893350,7720401358360⟩,⟨-48598476504550,-47185332124955⟩,⟨-21620498697687,-21053822732932⟩,⟨584196212736320,611836563653716⟩,⟨313505943670766,326404022371530⟩,⟨116307207501327,121093695065603⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6522775265574,6620889730584⟩,⟨-48598476504550,-47185332124954⟩,⟨-21620498697687,-21053822732932⟩,⟨584196212736324,611836563653712⟩,⟨313505943670767,326404022371529⟩,⟨116307207501327,121093695065603⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1957607699648,1974023250816⟩,⟨-8192002304786,-7835928922373⟩,⟨-3644459413157,-3496346238331⟩,⟨35980551238058,47289636294567⟩,⟨24909661080308,30102758748664⟩,⟨7234809472508,9294098289530⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99941875711,100371372442⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134000648233,136016262965⟩,⟨698014952716,705487271364⟩,⟨311637081193,313673558264⟩,⟨-1767320322048,-1753486165276⟩,⟨-1572580465052,-1564698864514⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4354524101056,4375654699008⟩,⟨-20334995201848,-19834131952009⟩,⟨-3644459413157,-3496346238331⟩,⟨138145792809352,156408429738800⟩,⟨24909661080308,30102758748664⟩,⟨7234809472508,9294098289530⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨665287667770,713312363868⟩,⟨-5927076585374,-4558007615122⟩,⟨4975390238124,6788974420058⟩,⟨45566335173732,93633695292216⟩,⟨-72063704499370,-1835670502044⟩,⟨-60488576600878,39990832064788⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5019811768826,5088967062876⟩,⟨-26262071787222,-24392139567131⟩,⟨1330930824967,3292628181727⟩,⟨183712127983084,250042125031016⟩,⟨-47154043419062,28267088246620⟩,⟨-53253767128370,49284930354318⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨456283854775,464557714089⟩,⟨1602770677799,1842083673181⟩,⟨120977095401,300574910890⟩,⟨-35375336527501,-26088942633891⟩,⟨-3243976574051,5206809675149⟩,⟨-4861388965202,4499084844039⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33113342992,35158496570⟩,⟨-711516381085,-670356059224⟩,⟨322945996948,325509439814⟩,⟨8258639834731,8943414583478⟩,⟨-6594864009033,-6530061933853⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨489397197767,499716210659⟩,⟨891254296714,1171727613957⟩,⟨443923092349,626084350704⟩,⟨-27116696692770,-17145528050413⟩,⟨-9838840583084,-1323252258704⟩,⟨-4861388965202,4499084844039⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503376910943,504367118897⟩,⟨2514798172912,2555168940688⟩,⟨0,0⟩,⟨2165995870996,4475808627517⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨224055156319,229229431567⟩,⟨1527379948599,1698790785139⟩,⟨203236263517,287196926503⟩,⟨-7397910413915,-369350170572⟩,⟨-3497926351543,849155778984⟩,⟨-2230012565830,2063816701104⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-713312363868,-665287667770⟩,⟨4558007615122,5927076585374⟩,⟨-6788974420058,-4975390238124⟩,⟨-93633695292216,-45566335173732⟩,⟨1835670502044,72063704499370⟩,⟨-39990832064788,60488576600878⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3641211737188,3710367031238⟩,⟨-15776987586726,-13907055366635⟩,⟨-10433433833215,-8471736476455⟩,⟨44512097517136,110842094565068⟩,⟨26745331582352,102166463248034⟩,⟨-32756022592280,69782674890408⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443764959651,458994925628⟩,⟨359881001868,685815647091⟩,⟨-258642177964,26035058591⟩,⟨-20785305406085,-9752650032502⟩,⟨-13242640801060,-1863056438892⟩,⟨-11185482186188,2674110923025⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨313176935628,317208165090⟩,⟨1963659047730,1971389988864⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-317208165090,-313176935628⟩,⟨-1971389988864,-1963659047730⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨782303462686,786334692148⟩,⟨-1971389988864,-1963659047730⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1392839551058,1411756752735⟩,⟨-9398013648801,-9071435125090⟩,⟨-4180989950082,-4047621971827⟩,⟨53589151570537,63196006760602⟩,⟨34126972263059,38545356958656⟩,⟨10719874939112,12460886245450⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1411756752735,-1392839551058⟩,⟨9071435125090,9398013648801⟩,⟨4047621971827,4180989950082⟩,⟨-63196006760602,-53589151570537⟩,⟨-38545356958656,-34126972263059⟩,⟨-12460886245450,-10719874939112⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-312245124959,-293327923282⟩,⟨9071435125090,9398013648801⟩,⟨4047621971827,4180989950082⟩,⟨-63196006760602,-53589151570537⟩,⟨-38545356958656,-34126972263059⟩,⟨-12460886245450,-10719874939112⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13450801119,-11983584316⟩,⟨400967361987,438264777488⟩,⟨40828932024,63234576953⟩,⟨-4734100775238,-4067395419172⟩,⟨1799786038429,2247225876822⟩,⟨2688662467363,2897044260820⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430314158532,447011341312⟩,⟨760848363855,1124080424579⟩,⟨-217813245940,89269635544⟩,⟨-25519406181323,-13820045451674⟩,⟨-11442854762631,384169437930⟩,⟨-8496819718825,5571155183845⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100371372442,-99941875711⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4083013580,4323767646⟩,⟨25052208168,27434987555⟩,⟨39820591103,40030926275⟩,⟨-282468590554,-271233895628⟩,⟨248728938086,249843280775⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8900899244,9444280617⟩,⟨6861745382,15370372228⟩,⟨86808202403,87438394478⟩,⟨-843582801722,-708936226385⟩,⟨100123741306,111191132797⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1478494612968,1497072058786⟩,⟨-7777226462056,-7451517448007⟩,⟨-1472547715243,-1397548844602⟩,⟨109186341493456,117196646650994⟩,⟨23167812921285,25118327059361⟩,⟨5134693457373,5616591874735⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11968888050,12859135156⟩,⟨-57575794515,-39394445796⟩,⟨104081032776,107740684857⟩,⟨-482146195758,-39636874297⟩,⟨-316881615777,-229880962880⟩,⟨-192641006755,-172433589035⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12859135156,-11968888050⟩,⟨39394445796,57575794515⟩,⟨-107740684857,-104081032776⟩,⟨39636874297,482146195758⟩,⟨229880962880,316881615777⟩,⟨172433589035,192641006755⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113230507598,-111910763761⟩,⟨-837637876048,-818597533869⟩,⟨-107740684857,-104081032776⟩,⟨2238660129849,2681169451310⟩,⟨229880962880,316881615777⟩,⟨172433589035,192641006755⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨79975873641,85036376960⟩,⟨-564174775356,-522771098799⟩,⟨622989396749,644456675754⟩,⟨3092227348368,3790729152601⟩,⟨-3861641353617,-3392907040133⟩,⟨-2611455777487,-2385782551652⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨107542199062,115783754088⟩,⟨-1369660325134,-1244967162387⟩,⟨723836223573,775824348755⟩,⟨19185782053014,22206589077627⟩,⟨-7466748375036,-6086216068127⟩,⟨-4908426756638,-4357451188926⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-115783754088,-107542199062⟩,⟨1244967162387,1369660325134⟩,⟨-775824348755,-723836223573⟩,⟨-22206589077627,-19185782053014⟩,⟨6086216068127,7466748375036⟩,⟨4357451188926,4908426756638⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨983727873688,991969428714⟩,⟨1244967162387,1369660325134⟩,⟨-775824348755,-723836223573⟩,⟨-22206589077627,-19185782053014⟩,⟨6086216068127,7466748375036⟩,⟨4357451188926,4908426756638⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119889748711,122712640104⟩,⟨776238423010,805919521096⟩,⟨182846046853,194777437374⟩,⟨-2760838105845,-2149413010483⟩,⟨-821956852911,-545024664507⟩,⟨-227179103620,-115453310768⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11390528966,11660766042⟩,⟨166637392300,172524163442⟩,⟨21187202712,22190820230⟩,⟨666680979571,820558937373⟩,⟨89712212774,117363969000⟩,⟨-19972462899,-13986426843⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165096975508,176056287159⟩,⟨1462715546025,1883744352861⟩,⟨-6134730390,231109265437⟩,⟨-11048108333873,7581084654086⟩,⟨-6224697204313,7191874332117⟩,⟨-6707323018903,5536045395362⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176056287159,-165096975508⟩,⟨-1883744352861,-1462715546025⟩,⟨-231109265437,6134730390⟩,⟨-7581084654086,11048108333873⟩,⟨-7191874332117,6224697204313⟩,⟨-5536045395362,6707323018903⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47998869160,64132456059⟩,⟨-356364404262,236075239114⟩,⟨-27873001920,293331656893⟩,⟨-14978995068001,10678758163301⟩,⟨-10689800683660,7073852983297⟩,⟨-7766057961192,8771139720007⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28374021207383,29804148634075⟩,⟨-284941836134458,-237498390659472⟩,⟨-108050132930129,-68538830613262⟩,⟨2798397190146797,4809997901497337⟩,⟨471387677151714,2374229877080900⟩,⟨-713933017898376,1373071817182845⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13072669249,13695527779⟩,⟨169280664474,179891707640⟩,⟨39874733574,43476854578⟩,⟨479770017570,712704948057⟩,⟨74701586688,166677762500⟩,⟨10104357475,43831426766⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337353589664,371240772027⟩,⟨819222197247,2052530621113⟩,⟨-316865281095,363620686281⟩,⟨-47586419362500,6102030344064⟩,⟨-21412977821427,14926205224179⟩,⟨-17177033495286,13319883103226⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371240772027,-337353589664⟩,⟨-2052530621113,-819222197247⟩,⟨-363620686281,316865281095⟩,⟨-6102030344064,47586419362500⟩,⟨-14926205224179,21412977821427⟩,⟨-13319883103226,17177033495286⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59073386505,109657751648⟩,⟨-1291682257258,304858227332⟩,⟨-581433932221,406134916639⟩,⟨-31621436525387,33766373910826⟩,⟨-26369059986810,21797147259357⟩,⟨-21816702822051,22748188679131⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨233942523944,236387635407⟩,⟨1574188281100,1582519593208⟩,⟨311637081193,313673558264⟩,⟨-3966343577600,-3952509420828⟩,⟨-1572580465052,-1564698864514⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1709574027038,-1622060632914⟩,⟨-5562506242265,-2615166255763⟩,⟨-605570319892,1532979272067⟩,⟨-22089788228592,103884845299585⟩,⟨-63027440770454,46553417170695⟩,⟨-55081419967223,59322883841058⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-190799566837,-176868017364⟩,⟨-1873894605281,-1430305394896⟩,⟨-370434991701,-98654200686⟩,⟨-7448836857667,12194373713605⟩,⟨-7659484487814,7162428958535⟩,⟨-6191673550928,7517179927233⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43142957107,59519618043⟩,⟨-299706324181,152214198312⟩,⟨-58797910508,215019357578⟩,⟨-11415180435267,8241864292777⟩,⟨-9232064952866,5597730094021⟩,⟨-6541458707414,7168079616705⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2578831981,6396131484⟩,⟨-110882751819,41326335859⟩,⟨-36693815521,52943978225⟩,⟨-3892993577279,3871853785220⟩,⟨-3080418003972,2246665033704⟩,⟨-2357294895506,2418332886022⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1692855901,3221962227⟩,⟨-32447871382,16479554588⟩,⟨-6365788386,23279189982⟩,⟨-1318852332158,1055698695242⟩,⟨-1116735149538,665575055318⟩,⟨-731211571573,860154041260⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3014017917,5784593986⟩,⟨-82261226033,17522257081⟩,⟨-22108474561,36411485711⟩,⟨-2557986934265,2517449744508⟩,⟨-2194660673259,1438142216470⟩,⟨-1455974852220,1613724657697⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5784593986,-3014017917⟩,⟨-17522257081,82261226033⟩,⟨-36411485711,22108474561⟩,⟨-2517449744508,2557986934265⟩,⟨-1438142216470,2194660673259⟩,⟨-1613724657697,1455974852220⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3205762005,3382113567⟩,⟨-128405008900,123587561892⟩,⟨-73105301232,75052452786⟩,⟨-6410443321787,6429840719485⟩,⟨-4518560220442,4441325706963⟩,⟨-3971019553203,3874307738242⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47998869160,64132456059⟩,⟨-356364404262,236075239114⟩,⟨-27873001920,293331656893⟩,⟨-14978995068001,10678758163301⟩,⟨-10689800683660,7073852983297⟩,⟨-7766057961192,8771139720007⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3205762005,3382113567⟩,⟨-128405008900,123587561892⟩,⟨-73105301232,75052452786⟩,⟨-6410443321787,6429840719485⟩,⟨-4518560220442,4441325706963⟩,⟨-3971019553203,3874307738242⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (519/5120) u, BivariateJet2.affineZ (539/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000011

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000012Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2127846812736,-2127846773696⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2127846812672,-2127846773696⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-171453311680,-171453311616⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-171453311680,-171453311616⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨85565532480,85565532544⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-92790577984,-92790577920⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨85565655872,85565655936⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-92790723136,-92790723072⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7225067264,-7225067200⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7225045504,-7225045440⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨178356110400,178356110464⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨178356378944,178356379008⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1956393462016,1956393500608⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1956393462080,1956393500672⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2518909148864,-2518909091008⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2134856910272,-2134856871104⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2120875930240,-2120875891328⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-172634027520,-172634027456⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-170274743872,-170274743808⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨82977075776,82977075840⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-89754040960,-89754040896⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨88176809216,88176809280⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-95869688640,-95869688576⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7692879424,-7692879360⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6776965184,-6776965120⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨172731116672,172731116736⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨184046497792,184046497856⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1948241863872,1948241902464⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1964582127296,1964582165888⟩



end LaneCBRB2Cell000012Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000012
open Set LaneCBRB2Cell000012Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111024904601,111024904602⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨119614839193,119614839194⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111024904602,-111024904601⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438730909286,438730909287⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨47729124310,47729124312⟩,⟨-119614839194,-119614839193⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158754028911,158754028914⟩,⟨979896788582,979896788583⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47729124309,47729124313⟩,⟨-119614839194,-119614839193⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2127846812736,-2127846773696⟩,⟨6786649261354,6786649261491⟩,⟨3038598387232,3038598387297⟩,⟨-41890060127561,-41890060125877⟩,⟨-26370597646172,-26370597645249⟩,⟨-8397437485913,-8397437485553⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-307231179644,-307231174001⟩,⟨-916463564273,-916463529439⟩,⟨-410329840416,-410329824816⟩,⟨6048336050449,6048336051065⟩,⟨3736367263155,3736367302525⟩,⟨1212471973602,1212471973736⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307231174001,307231179644⟩,⟨916463529439,916463564273⟩,⟨410329824816,410329840416⟩,⟨-6048336051065,-6048336050449⟩,⟨-3736367302525,-3736367263155⟩,⟨-1212471973736,-1212471973602⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158754028914,-158754028911⟩,⟨-979896788583,-979896788582⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940757598862,940757598865⟩,⟨-979896788583,-979896788582⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-171453311680,-171453311616⟩,⟨-1145255605027,-1145255605020⟩,⟨-512767302449,-512767302444⟩,⟨-1192902710359,-1192902710345⟩,⟨750955174324,750955174337⟩,⟨-239133720661,-239133720657⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146697862705,-146697862649⟩,⟨-827095722006,-827095721937⟩,⟨-370317019519,-370317019485⟩,⟨1020664321415,1020664321446⟩,⟨1385042144416,1385042144505⟩,⟨204606171655,204606171666⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146697862649,146697862705⟩,⟨827095721937,827095722006⟩,⟨370317019485,370317019519⟩,⟨-1020664321446,-1020664321415⟩,⟨-1385042144505,-1385042144416⟩,⟨-204606171666,-204606171655⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨453929036650,453929042349⟩,⟨1743559251376,1743559286279⟩,⟨780646844301,780646859935⟩,⟨-7069000372511,-7069000371864⟩,⟨-5121409447030,-5121409407571⟩,⟨-1417078145402,-1417078145257⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨813714988794,813715000397⟩,⟨4147554196900,4147554289747⟩,⟨780646844301,780646859935⟩,⟨-19180787536713,-19180787535559⟩,⟨-5121409447030,-5121409407571⟩,⟨-1417078145402,-1417078145257⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95458248618,95458248626⟩,⟨-239229678388,-239229678386⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12664445839050,12664445840113⟩,⟨31738601416027,31738601421621⟩,⟨-116412859433111,-116412859413302⟩,⟨159081389371081,159081389413800⟩,⟨-291744415297803,-291744415095689⟩,⟨2140157415335903,2140157415884572⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9372569733390,9372569867824⟩,⟨71261321124205,71261322536725⟩,⟨-77161921836483,-77161920412500⟩,⟨136249586879388,136249594024070⟩,⟨-691496675301457,-691496661253346⟩,⟨1402238005056254,1402238031388833⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨88983020544,88983153920⟩,⟨-670178712834,-670176664005⟩,⟨725668814365,725671031849⟩,⟨8765742468287,8765793422658⟩,⟨-4375902649727,-4375831893635⟩,⟨-1407542967340,-1407447597581⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1188494648320,1188494781696⟩,⟨-670178712834,-670176664005⟩,⟨725668814365,725671031849⟩,⟨8765742468287,8765793422658⟩,⟨-4375902649727,-4375831893635⟩,⟨-1407542967340,-1407447597581⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨85565532480,85565655936⟩,⟨-620002192262,-620000227250⟩,⟨671337654650,671339781451⟩,⟨7759835040257,7759885305824⟩,⟨-3669718725478,-3669650413540⟩,⟨-1712066347114,-1711975374437⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨92490315576,92490459404⟩,⟨-722333107936,-722330673993⟩,⟨782141294868,782143929277⟩,⟨9825805324938,9825870255437⟩,⟨-5125642744384,-5125557366542⟩,⟨-1074005610413,-1073893972574⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-88983153920,-88983020544⟩,⟨670176664005,670178712834⟩,⟨-725671031849,-725668814365⟩,⟨-8765793422658,-8765742468287⟩,⟨4375831893635,4375902649727⟩,⟨1407447597581,1407542967340⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1010528473856,1010528607232⟩,⟨670176664005,670178712834⟩,⟨-725671031849,-725668814365⟩,⟨-8765793422658,-8765742468287⟩,⟨4375831893635,4375902649727⟩,⟨1407447597581,1407542967340⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-92790723136,-92790577920⟩,⟨729189682967,729192008452⟩,⟨-789570762330,-789568245369⟩,⟨-10021272055688,-10021212271131⟩,⟨5284786816233,5284867770428⟩,⟨964382687048,964490271722⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-85281208353,-85281063633⟩,⟨613618403881,613620891040⟩,⟨-664430093917,-664427401892⟩,⟨-7581576906235,-7581509734078⟩,⟨3525271813887,3525359417650⟩,⟨1809766527117,1809880263533⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7209107223,7209395771⟩,⟨-108714704055,-108709782953⟩,⟨117711200951,117716527385⟩,⟨2244228418703,2244360521359⟩,⟨-1600370930497,-1600197948892⟩,⟨735760916704,735986290959⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3604553611,3604697886⟩,⟨-54357352028,-54354891476⟩,⟨58855600475,58858263693⟩,⟨1122114209351,1122180260680⟩,⟨-800185465249,-800098974446⟩,⟨367880458352,367993145480⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3604697886,-3604553611⟩,⟨54354891476,54357352028⟩,⟨-58858263693,-58855600475⟩,⟨-1122180260680,-1122114209351⟩,⟨800098974446,800185465249⟩,⟨-367993145480,-367880458352⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758518685730,758518849269⟩,⟨54354891476,54357352028⟩,⟨-58858263693,-58855600475⟩,⟨-1122180260680,-1122114209351⟩,⟨800098974446,800185465249⟩,⟨-367993145480,-367880458352⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7201358989,7201380578⟩,⟨-108474733786,-108474239570⟩,⟨117456153050,117456688026⟩,⟨2235790822151,2235806191486⟩,⟨-1592908842370,-1592890920568⟩,⟨730047059967,730068692020⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7201380578,-7201358989⟩,⟨108474239570,108474733786⟩,⟨-117456688026,-117456153050⟩,⟨-2235806191486,-2235790822151⟩,⟨1592890920568,1592908842370⟩,⟨-730068692020,-730047059967⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092310247198,1092310268787⟩,⟨108474239570,108474733786⟩,⟨-117456688026,-117456153050⟩,⟨-2235806191486,-2235790822151⟩,⟨1592890920568,1592908842370⟩,⟨-730068692020,-730047059967⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7225067264,-7225045440⟩,⟨109189386138,109189885771⟩,⟨-118231056219,-118230515378⟩,⟨-2261389797561,-2261374183181⟩,⟨1615133634283,1615151813369⟩,⟨-747595334139,-747573428631⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3612533632,-3612522720⟩,⟨54594693069,54594942886⟩,⟨-59115528110,-59115257689⟩,⟨-1130694898781,-1130687091590⟩,⟨807566817141,807575906685⟩,⟨-373797667070,-373786714315⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3612522720,3612533632⟩,⟨-54594942886,-54594693069⟩,⟨59115257689,59115528110⟩,⟨1130687091590,1130694898781⟩,⟨-807575906685,-807566817141⟩,⟨373786714315,373797667070⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765735906336,765735936512⟩,⟨-54594942886,-54594693069⟩,⟨59115257689,59115528110⟩,⟨1130687091590,1130694898781⟩,⟨-807575906685,-807566817141⟩,⟨373786714315,373797667070⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273077561799,273077567197⟩,⟨27118559892,27118683447⟩,⟨-29364172007,-29364038262⟩,⟨-558951547872,-558947705537⟩,⟨398222730142,398227210593⟩,⟨-182517173005,-182511764991⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531471812672,1531471873024⟩,⟨-109189885772,-109189386138⟩,⟨118230515378,118231056220⟩,⟨2261374183180,2261389797562⟩,⟨-1615151813370,-1615133634282⟩,⟨747573428630,747595334140⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1196330129560,1196330287460⟩,⟨-793401782254,-793399147276⟩,⟨859094399202,859097251186⟩,⟨11429816956789,11429886870441⟩,⟨-6319982484489,-6319889934416⟩,⟨-432496886939,-432375512791⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1293148631344,1293148947144⟩,⟨-1586803564507,-1586798294552⟩,⟨1718188798403,1718194502372⟩,⟨22859633913582,22859773740877⟩,⟨-12639964968975,-12639779868834⟩,⟨-864993624205,-864751175254⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨178356110400,178356379008⟩,⟨-1349194460625,-1349189650308⟩,⟨1460905618590,1460910825214⟩,⟨17781034615759,17781170057178⟩,⟨-8954598256882,-8954425468830⟩,⟨-2676567420182,-2676347260190⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨61386603006,61386708254⟩,⟨-457936515559,-457934796728⟩,⟨495852838329,495854698712⟩,⟨5890129648105,5890174787472⟩,⟨-2882299776747,-2882239750195⟩,⟨-1078493857208,-1078414938060⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380360314528,380360337037⟩,⟨10653822487,10654120699⟩,⟨-11536306042,-11535983234⟩,⟨-222289779767,-222280458910⟩,⟨159359516285,159370354998⟩,⟨-74867695538,-74854651051⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178369829599,3178370017690⟩,⟨-89028051827,-89025549368⟩,⟨96397067452,96399776313⟩,⟨1862408774338,1862487161285⟩,⟨-1337132314580,-1337041283197⟩,⟨631348253301,631457658073⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨177450899114,177451213858⟩,⟨-1328732496497,-1328727301278⟩,⟨1438748940723,1438754563844⟩,⟨17204795865595,17204934275591⟩,⟨-8486847308798,-8486665527898⟩,⟨-2995419614695,-2995182359707⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨355807009514,355807592866⟩,⟨-2677926957122,-2677916951586⟩,⟨2899654559313,2899665389058⟩,⟨34985830481354,34986104332769⟩,⟨-17441445565680,-17441090996728⟩,⟨-5671987034877,-5671529619897⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523278319271,523278544912⟩,⟨74995479454,74998890542⟩,⟨-81208968272,-81205276218⟩,⟨-1542940346148,-1542848392265⟩,⟨1098106882982,1098226982370⟩,⟨-501433088251,-501276929879⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360993347389,360993580884⟩,⟨77605553784,77609100322⟩,⟨-84035309325,-84031470657⟩,⟨-1591078623729,-1590982619828⟩,⟨1130302214109,1130427285596⟩,⟨-512364382489,-512202085009⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721986694778,721987161768⟩,⟨155211107568,155218200644⟩,⟨-168070618650,-168062941314⟩,⟨-3182157247458,-3181965239656⟩,⟨2260604428218,2260854571192⟩,⟨-1024728764978,-1024404170018⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524270432094,1524270514035⟩,⟨-715646202,-714652352⟩,⟨773827352,774903170⟩,⟨25567991694,25598975411⟩,⟨-22260892802,-22224791912⟩,⟨17504736610,17548274173⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000901621605,1000902322808⟩,⟨214701699067,214712196788⟩,⟨-232490852098,-232479489600⟩,⟨-4394888379593,-4394601313035⟩,⟨3119512823973,3119883798275⟩,⟨-1409340376379,-1408861373064⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67822252056,67822254738⟩,⟨13470471848,13470533490⟩,⟨-14585924246,-14585857520⟩,⟨-276307605571,-276305679306⟩,⟨196358768360,196361011024⟩,⟨-89092461774,-89089759395⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50193178205,50193180906⟩,⟨265806730573,265806792181⟩,⟨37358806081,37358858488⟩,⟨-1286008116652,-1286006173982⟩,⟨-216046550557,-216044576936⟩,⟨-174057476628,-174055377106⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133134251388,2133134419513⟩,⟨-304173661568,-304172257734⟩,⟨329358411724,329359931346⟩,⟨6321266740067,6321310684262⟩,⟨-4522861142258,-4522810108022⟩,⟨2107965135320,2108026472878⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2971169104644,2971169455908⟩,⟨-635509523645,-635506565572⟩,⟨688127953010,688131155073⟩,⟨13252321261773,13252414011215⟩,⟨-9498668166420,-9498560717428⟩,⟨4457291745347,4457420559488⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135635146167,135635169502⟩,⟨689268291531,689268679530⟩,⟨132366639615,132366941035⟩,⟨-3177426523768,-3177415095264⟩,⟨-872671217322,-872659943173⟩,⟨-220109852066,-220097948430⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8913070437802,8913071971229⟩,⟨-45294317304756,-45294276222865⟩,⟨-8698306489115,-8698283688775⟩,⟨669150498827026,669152077556741⟩,⟨145751149124230,145752206427890⟩,⟨31440766416496,31441639706631⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8113699236378,8113706316507⟩,⟨-39491656965250,-39491505283710⟩,⟨-9802863921190,-9802745185356⟩,⟨555820750559996,555825828599232⟩,⟨165845773848932,165850405157834⟩,⟨20874637801965,20879527196458⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16227398472756,16227412633014⟩,⟨-78983313930500,-78983010567420⟩,⟨-19605727842380,-19605490370712⟩,⟨1111641501119992,1111651657198464⟩,⟨331691547697864,331700810315668⟩,⟨41749275603930,41759054392916⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10888780530353,10888780530452⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239700,2135836853297982⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9789268902577,9789268902676⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239713,2135836853297977⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2403994945600,2403995003456⟩,⟨-12111787164150,-12111787163733⟩,⟨0,0⟩,⟨106474359377039,106474359411671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7615087490280,7615087490425⟩,⟨-47003530101464,-47003530099623⟩,⟨-21044973043472,-21044973042621⟩,⟨580251203849278,580251203883627⟩,⟨312538085376649,312538085394366⟩,⟨116319317651962,116319317659142⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6515575862504,6515575862649⟩,⟨-47003530101464,-47003530099623⟩,⟨-21044973043472,-21044973042621⟩,⟨580251203849281,580251203883622⟩,⟨312538085376650,312538085394364⟩,⟨116319317651961,116319317659142⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1956393462016,1956393500672⟩,⟨-7931904866705,-7931904866180⟩,⟨-3551365689830,-3551365689589⟩,⟨40697157407492,40697157425948⟩,⟨27121552815730,27121552824662⟩,⟨8158303763248,8158303767043⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99813991382,99813991384⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135832177918,135832177922⟩,⟨696930134700,696930134709⟩,⟨312037752616,312037752622⟩,⟨-1746589471214,-1746589471210⟩,⟨-1564007139908,-1564007139896⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4360388407616,4360388504128⟩,⟨-20043692030855,-20043692029913⟩,⟨-3551365689830,-3551365689589⟩,⟨147171516784531,147171516837619⟩,⟨27121552815730,27121552824662⟩,⟨8158303763248,8158303767043⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨711614019028,711615185732⟩,⟨-5355853914244,-5355833903172⟩,⟨5799309118626,5799330778116⟩,⟨69971660962708,69972208665538⟩,⟨-34882891131360,-34882181993456⟩,⟨-11343974069754,-11343059239794⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5072002426644,5072003689860⟩,⟨-25399545945099,-25399525933085⟩,⟨2247943428796,2247965088527⟩,⟨217143177747239,217143725503157⟩,⟨-7761338315630,-7760629168794⟩,⟨-3185670306506,-3184755472751⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨460437883250,460437997935⟩,⟨1741917379114,1741920203974⟩,⟨204068970587,204070936869⟩,⟨-30971741894797,-30971657701380⟩,⟨1089387636341,1089469298402⟩,⟨-289196094424,-289113045538⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35551810499,35551812508⟩,⟨-717394252959,-717394242841⟩,⟨326795816458,326795834885⟩,⟨8940797255142,8940797282190⟩,⟨-6594360098773,-6594360006268⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨495989693749,495989810443⟩,⟨1024523126155,1024525961133⟩,⟨530864787045,530866771754⟩,⟨-22030944639655,-22030860419190⟩,⟨-5504972462432,-5504890707866⟩,⟨-289196094424,-289113045538⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502882001783,502882013886⟩,⟨2533615820870,2533615942923⟩,⟨0,0⟩,⟨3256741201878,3256744126778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226850070299,226850129132⟩,⟨1611498715305,1611500347171⟩,⟨242800839974,242801753562⟩,⟨-3885506643488,-3885452923323⟩,⟨-1294524022429,-1294481937551⟩,⟨-132269191793,-132231204662⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-711615185732,-711614019028⟩,⟨5355833903172,5355853914244⟩,⟨-5799330778116,-5799309118626⟩,⟨-69972208665538,-69971660962708⟩,⟨34882181993456,34882891131360⟩,⟨11343059239794,11343974069754⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3648773221884,3648774485100⟩,⟨-14687858127683,-14687838115669⟩,⟨-9350696467946,-9350674808215⟩,⟨77199308118993,77199855874911⟩,⟨62003734809186,62004443956022⟩,⟨19501363003042,19502277836797⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450764503927,450764659998⟩,⟨498272360822,498275633860⟩,⟨-119662645709,-119659611342⟩,⟨-14878953907074,-14878858861476⟩,⟨-7625708711614,-7625599898823⟩,⟨-4060134879428,-4060009165745⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨317508057822,317508057828⟩,⟨1959793577164,1959793577166⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-317508057828,-317508057822⟩,⟨-1959793577166,-1959793577164⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨782003569948,782003569954⟩,⟨-1959793577166,-1959793577164⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1391442011953,1391442039458⟩,⟨-9128512228313,-9128512158990⟩,⟨-4087124804397,-4087124773351⟩,⟨57220963574058,57220963589310⟩,⟨35862461283297,35862461367981⟩,⟨11470727495526,11470727498669⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1391442039458,-1391442011953⟩,⟨9128512158990,9128512228313⟩,⟨4087124773351,4087124804397⟩,⟨-57220963589310,-57220963574058⟩,⟨-35862461367981,-35862461283297⟩,⟨-11470727498669,-11470727495526⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-291930411682,-291930384177⟩,⟨9128512158990,9128512228313⟩,⟨4087124773351,4087124804397⟩,⟨-57220963589310,-57220963574058⟩,⟨-35862461367981,-35862461283297⟩,⟨-11470727498669,-11470727495526⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12672519834,-12672518638⟩,⟨428021937796,428021943834⟩,⟨60932499224,60932511565⟩,⟨-4470091452281,-4470091436309⟩,⟨1933018792258,1933018854624⟩,⟨2763779919050,2763779944014⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438091984093,438092141360⟩,⟨926294298618,926297577694⟩,⟨-58730146485,-58727099777⟩,⟨-19349045359355,-19348950297785⟩,⟨-5692689919356,-5692581044199⟩,⟨-1296354960378,-1296229221731⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99813991384,-99813991382⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4332864048,4332864049⟩,⟨27231407953,27231407959⟩,⟨39828121951,39828121953⟩,⟨-286374745872,-286374745861⟩,⟨250313839737,250313839741⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9473463498,9473463729⟩,⟨11810188795,11810190256⟩,⟨87081028926,87081031027⟩,⟨-806491306480,-806491290998⟩,⟨108560442911,108560456131⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1485687026815,1485687048000⟩,⟨-7572636333378,-7572635947892⟩,⟨-1425311005500,-1425310936305⟩,⟨112216787420246,112216795179712⟩,⟨23880498968162,23880500544701⟩,⟨5322088917405,5322089217990⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12800775783,12800776278⟩,⟨-49288111187,-49288104071⟩,⟨105385445607,105385451021⟩,⟨-285563692658,-285563537359⟩,⟨-262615046002,-262614959804⟩,⟨-179913048391,-179913028273⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12800776278,-12800775783⟩,⟨49288104071,49288111187⟩,⟨-105385451021,-105385445607⟩,⟨285563537359,285563692658⟩,⟨262614959804,262615046002⟩,⟨179913028273,179913048391⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112614767662,-112614767165⟩,⟨-828173714503,-828173707385⟩,⟨-105385451021,-105385445607⟩,⟨2484586792911,2484586948210⟩,⟨262614959804,262615046002⟩,⟨179913028273,179913048391⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨84925838333,84925840019⟩,⟨-557153332380,-557153328119⟩,⟨626484241384,626484256835⟩,⟨3492447590405,3492447591485⟩,⟨-3557729756150,-3557729716760⟩,⟨-2480009336208,-2480009335813⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨114753871687,114753875602⟩,⟨-1337746645221,-1337746587339⟩,⟨736430388767,736430429248⟩,⟨21061193788772,21061195078304⟩,⟨-6555294328925,-6555293682113⟩,⟨-4564212484920,-4564212286310⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-114753875602,-114753871687⟩,⟨1337746587339,1337746645221⟩,⟨-736430429248,-736430388767⟩,⟨-21061195078304,-21061193788772⟩,⟨6555293682113,6555294328925⟩,⟨4564212286310,4564212484920⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨984757752174,984757756089⟩,⟨1337746587339,1337746645221⟩,⟨-736430429248,-736430388767⟩,⟨-21061195078304,-21061193788772⟩,⟨6555293682113,6555294328925⟩,⟨4564212286310,4564212484920⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121655639486,121655639974⟩,⟨789456303509,789456313156⟩,⟨188493365172,188493371295⟩,⟨-2470300120869,-2470299881860⟩,⟨-678084200853,-678084073240⟩,⟨-167722095469,-167722046680⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11534289827,11534289930⟩,⟨169647299534,169647301742⟩,⟨21587688788,21587689994⟩,⟨738637950589,738638006096⟩,⟨104961368928,104961396348⟩,⟨-16652436897,-16652430534⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170231503146,170231653213⟩,⟨1675214559198,1675219966412⟩,⟨112935484908,112938273733⟩,⟨-1810298793276,-1810087885148⟩,⟨452883140654,453024819012⟩,⟨-577676900800,-577564637352⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170231653213,-170231503146⟩,⟨-1675219966412,-1675214559198⟩,⟨-112938273733,-112935484908⟩,⟨1810087885148,1810298793276⟩,⟨-453024819012,-452883140654⟩,⟨577564637352,577676900800⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56618417086,56618625986⟩,⟨-63721251107,-63714212027⟩,⟨129862566241,129866268654⟩,⟨-2075418758340,-2075154130047⟩,⟨-1747548841441,-1747365078205⟩,⟨445295445559,445445696138⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28873888620754,28873914387033⟩,⟨-257602310078257,-257601665358321⟩,⟨-87298753884513,-87298284914424⟩,⟨3718185877539490,3718208889043641⟩,⟨1387013852152168,1387033387484920⟩,⟨321341383390672,321360423721613⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13460607641,13460607750⟩,⟨174699037324,174699040160⟩,⟨41711756928,41711758452⟩,⟨587015734740,587015817534⟩,⟨120625387158,120625428104⟩,⟨27512960243,27512975390⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353484288820,353484607123⟩,⟨1434052041430,1434064128281⟩,⟨26635771619,26642539079⟩,⟨-20925003309423,-20924499090164⟩,⟨-3495261439970,-3494918687644⟩,⟨-1967157586534,-1966887589449⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353484607123,-353484288820⟩,⟨-1434064128281,-1434052041430⟩,⟨-26642539079,-26635771619⟩,⟨20924499090164,20925003309423⟩,⟨3494918687644,3495261439970⟩,⟨1966887589449,1967157586534⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84607376970,84607852540⟩,⟨-507769829663,-507754463736⟩,⟨-85372685564,-85362871396⟩,⟨1575453730809,1576053011638⟩,⟨-2197771231712,-2197319604229⟩,⟨670532629071,670928364803⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235646169300,235646169306⟩,⟨1574391953272,1574391953283⟩,⟨312037752616,312037752622⟩,⟨-3945612726766,-3945612726762⟩,⟨-1564007139908,-1564007139896⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1662052730738,-1662051273072⟩,⟨-4133165250111,-4133123372355⟩,⟨452686921579,452712690022⟩,⟨41794275781583,41795808806259⟩,⟨-7760209591569,-7759047625787⟩,⟨2136494795290,2137544711687⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-183898090317,-183897928294⟩,⟨-1650679118667,-1650673422063⟩,⟨-234844269977,-234841159472⟩,⟨2423228225363,2423461711459⟩,⟨-217151387346,-216996017988⟩,⟨645137555893,645262861321⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51748078983,51748241012⟩,⟨-76287165395,-76281468780⟩,⟨77193482639,77196593150⟩,⟨-1522384501403,-1522151015303⟩,⟨-1781158527254,-1781003157884⟩,⟨295009724770,295135030200⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4356784991,4356825556⟩,⟨-31050647787,-31049190838⟩,⟨5596709290,5597571956⟩,⟨-19731193529,-19670491482⟩,⟨-302674822781,-302631612652⟩,⟨48626781289,48661934527⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2435502827,2435518080⟩,⟨-7180872892,-7180314188⟩,⟨7266161330,7266476874⟩,⟨-132716845862,-132692838376⟩,⟨-178371792606,-178355411332⟩,⟨38608087014,38620842440⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4333561998,4333589225⟩,⟨-30347028558,-30345924148⟩,⟨5062297690,5062908671⟩,⟨-42401729535,-42350382009⟩,⟨-286534376789,-286500765634⟩,⟨39827089113,39851938149⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4333589225,-4333561998⟩,⟨30345924148,30347028558⟩,⟨-5062908671,-5062297690⟩,⟨42350382009,42401729535⟩,⟨286500765634,286534376789⟩,⟨-39851938149,-39827089113⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨23195766,23263558⟩,⟨-704723639,-702162280⟩,⟨533800619,535274266⟩,⟨22619188480,22731238053⟩,⟨-16174057147,-16097235863⟩,⟨8774843140,8834845414⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56618417086,56618625986⟩,⟨-63721251107,-63714212027⟩,⟨129862566241,129866268654⟩,⟨-2075418758340,-2075154130047⟩,⟨-1747548841441,-1747365078205⟩,⟨445295445559,445445696138⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨23195766,23263558⟩,⟨-704723639,-702162280⟩,⟨533800619,535274266⟩,⟨22619188480,22731238053⟩,⟨-16174057147,-16097235863⟩,⟨8774843140,8834845414⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110810156236,111239652967⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨117682103910,121547574477⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111239652967,-110810156236⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438516160921,438945657652⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46934932848,48524070749⟩,⟨-121547574477,-117682103910⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157745089084,159763723716⟩,⟨977964053299,981829523866⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46505436117,48953567480⟩,⟨-121547574477,-117682103910⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2134856910272,-2120875891328⟩,⟨6730456846765,6843528278778⟩,⟨3017916750346,3059530140386⟩,⟨-42595165089027,-41199245393884⟩,⟨-26706776515621,-26040579303834⟩,⟨-8513529501147,-8283515409879⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310203804098,-304278506895⟩,⟨-940753151432,-892025875194⟩,⟨-419299452771,-401302191316⟩,⟨5783592796353,6311327150053⟩,⟨3608858455093,3862988284143⟩,⟨1170208051563,1254421534119⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨304278506895,310203804098⟩,⟨892025875194,940753151432⟩,⟨401302191316,419299452771⟩,⟨-6311327150053,-5783592796353⟩,⟨-3862988284143,-3608858455093⟩,⟨-1254421534119,-1170208051563⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159763723716,-157745089084⟩,⟨-981829523866,-977964053299⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939747904060,941766538692⟩,⟨-981829523866,-977964053299⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-172634027520,-170274743808⟩,⟨-1148747417602,-1141772195094⟩,⟨-513569492910,-511967242507⟩,⟨-1200187970832,-1185657079521⟩,⟨747111908664,754791209548⟩,⟨-239882523645,-238388072285⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147866513142,-145533098118⟩,⟨-832487149345,-821711039142⟩,⟨-371978182339,-368657480384⟩,⟨1003106678259,1038215036461⟩,⟨1376661065417,1393430853123⟩,⟨202906890460,206303872210⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145533098118,147866513142⟩,⟨821711039142,832487149345⟩,⟨368657480384,371978182339⟩,⟨-1038215036461,-1003106678259⟩,⟨-1393430853123,-1376661065417⟩,⟨-206303872210,-202906890460⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨449811605013,458070317240⟩,⟨1713736914336,1773240300777⟩,⟨769959671700,791277635110⟩,⟨-7349542186514,-6786699474612⟩,⟨-5256419137266,-4985519520510⟩,⟨-1460725406329,-1373114942023⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨808653504222,818801714267⟩,⟨4110628998415,4184325980627⟩,⟨769959671700,791277635110⟩,⟨-19567843516159,-18791727697263⟩,⟨-5256419137266,-4985519520510⟩,⟨-1460725406329,-1373114942023⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨93010872234,97907134960⟩,⟨-243095148954,-235364207820⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12347678441500,12997682857690⟩,⟨29683245822554,33971014080998⟩,⟨-122679775232459,-110608007244123⟩,⟨142714290258950,177574697017409⟩,⟨-363944305315858,-224493397815894⟩,⟨1981608336251736,2315847742381559⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9081298631577,9679320105875⟩,⟨67993992903052,74762344078674⟩,⟨-82712354767095,-71994488188856⟩,⟨95590993422826,179766947419010⟩,⟨-779252112440872,-610166301223116⟩,⟨1263561857457101,1554269974609190⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨86188371968,91808981248⟩,⟨-748689069480,-599730867986⟩,⟨635016639680,828302492226⟩,⟨6495143466206,11322981176454⟩,⟨-8077957125956,-979813811553⟩,⟨-6264628875744,3746059226918⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1185699999744,1191320609024⟩,⟨-748689069480,-599730867986⟩,⟨635016639680,828302492226⟩,⟨6495143466206,11322981176454⟩,⟨-8077957125956,-979813811553⟩,⟨-6264628875744,3746059226918⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨82977075776,88176809280⟩,⟨-694266962689,-553512679871⟩,⟨586079157760,768093296547⟩,⟨5556213543371,10221267602788⟩,⟨-7195729396153,-419305794723⟩,⟨-6345825998149,3161357465652⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨89481471810,95539553635⟩,⟨-812280226552,-642161374397⟩,⟨679943587815,898655748382⟩,⟨7085752884816,12928295536551⟩,⟨-9490427439594,-1165474249834⟩,⟨-6701128080538,4883016149426⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-91808981248,-86188371968⟩,⟨599730867986,748689069480⟩,⟨-828302492226,-635016639680⟩,⟨-11322981176454,-6495143466206⟩,⟨979813811553,8077957125956⟩,⟨-3746059226918,6264628875744⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1007702646528,1013323255808⟩,⟨599730867986,748689069480⟩,⟨-828302492226,-635016639680⟩,⟨-11322981176454,-6495143466206⟩,⟨979813811553,8077957125956⟩,⟨-3746059226918,6264628875744⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-95869688640,-89754040896⟩,⟨650741073104,816900045186⟩,⟨-903766825121,-689028081766⟩,⟨-12961515625958,-7432727148617⟩,⟨1470950242045,9485385559845⟩,⟨-4830222495442,6403590333523⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-88354668175,-82259598045⟩,⟨531123908869,703908467228⟩,⟨-781085538871,-559272229563⟩,⟨-10705390036310,-4712310209779⟩,⟨-587016501730,7910199847264⟩,⟨-4201934835570,7589938072322⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1126803635,13279955590⟩,⟨-281156317683,61747092831⟩,⟨-101141951056,339383518819⟩,⟨-3619637151494,8215985326772⟩,⟨-10077443941324,6744725597430⟩,⟨-10903062916108,12472954221748⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨563401817,6639977795⟩,⟨-140578158842,30873546416⟩,⟨-50570975528,169691759410⟩,⟨-1809818575747,4107992663386⟩,⟨-5038721970662,3372362798715⟩,⟨-5451531458054,6236477110874⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6639977795,-563401817⟩,⟨-30873546416,140578158842⟩,⟨-169691759410,50570975528⟩,⟨-4107992663386,1809818575747⟩,⟨-3372362798715,5038721970662⟩,⟨-6236477110874,5451531458054⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755483405821,761560001063⟩,⟨-30873546416,140578158842⟩,⟨-169691759410,50570975528⟩,⟨-4107992663386,1809818575747⟩,⟨-3372362798715,5038721970662⟩,⟨-6236477110874,5451531458054⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6756122695,7666029922⟩,⟨-125030748206,-94023247820⟩,⟨99555200624,138326155096⟩,⟨1672529752005,2910540732520⟩,⟨-2477045266374,-846353282666⟩,⟨-312689848778,1873571636582⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7666029922,-6756122695⟩,⟨94023247820,125030748206⟩,⟨-138326155096,-99555200624⟩,⟨-2910540732520,-1672529752005⟩,⟨846353282666,2477045266374⟩,⟨-1873571636582,312689848778⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091845597854,1092755505081⟩,⟨94023247820,125030748206⟩,⟨-138326155096,-99555200624⟩,⟨-2910540732520,-1672529752005⟩,⟨846353282666,2477045266374⟩,⟨-1873571636582,312689848778⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7692879424,-6776965120⟩,⟨94604560469,125908609929⟩,⟨-139297366086,-100170715391⟩,⟨-2945394323656,-1691010413190⟩,⟨860204910542,2510388403085⟩,⟨-1904373908772,305759269851⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3846439712,-3388482560⟩,⟨47302280234,62954304965⟩,⟨-69648683043,-50085357695⟩,⟨-1472697161828,-845505206595⟩,⟨430102455271,1255194201543⟩,⟨-952186954386,152879634926⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3388482560,3846439712⟩,⟨-62954304965,-47302280234⟩,⟨50085357695,69648683043⟩,⟨845505206595,1472697161828⟩,⟨-1255194201543,-430102455271⟩,⟨-152879634926,952186954386⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765511866176,765969842592⟩,⟨-62954304965,-47302280234⟩,⟨50085357695,69648683043⟩,⟨845505206595,1472697161828⟩,⟨-1255194201543,-430102455271⟩,⟨-152879634926,952186954386⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272961399463,273188876271⟩,⟨23505811955,31257687052⟩,⟨-34581538774,-24888800156⟩,⟨-727635183130,-418132438001⟩,⟨211588320666,619261316594⟩,⟨-468392909146,78172462195⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531023732352,1531939685184⟩,⟨-125908609930,-94604560468⟩,⟨100170715390,139297366086⟩,⟨1691010413190,2945394323656⟩,⟨-2510388403086,-860204910542⟩,⟨-305759269852,1904373908772⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1193030765538,1199685069579⟩,⟨-891325532892,-706089959397⟩,⟨747633475718,986106503187⟩,⟨8482815153943,14804628011624⟩,⟨-11082216480975,-2038545702466⟩,⟨-6521099318567,6080841698480⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1286549903300,1299858511382⟩,⟨-1782651065784,-1412179918793⟩,⟨1495266951436,1972213006373⟩,⟨16965630307890,29609256023240⟩,⟨-22164432961944,-4077091404931⟩,⟨-13037408594265,12161683396958⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨172731116672,184046497856⟩,⟨-1523489737997,-1194520963342⟩,⟨1264801811379,1685493215147⟩,⟨12239765452715,24006930322369⟩,⟨-17568079765394,-1113261024641⟩,⟨-13725805692610,8938681009171⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59220733234,63590094085⟩,⟨-521146027853,-400341724500⟩,⟨422155886681,577933784921⟩,⟨3928402133059,8035855471405⟩,⟨-5934359071427,-31055187473⟩,⟨-5115514430016,3126046566075⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380087276966,380631610015⟩,⟨1447119112,20064815582⟩,⟨-23314071737,-46250352⟩,⟨-601161326209,145547133427⟩,⟨-324829905746,657179477583⟩,⟨-737340043683,577550060762⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176104631895,3180653215401⟩,⟨-167906752120,-12075197102⟩,⟨385926847,195097236157⟩,⟨-1217878333378,5048376668989⟩,⟨-5520019547475,2718244549121⟩,⟨-4833064755113,6194156304039⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨171067990894,183952613242⟩,⟨-1517275445940,-1157097638089⟩,⟨1219481529859,1683122903070⟩,⟨11286137690524,23697161090982⟩,⟨-17666816310056,62724924366⟩,⟨-15077318148704,9606322794090⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨343799107566,367999111098⟩,⟨-3040765183937,-2351618601431⟩,⟨2484283341238,3368616118217⟩,⟨23525903143239,47704091413351⟩,⟨-35234896075450,-1050536100275⟩,⟨-28803123841314,18545003803261⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519098809009,527482948400⟩,⟨-42768184434,194738645946⟩,⟨-235068830948,70054433632⟩,⟨-5698571919144,2543033870487⟩,⟨-4715023481702,6992919741542⟩,⟨-8654811595988,7604218983403⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356677024854,365353039110⟩,⟨-44434098414,202324140556⟩,⟨-244225274146,72783206476⟩,⟨-5928745908150,2679438072048⟩,⟨-4943766040735,7278744427507⟩,⟨-9008153012938,7954838466400⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713354049708,730706078220⟩,⟨-88868196828,404648281112⟩,⟨-488450548292,145566412952⟩,⟨-11857491816300,5358876144096⟩,⟨-9887532081470,14557488855014⟩,⟨-18016306025876,15909676932800⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523357702430,1525183562489⟩,⟨-31885362110,30426187738⟩,⟨-38155439706,39742165462⟩,⟨-1219530319330,1272864571651⟩,⟨-1664035120420,1616840355832⟩,⟨-2179330906434,2217063757550⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988341877184,1013596283440⟩,⟨-144463357111,581526826191⟩,⟨-702909491388,228333503538⟩,⟨-17282013269705,8301852628198⟩,⟨-14848886350847,21296667737125⟩,⟨-26474889011519,23576352574993⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67764563570,67877556029⟩,⟨11670962206,15532809632⟩,⟨-17184523528,-12357635062⟩,⟨-360577023128,-205831333800⟩,⟨103090324412,306663917842⟩,⟨-231630620202,41021357769⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49838537773,50548132310⟩,⟨261927875327,269883559985⟩,⟨34656535531,39760331779⟩,⟨-1389260876687,-1191320532320⟩,⟨-305906733457,-113915576555⟩,⟨-287405307778,-71386182738⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131886202755,2134437817442⟩,⟨-350854672904,-263465748984⟩,⟨278967022584,388163540536⟩,⟨4725601860826,8236419364002⟩,⟨-7027306051250,-2412836218764⟩,⟨-833771241338,5341989385627⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2968561940262,2973893058968⟩,⟨-733264001365,-550297474124⟩,⟨582674782143,811237167121⟩,⟨9904306798423,17273860037248⟩,⟨-14753298480618,-5075664010876⟩,⟨-1704413761339,11238183601310⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134558637356,136719554413⟩,⟨673466271136,705021033646⟩,⟨119980296856,144836575018⟩,⟨-3668618690411,-2684486321067⟩,⟨-1393365571140,-355849758127⟩,⟨-818982338070,382592592633⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8842376826088,8984379177505⟩,⟨-47073725023198,-43556626370034⟩,⟨-9670629357596,-7759760489723⟩,⟨602730732107305,738237216659475⟩,⟨99462228626037,194372649346959⟩,⟨-11926031573319,75501429959252⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7948339144662,8282343827282⟩,⟨-44575850832854,-34400891638115⟩,⟨-14658616576965,-5109415246076⟩,⟨350779914899485,760758073454577⟩,⟨-46818584948825,384569241618286⟩,⟨-231343510864488,274614662233660⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15896678289324,16564687654564⟩,⟨-89151701665708,-68801783276230⟩,⟨-29317233153930,-10218830492152⟩,⟨701559829798970,1521516146909154⟩,⟨-93637169897650,769138483236572⟩,⟨-462687021728976,549229324467320⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10867759718499,10909882818322⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108414,2148278590204846⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9768248090723,9810371190546⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108424,2148278590204831⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2401631390336,2406362620352⟩,⟨-12184942684160,-12039116462039⟩,⟨0,0⟩,⟨102958094106835,109987257462969⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7566960706071,7663793698015⟩,⟨-47700622321900,-46319748883780⟩,⟨-21325475071326,-20769637070832⟩,⟨567075532699727,593791915480663⟩,⟨306351636376043,318884046704335⟩,⟨114016139586400,118681662095241⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6467449078295,6564282070239⟩,⟨-47700622321900,-46319748883779⟩,⟨-21325475071327,-20769637070831⟩,⟨567075532699729,593791915480654⟩,⟨306351636376044,318884046704331⟩,⟨114016139586400,118681662095240⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1948241863872,1964582165888⟩,⟨-8109439789998,-7758518288558⟩,⟨-3625480081098,-3478896430658⟩,⟨35173553773382,46202108044623⟩,⟨24573935625683,29664275042970⟩,⟨7143111181993,9169353495884⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99599284960,100028781692⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134824055605,136842690238⟩,⟨693197697315,700661226409⟩,⟨311017220470,313057682263⟩,⟨-1753486165281,-1739706366688⟩,⟨-1567950960072,-1560063319732⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4349873254208,4370944786240⟩,⟨-20294382474158,-19797634750597⟩,⟨-3625480081098,-3478896430658⟩,⟨138131647880217,156189365507592⟩,⟨24573935625683,29664275042970⟩,⟨7143111181993,9169353495884⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨687598215132,735998222196⟩,⟨-6081530367874,-4703237202862⟩,⟨4968566682476,6737232236434⟩,⟨47051806286478,95408182826702⟩,⟨-70469792150900,-2101072200550⟩,⟨-57606247682628,37090007606522⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5037471469340,5106943008436⟩,⟨-26375912842032,-24500871953459⟩,⟨1343086601378,3258335805776⟩,⟨185183454166695,251597548334294⟩,⟨-45895856525217,27563202842420⟩,⟨-50463136500635,46259361102406⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨456319463730,464607444251⟩,⟨1618604866384,1858162784082⟩,⟨121663529295,296429207988⟩,⟨-35558074572123,-26272240490176⟩,⟨-3104083818915,5109157706186⟩,⟨-4590916491467,4208475304881⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34520865937,36589834703⟩,⟨-738287075309,-696692100140⟩,⟨325509421405,328085365043⟩,⟨8594307287689,9295026650633⟩,⟨-6627114036394,-6561817940510⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨490840329667,501197278954⟩,⟨880317791075,1161470683942⟩,⟨447172950700,624514573031⟩,⟨-26963767284434,-16977213839543⟩,⟨-9731197855309,-1452660234324⟩,⟨-4590916491467,4208475304881⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502387216868,503376923070⟩,⟨2513460839922,2553938535635⟩,⟨0,0⟩,⟨2096765778922,4420352332343⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨224274033051,229457458892⟩,⟨1524284336746,1695920749440⟩,⟨204321599231,285914415313⟩,⟨-7383707647702,-346533101557⟩,⟨-3432895695309,786871079939⟩,⟨-2101807165260,1926718459606⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-735998222196,-687598215132⟩,⟨4703237202862,6081530367874⟩,⟨-6737232236434,-4968566682476⟩,⟨-95408182826702,-47051806286478⟩,⟨2101072200550,70469792150900⟩,⟨-37090007606522,57606247682628⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3613875032012,3683346571108⟩,⟨-15591145271296,-13716104382723⟩,⟨-10362712317532,-8447463113134⟩,⟨42723465053515,109137559221114⟩,⟨26675007826233,100134067193870⟩,⟨-29946896424529,66775601178512⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443139732183,458420848981⟩,⟨337964218269,665311113901⟩,⟨-267467898186,12895456199⟩,⟨-20506166365681,-9429957699694⟩,⟨-13024466695974,-1870799114133⟩,⟨-10802225210513,2382021256384⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨315490178168,319527447432⟩,⟨1955928106598,1963659047732⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-319527447432,-315490178168⟩,⟨-1963659047732,-1955928106598⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨779984180344,784021449608⟩,⟨-1963659047732,-1955928106598⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1382066178215,1400871549389⟩,⟨-9291165301623,-8969566395519⟩,⟨-4153793061362,-4021926785162⟩,⟨52555172698709,61910935396942⟩,⟨33706285485325,38031433467251⟩,⟨10617189171578,12327768466838⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1400871549389,-1382066178215⟩,⟨8969566395519,9291165301623⟩,⟨4021926785162,4153793061362⟩,⟨-61910935396942,-52555172698709⟩,⟨-38031433467251,-33706285485325⟩,⟨-12327768466838,-10617189171578⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-301359921613,-282554550439⟩,⟨8969566395519,9291165301623⟩,⟨4021926785162,4153793061362⟩,⟨-61910935396942,-52555172698709⟩,⟨-38031433467251,-33706285485325⟩,⟨-12327768466838,-10617189171578⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13417450881,-11951053779⟩,⟨409622963132,446985045599⟩,⟨49804684924,72248669512⟩,⟨-4810679790044,-4142944922684⟩,⟨1707407153378,2154439325211⟩,⟨2659245675340,2867474760369⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429722281302,446469795202⟩,⟨747587181401,1112296159500⟩,⟨-217663213262,85144125711⟩,⟨-25316846155725,-13572902622378⟩,⟨-11317059542596,283640211078⟩,⟨-8142979535173,5249496016753⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100028781692,-99599284960⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4212695952,4453582474⟩,⟨26037482550,28426128067⟩,⟨39722996071,39933365192⟩,⟨-292003417954,-280750603627⟩,⟨249756374792,250871388573⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9201669705,9746995049⟩,⟨7517690603,16085718778⟩,⟨86765789348,87397126939⟩,⟨-874639632610,-737926447910⟩,⟨102988436616,114103164432⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1476457362692,1494986187908⟩,⟨-7735710677178,-7412256648040⟩,⟨-1462862807266,-1388385742785⟩,⟨108308589751709,116231643866500⟩,⟨22930074603302,24856707606167⟩,⟨5087126290539,5563353807967⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12356279498,13252813890⟩,⟨-58480858598,-40160748583⟩,⟨103543672568,107213082274⟩,⟨-509156265292,-61894556108⟩,⟨-306096880580,-218921643474⟩,⟨-189984309190,-169805196275⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13252813890,-12356279498⟩,⟨40160748583,58480858598⟩,⟨-107213082274,-103543672568⟩,⟨61894556108,509156265292⟩,⟨218921643474,306096880580⟩,⟨169805196275,189984309190⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113281595582,-111955564458⟩,⟨-837730566721,-818551463244⟩,⟨-107213082274,-103543672568⟩,⟨2260917811660,2708179520844⟩,⟨218921643474,306096880580⟩,⟨169805196275,189984309190⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨82403710203,87469111921⟩,⟨-578235090062,-536680525416⟩,⟨615596362779,637153075426⟩,⟨3148524200567,3850003383890⟩,⟨-3790281764213,-3321028850356⟩,⟨-2592591023361,-2366716261275⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨110654186430,118930178533⟩,⟨-1401612476928,-1276187833299⟩,⟨710266678340,762271984920⟩,⟨19581165329065,22617768325890⟩,⟨-7240130727849,-5862823839959⟩,⟨-4839261931339,-4290181513407⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-118930178533,-110654186430⟩,⟨1276187833299,1401612476928⟩,⟨-762271984920,-710266678340⟩,⟨-22617768325890,-19581165329065⟩,⟨5862823839959,7240130727849⟩,⟨4290181513407,4839261931339⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨980581449243,988857441346⟩,⟨1276187833299,1401612476928⟩,⟨-762271984920,-710266678340⟩,⟨-22617768325890,-19581165329065⟩,⟨5862823839959,7240130727849⟩,⟨4290181513407,4839261931339⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120240627291,123070924507⟩,⟨774705424231,804588571202⟩,⟨182504998227,194457592937⟩,⟨-2782802014702,-2166257108338⟩,⟨-816006211821,-538948240269⟩,⟨-223204610197,-111490908598⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11399650623,11671290757⟩,⟨166694719346,172621103532⟩,⟨21086253232,22092115664⟩,⟨660728984684,816126289686⟩,⟨91096229252,118791249418⟩,⟨-19645874186,-13671509052⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨164815518077,175833780227⟩,⟨1463719758567,1887290974088⟩,⟨-6337876016,226880636744⟩,⟨-11166773392497,7584409568067⟩,⟨-6070933550408,7085311069249⟩,⟨-6385509497025,5240444681491⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-175833780227,-164815518077⟩,⟨-1887290974088,-1463719758567⟩,⟨-226880636744,6337876016⟩,⟨-7584409568067,11166773392497⟩,⟨-7085311069249,6070933550408⟩,⟨-5240444681491,6385509497025⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48440252824,64641940815⟩,⟨-363006637342,232200990873⟩,⟨-22559037513,292252291329⟩,⟨-14968117215769,10820240290940⟩,⟨-10518206764558,6857804630347⟩,⟨-7342251846751,8312227956631⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28167573090982,29597404090657⟩,⟨-281466946331264,-234083184953162⟩,⟨-107003014407951,-68404597845682⟩,⟨2722618489061485,4729743240875721⟩,⟨477778754814161,2331379849699023⟩,⟨-658778321833117,1312829865264369⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13149300185,13775618263⟩,⟨169440802300,180118985202⟩,⟨39916841106,43532192178⟩,⟨468728972305,703750002376⟩,⟨74507576178,166719259822⟩,⟨10619399555,44397927312⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336862171076,370821490223⟩,⟨814320607848,2049113684019⟩,⟨-318024958743,353763690999⟩,⟨-47649879064033,6055256781680⟩,⟨-21050249143874,14657657537837⟩,⟨-16454675953384,12676642233908⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370821490223,-336862171076⟩,⟨-2049113684019,-814320607848⟩,⟨-353763690999,318024958743⟩,⟨-6055256781680,47649879064033⟩,⟨-14657657537837,21050249143874⟩,⟨-12676642233908,16454675953384⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58900791079,109607624126⟩,⟨-1301526502618,297975551652⟩,⟨-571426904261,403169084454⟩,⟨-31372102937405,34076976441655⟩,⟨-25974717080433,21333889354952⟩,⟨-20819621769081,21704171970137⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234423340565,236871471930⟩,⟨1570230019157,1578552541713⟩,⟨311017220470,313057682263⟩,⟨-3952509420833,-3938729622240⟩,⟨-1567950960072,-1560063319732⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1706643386412,-1618647357543⟩,⟨-5615222738932,-2649360122543⟩,⟨-574706322826,1523496846875⟩,⟨-21630597062519,105216560996430⟩,⟨-61991595153851,45289142054499⟩,⟨-52206855945796,56249825027317⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-191028611307,-177012383241⟩,⟨-1877393895137,-1430212806425⟩,⟨-366162024324,-98146363315⟩,⟨-7450197986101,12363127802031⟩,⟨-7559102067760,7010998955815⟩,⟨-5882787789804,7181515412104⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43394729258,59859088689⟩,⟨-307163875980,148339735288⟩,⟨-55144803854,214911318948⟩,⟨-11402707406934,8424398179791⟩,⟨-9127053027832,5450935636083⟩,⟨-6233258463337,6831730255620⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2594942281,6443996928⟩,⟨-112705942423,40665979127⟩,⟨-35843901634,52836832214⟩,⟨-3886275293638,3941484686323⟩,⟨-3054682505512,2205749735389⟩,⟨-2259720698058,2318972778905⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1712671771,3258820015⟩,⟨-33444939062,16151682524⟩,⟨-6004334328,23400199464⟩,⟨-1324443077501,1088895159235⟩,⟨-1113858289288,651503665436⟩,⟨-700253465236,827873049790⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3034709919,5822784882⟩,⟨-83794052916,16774276609⟩,⟨-21473893132,36391981516⟩,⟨-2549949104861,2575896181947⟩,⟨-2177784296245,1406577906403⟩,⟨-1394387780808,1545998285063⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5822784882,-3034709919⟩,⟨-16774276609,83794052916⟩,⟨-36391981516,21473893132⟩,⟨-2575896181947,2549949104861⟩,⟨-1406577906403,2177784296245⟩,⟨-1545998285063,1394387780808⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3227842601,3409287009⟩,⟨-129480219032,124460032043⟩,⟨-72235883150,74310725346⟩,⟨-6462171475585,6491433791184⟩,⟨-4461260411915,4383534031634⟩,⟨-3805718983121,3713360559713⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48440252824,64641940815⟩,⟨-363006637342,232200990873⟩,⟨-22559037513,292252291329⟩,⟨-14968117215769,10820240290940⟩,⟨-10518206764558,6857804630347⟩,⟨-7342251846751,8312227956631⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3227842601,3409287009⟩,⟨-129480219032,124460032043⟩,⟨-72235883150,74310725346⟩,⟨-6462171475585,6491433791184⟩,⟨-4461260411915,4383534031634⟩,⟨-3805718983121,3713360559713⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (517/5120) u, BivariateJet2.affineZ (557/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000012

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000013Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2117215801024,-2117215762112⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2117215801024,-2117215762112⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-173257488640,-173257488576⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-173257488640,-173257488576⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨87915192320,87915192384⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-95560481728,-95560481664⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨87915315456,87915315520⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-95560627200,-95560627136⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7645311680,-7645311616⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7645289344,-7645289280⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨183475673984,183475674048⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨183475942592,183475942656⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2403994945600,2403995003456⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1943958273472,1943958312064⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1943958273472,1943958312064⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2518909148864,-2518909091008⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2124163443584,-2124163404544⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2110306637888,-2110306599040⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-174441029312,-174441029248⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-172076103488,-172076103424⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨85327631488,85327631552⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-92510845696,-92510845632⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨90525305024,90525305088⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-98652600384,-98652600320⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8127295360,-8127295296⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7183214208,-7183214144⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨177838477120,177838477184⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨189177905344,189177905408⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1935865569792,1935865608384⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1952087301120,1952087339712⟩



end LaneCBRB2Cell000013Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000013
open Set LaneCBRB2Cell000013Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111024904601,111024904602⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨123480309760,123480309760⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111024904602,-111024904601⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438730909286,438730909287⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49271537663,49271537665⟩,⟨-123480309760,-123480309760⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160296442264,160296442267⟩,⟨976031318016,976031318016⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49271537662,49271537666⟩,⟨-123480309760,-123480309760⟩,⟨438730909286,438730909287⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2117215801024,-2117215762112⟩,⟨6694832199984,6694832200111⟩,⟨3009360216624,3009360216688⟩,⟨-40764260291000,-40764260289463⟩,⟨-25865549975621,-25865549974745⟩,⟨-8236610405022,-8236610404673⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308666276775,-308666271095⟩,⟨-903411224123,-903411189542⟩,⟨-406087817579,-406087802030⟩,⟨5942971161674,5942971162237⟩,⟨3689099092128,3689099131354⟩,⟨1200805258260,1200805258392⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨308666271095,308666276775⟩,⟨903411189542,903411224123⟩,⟨406087802030,406087817579⟩,⟨-5942971162237,-5942971161674⟩,⟨-3689099131354,-3689099092128⟩,⟨-1200805258392,-1200805258260⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160296442267,-160296442264⟩,⟨-976031318016,-976031318016⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939215185509,939215185512⟩,⟨-976031318016,-976031318016⟩,⟨-438730909287,-438730909286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173257488640,-173257488576⟩,⟨-1142611192611,-1142611192606⟩,⟨-513609387571,-513609387567⟩,⟨-1187400209783,-1187400209771⟩,⟨753423691431,753423691443⟩,⟨-239919793786,-239919793781⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147998493353,-147998493297⟩,⟨-822231457556,-822231457490⟩,⟨-369597110626,-369597110594⟩,⟨1014290599677,1014290599701⟩,⟨1382182784927,1382182785012⟩,⟨204942183355,204942183366⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147998493297,147998493353⟩,⟨822231457490,822231457556⟩,⟨369597110594,369597110626⟩,⟨-1014290599701,-1014290599677⟩,⟨-1382182785012,-1382182784927⟩,⟨-204942183366,-204942183355⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨456664764392,456664770128⟩,⟨1725642647032,1725642681679⟩,⟨775684912624,775684928205⟩,⟨-6957261761938,-6957261761351⟩,⟨-5071281916366,-5071281877055⟩,⟨-1405747441758,-1405747441615⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨816450716536,816450728176⟩,⟨4129637592556,4129637685147⟩,⟨775684912624,775684928205⟩,⟨-19069048926140,-19069048925046⟩,⟨-5071281916366,-5071281877055⟩,⟨-1405747441758,-1405747441615⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98543075324,98543075332⟩,⟨-246960619520,-246960619520⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12267993621486,12267993622483⟩,⟨30745045197971,30745045202970⟩,⟨-109238482347395,-109238482329390⟩,⟨154101450227333,154101450264906⟩,⟨-273764576483507,-273764576304265⟩,⟨1945394885228681,1945394885711858⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9109691912018,9109692042635⟩,⟨68907121955217,68907123321259⟩,⟨-72461026226864,-72461024882486⟩,⟨132612565460829,132612572365323⟩,⟨-648466655273846,-648466642093395⟩,⟨1274751465340515,1274751489418540⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨91525553152,91525686528⟩,⟨-685412649304,-685410610638⟩,⟨720760843043,720762985938⟩,⟨8895219527855,8895270024786⟩,⟨-4290941206307,-4290873100579⟩,⟨-1384747453676,-1384658325519⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1191037180928,1191037314304⟩,⟨-685412649304,-685410610638⟩,⟨720760843043,720762985938⟩,⟨8895219527855,8895270024786⟩,⟨-4290941206307,-4290873100579⟩,⟨-1384747453676,-1384658325519⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨87915192320,87915315520⟩,⟨-632741941061,-632739988199⟩,⟨665373719407,665375772143⟩,⟨7847535766956,7847585550660⟩,⟨-3578297690818,-3578232012024⟩,⟨-1680992153069,-1680907246396⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨95233429257,95233573378⟩,⟨-740217302751,-740214870763⟩,⟨778391647289,778394203718⟩,⟨10000899434088,10000964129351⟩,⟨-5048822879889,-5048740346689⟩,⟨-1059301432894,-1059196687975⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-91525686528,-91525553152⟩,⟨685410610638,685412649304⟩,⟨-720762985938,-720760843043⟩,⟨-8895270024786,-8895219527855⟩,⟨4290873100579,4290941206307⟩,⟨1384658325519,1384747453676⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1007985941248,1007986074624⟩,⟨685410610638,685412649304⟩,⟨-720762985938,-720760843043⟩,⟨-8895270024786,-8895219527855⟩,⟨4290873100579,4290941206307⟩,⟨1384658325519,1384747453676⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-95560627200,-95560481664⟩,⟨747646178027,747648500735⟩,⟨-786208667682,-786206226179⟩,⟨-10211353296615,-10211293771846⟩,⟨5215090852251,5215169082374⟩,⟨948205309175,948306221676⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-87605968929,-87605823915⟩,⟨625840015182,625842503146⟩,⟨-658120493834,-658117878548⟩,⟨-7656109316142,-7656042273098⟩,⟨3427829594148,3427914391476⟩,⟨1779684326401,1779791148857⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7627460328,7627749463⟩,⟨-114377287569,-114372367617⟩,⟨120271153455,120276325170⟩,⟨2344790117946,2344921856253⟩,⟨-1620993285741,-1620825955213⟩,⟨720382893507,720594460882⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3813730164,3813874732⟩,⟨-57188643785,-57186183808⟩,⟨60135576727,60138162585⟩,⟨1172395058973,1172460928127⟩,⟨-810496642871,-810412977606⟩,⟨360191446753,360297230441⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3813874732,-3813730164⟩,⟨57186183808,57188643785⟩,⟨-60138162585,-60135576727⟩,⟨-1172460928127,-1172395058973⟩,⟨810412977606,810496642871⟩,⟨-360297230441,-360191446753⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758309508884,758309672716⟩,⟨57186183808,57188643785⟩,⟨-60138162585,-60135576727⟩,⟨-1172460928127,-1172395058973⟩,⟨810412977606,810496642871⟩,⟨-360297230441,-360191446753⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7618770614,7618792820⟩,⟨-114110413566,-114109907872⟩,⟨119995156364,119995687988⟩,⟨2335450686349,2335466334802⟩,⟨-1612991413770,-1612973689750⟩,⟨714419423272,714440216561⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7618792820,-7618770614⟩,⟨114109907872,114110413566⟩,⟨-119995687988,-119995156364⟩,⟨-2335466334802,-2335450686349⟩,⟨1612973689750,1612991413770⟩,⟨-714440216561,-714419423272⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091892834956,1091892857162⟩,⟨114109907872,114110413566⟩,⟨-119995687988,-119995156364⟩,⟨-2335466334802,-2335450686349⟩,⟨1612973689750,1612991413770⟩,⟨-714440216561,-714419423272⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7645311680,-7645289280⟩,⟨114906118971,114906630532⟩,⟨-120832970052,-120832432260⟩,⟨-2363770831624,-2363754919227⟩,⟨1636856119321,1636874112469⟩,⟨-732704469910,-732683398697⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3822655840,-3822644640⟩,⟨57453059485,57453315266⟩,⟨-60416485026,-60416216130⟩,⟨-1181885415812,-1181877459613⟩,⟨818428059660,818437056235⟩,⟨-366352234955,-366341699348⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3822644640,3822655840⟩,⟨-57453315266,-57453059485⟩,⟨60416216130,60416485026⟩,⟨1181877459613,1181885415812⟩,⟨-818437056235,-818428059660⟩,⟨366341699348,366352234955⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765946028256,765946058720⟩,⟨-57453315266,-57453059485⟩,⟨60416216130,60416485026⟩,⟨1181877459613,1181885415812⟩,⟨-818437056235,-818428059660⟩,⟨366341699348,366352234955⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272973208739,272973214291⟩,⟨28527476968,28527603392⟩,⟨-29998921997,-29998789091⟩,⟨-583866583701,-583862671587⟩,⟨403243422437,403247853443⟩,⟨-178610054141,-178604855818⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531892056512,1531892117440⟩,⟨-114906630532,-114906118970⟩,⟨120832432260,120832970052⟩,⟨2363754919226,2363770831624⟩,⟨-1636874112470,-1636856119320⟩,⟨732683398696,732704469910⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1199347739070,1199347897768⟩,⟨-815535402240,-815532760717⟩,⟨857594077215,857596853886⟩,⟨11693029637033,11693099559534⟩,⟨-6271860072499,-6271770286566⟩,⟨-421190051914,-421075787577⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1299183850364,1299184167760⟩,⟨-1631070804480,-1631065521434⟩,⟨1715188154430,1715193707772⟩,⟨23386059274069,23386199119054⟩,⟨-12543720144992,-12543540573133⟩,⟨-842379955054,-842151723929⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨183475673984,183475942656⟩,⟨-1380390708175,-1380385899847⟩,⟨1451579665468,1451584719943⟩,⟨18058816562711,18058951823378⟩,⟨-8793478448992,-8793311188496⟩,⟨-2629308802276,-2629102128084⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨63123204437,63123310062⟩,⟨-467954164073,-467952444207⟩,⟨492087214564,492089022418⟩,⟨5965942928482,5965987984932⟩,⟨-2816935740453,-2816877619730⟩,⟨-1063867387557,-1063793237479⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380319297717,380319320580⟩,⟨11218237959,11218543266⟩,⟨-11797142530,-11796821568⟩,⟨-232589512781,-232580014440⟩,⟨161705153602,161715880517⟩,⟨-73540025725,-73527479713⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178712608581,3178712799671⟩,⟨-93764705834,-93762142801⟩,⟨98597950275,98600644734⟩,⟨1949437423616,1949517346651⟩,⟨-1357440060515,-1357349924733⟩,⟨620660058324,620765325864⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨182490590157,182490906493⟩,⟨-1358249055192,-1358243845538⟩,⟨1428295629037,1428301105269⟩,⟨17439401921058,17439540467793⟩,⟨-8305684758466,-8305508333217⟩,⟨-2951777104326,-2951553710774⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨365966264141,365966849149⟩,⟨-2738639763367,-2738629745385⟩,⟨2879875294505,2879885825212⟩,⟨35498218483769,35498492291171⟩,⟨-17099163207458,-17098819521713⟩,⟨-5581085906602,-5580655838858⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522989749937,522989975921⟩,⟨78880160722,78883570954⟩,⟨-82952011122,-82948426378⟩,⟨-1611293924840,-1611202206567⟩,⟨1111592877502,1111709061388⟩,⟨-490400611505,-490254024937⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360694776123,360695009908⟩,⟨81602924098,81606469675⟩,⟨-85815344035,-85811617012⟩,⟨-1660758580898,-1660662804910⟩,⟨1143490684160,1143611685913⟩,⟨-500523187081,-500370843366⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721389552246,721390019816⟩,⟨163205848196,163212939350⟩,⟨-171630688070,-171623234024⟩,⟨-3321517161796,-3321325609820⟩,⟨2286981368320,2287223371826⟩,⟨-1001046374162,-1000741686732⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524273263692,1524273346826⟩,⟨-796722660,-795705404⟩,⟨836744272,837813688⟩,⟨28288584424,28320145275⟩,⟨-23900422720,-23864705550⟩,⟨18243182135,18285046638⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000075651241,1000076353987⟩,⟨225732549649,225743060349⟩,⟨-237385815806,-237374767146⟩,⟨-4586357192598,-4586070358030⟩,⟨3155051809666,3155411249059⟩,⟨-1376061350276,-1375611060490⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67770427166,67770429924⟩,⟨14164901448,14164964512⟩,⟨-14895526262,-14895459964⟩,⟨-288430094094,-288428132571⟩,⟨198667937322,198670155346⟩,⟨-87049253556,-87046656095⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50323445811,50323448578⟩,⟨265056085139,265056148186⟩,⟨36749983893,36750036189⟩,⟨-1283128572405,-1283126588796⟩,⟨-211008229790,-211006270576⟩,⟨-172301957159,-172299929969⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134305098301,2134305268078⟩,⟨-320186812230,-320185374028⟩,⟨336699018858,336700530806⟩,⟨6610609126218,6610653941863⟩,⟨-4586398171488,-4586347627400⟩,⟨2068177045814,2068236078267⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2973615688697,2973616043509⟩,⟨-669149340543,-669146308271⟩,⟨703657705013,703660892778⟩,⟨13865516213406,13865610870742⟩,⟨-9637764828547,-9637658344672⟩,⟨4377727440437,4377851478864⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136099140920,136099164644⟩,⟨686214689925,686215086438⟩,⟨131595524226,131595825193⟩,⟨-3158216212354,-3158204527682⟩,⟨-864516119770,-864504913108⟩,⟨-218586788708,-218575282441⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8882683613649,8882685162027⟩,⟨-44786708608582,-44786667115744⟩,⟨-8588770479557,-8588747842276⟩,⟨657754730647748,657756323229100⟩,⟨143032277614380,143033322119995⟩,⟨30874668776821,30875509379174⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8079364851880,8079371937542⟩,⟨-38912746670136,-38912595073359⟩,⟨-9729819548887,-9729703875682⟩,⟨542827134539426,542832200526304⟩,⟨163491490219503,163495985705695⟩,⟨20674077662956,20678684082458⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16158729703760,16158743875084⟩,⟨-77825493340272,-77825190146718⟩,⟨-19459639097774,-19459407751364⟩,⟨1085654269078852,1085664401052608⟩,⟨326982980439006,326991971411390⟩,⟨41348155325912,41357368164916⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10888780530353,10888780530452⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239700,2135836853297982⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9789268902577,9789268902676⟩,⟨-107834731752838,-107834731750876⟩,⟨0,0⟩,⟨2135836853239713,2135836853297977⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2403994945600,2403995003456⟩,⟨-12111787164150,-12111787163733⟩,⟨0,0⟩,⟨106474359377039,106474359411671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7541813171380,7541813171522⟩,⟨-45921454937276,-45921454935545⟩,⟨-20641921328269,-20641921327444⟩,⟨559223617842938,559223617874541⟩,⟨303104884603316,303104884620044⟩,⟨112993760626511,112993760633413⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6442301543604,6442301543746⟩,⟨-45921454937276,-45921454935544⟩,⟨-20641921328270,-20641921327444⟩,⟨559223617842938,559223617874535⟩,⟨303104884603315,303104884620042⟩,⟨112993760626510,112993760633412⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1943958273472,1943958312064⟩,⟨-7837443392907,-7837443392401⟩,⟨-3522969604342,-3522969604106⟩,⟨39576860072493,39576860088177⟩,⟨26618973662676,26618973670450⟩,⟨7996690609385,7996690612694⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99813991382,99813991384⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136927021919,136927021923⟩,⟨691442517194,691442517200⟩,⟨310806834460,310806834465⟩,⟨-1732836851712,-1732836851712⟩,⟨-1557837486494,-1557837486486⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4347953219072,4347953315520⟩,⟨-19949230557057,-19949230556134⟩,⟨-3522969604342,-3522969604106⟩,⟨146051219449532,146051219499848⟩,⟨26618973662676,26618973670450⟩,⟨7996690609385,7996690612694⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨731932528282,731933698298⟩,⟨-5477279526734,-5477259490770⟩,⟨5759750589010,5759771650424⟩,⟨70996436967538,70996984582342⟩,⟨-34198326414916,-34197639043426⟩,⟨-11162171813204,-11161311677716⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5079885747354,5079887013818⟩,⟨-25426510083791,-25426490046904⟩,⟨2236780984668,2236802046318⟩,⟨217047656417070,217048204082190⟩,⟨-7579352752240,-7578665372976⟩,⟨-3165481203819,-3164621065022⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461153533440,461153648420⟩,⟨1745760826072,1745763655782⟩,⟨203055640601,203057552589⟩,⟨-31039217290612,-31039133059242⟩,⟨1097000186060,1097079394757⟩,⟨-287363321699,-287285238038⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36700702042,36700704115⟩,⟨-740577550182,-740577539740⟩,⟨326795816458,326795834885⟩,⟨9229727866647,9229727894527⟩,⟨-6594360098773,-6594360006268⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497854235482,497854352535⟩,⟨1005183275890,1005186116042⟩,⟨529851457059,529853387474⟩,⟨-21809489423965,-21809405164715⟩,⟨-5497359912713,-5497280611511⟩,⟨-287363321699,-287285238038⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502882001783,502882013886⟩,⟨2533615820870,2533615942923⟩,⟨0,0⟩,⟨3256741201878,3256744126778⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227702852985,227702912003⟩,⟨1606949759154,1606951394208⟩,⟨242337374741,242338263486⟩,⟨-3867827272906,-3867773511865⟩,⟨-1293377308362,-1293336470883⟩,⟨-131430939231,-131395223058⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-731933698298,-731932528282⟩,⟨5477259490770,5477279526734⟩,⟨-5759771650424,-5759750589010⟩,⟨-70996984582342,-70996436967538⟩,⟨34197639043426,34198326414916⟩,⟨11161311677716,11162171813204⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3616019520774,3616020787238⟩,⟨-14471971066287,-14471951029400⟩,⟨-9282741254766,-9282720193116⟩,⟨75054234867190,75054782532310⟩,⟨60816612706102,60817300085366⟩,⟨19158002287101,19158862425898⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450318824896,450318982629⟩,⟨471723742706,471727034494⟩,⟨-133854459546,-133851478594⟩,⟨-14553819182537,-14553723782074⟩,⟨-7478051491988,-7477945186003⟩,⟨-4013691218957,-4013571791336⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨320592884528,320592884534⟩,⟨1952062636032,1952062636032⟩,⟨877461818572,877461818574⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-320592884534,-320592884528⟩,⟨-1952062636032,-1952062636032⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨778918743242,778918743248⟩,⟨-1952062636032,-1952062636032⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1377143721845,1377143749196⟩,⟨-9003506370269,-9003506301350⟩,⟨-4047120685256,-4047120654266⟩,⟨55866184016643,55866184029769⟩,⟨35254690034901,35254690118578⟩,⟨11288025080595,11288025083374⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1377143749196,-1377143721845⟩,⟨9003506301350,9003506370269⟩,⟨4047120654266,4047120685256⟩,⟨-55866184029769,-55866184016643⟩,⟨-35254690118578,-35254690034901⟩,⟨-11288025083374,-11288025080595⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-277632121420,-277632094069⟩,⟨9003506301350,9003506370269⟩,⟨4047120654266,4047120685256⟩,⟨-55866184029769,-55866184016643⟩,⟨-35254690118578,-35254690034901⟩,⟨-11288025083374,-11288025080595⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12441306834,-12441305606⟩,⟨434646332716,434646338911⟩,⟨70578666655,70578678975⟩,⟨-4525758687790,-4525758671517⟩,⟨1835891193052,1835891255272⟩,⟨2723950725522,2723950750429⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437877518062,437877677023⟩,⟨906370075422,906373373405⟩,⟨-63275792891,-63272799619⟩,⟨-19079577870327,-19079482453591⟩,⟨-5642160298936,-5642053930731⟩,⟨-1289740493435,-1289621040907⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99813991384,-99813991382⟩,⟨-877461818574,-877461818572⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4472884789,4472884790⟩,⟨28111417546,28111417551⟩,⟨39828121951,39828121953⟩,⟨-295629225989,-295629225979⟩,⟨250313839737,250313839741⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9779607739,9779607978⟩,⟨12191846606,12191848111⟩,⟨87081028926,87081031027⟩,⟨-832553862164,-832553846214⟩,⟨108560442911,108560456131⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1480708850998,1480708872110⟩,⟨-7489479812015,-7489479430517⟩,⟨-1406776345337,-1406776276962⟩,⟨110347603381413,110347611007844⟩,⟨23428289909542,23428291456777⟩,⟨5222523293650,5222523588341⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13170166983,13170167494⟩,⟨-50196469003,-50196461719⟩,⟨104759173258,104759178676⟩,⟨-305803782617,-305803624365⟩,⟨-254182790213,-254182704257⟩,⟨-176380890420,-176380870455⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13170167494,-13170166983⟩,⟨50196461719,50196469003⟩,⟨-104759178676,-104759173258⟩,⟨305803624365,305803782617⟩,⟨254182704257,254182790213⟩,⟨176380870455,176380890420⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112984158878,-112984158365⟩,⟨-827265356855,-827265349569⟩,⟨-104759178676,-104759173258⟩,⟨2504826879917,2504827038169⟩,⟨254182704257,254182790213⟩,⟨176380870455,176380890420⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨87113051708,87113053446⟩,⟨-569528730806,-569528726419⟩,⟨617812885481,617812900908⟩,⟨3533889527939,3533889528901⟩,⟨-3482781078627,-3482781039351⟩,⟨-2453145564937,-2453145564564⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨117314872751,117314876765⟩,⟨-1360365513187,-1360365454276⟩,⟨720549382853,720549423133⟩,⟨21260644048100,21260645350899⟩,⟨-6313687445072,-6313686805206⟩,⟨-4470797294323,-4470797098796⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-117314876765,-117314872751⟩,⟨1360365454276,1360365513187⟩,⟨-720549423133,-720549382853⟩,⟨-21260645350899,-21260644048100⟩,⟨6313686805206,6313687445072⟩,⟨4470797098796,4470797294323⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨982196751011,982196755025⟩,⟨1360365454276,1360365513187⟩,⟨-720549423133,-720549382853⟩,⟨-21260645350899,-21260644048100⟩,⟨6313686805206,6313687445072⟩,⟨4470797098796,4470797294323⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122317284016,122317284521⟩,⟨787079792893,787079802765⟩,⟨187911406410,187911412570⟩,⟨-2484661815092,-2484661572333⟩,⟨-673932135098,-673932007698⟩,⟨-163367856467,-163367808039⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11610081893,11610082000⟩,⟨170017081954,170017084226⟩,⟨21529789630,21529790844⟩,⟨730073557051,730073613841⟩,⟨105401350686,105401378134⟩,⟨-16286798501,-16286792165⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170625003327,170625154540⟩,⟨1676835120584,1676840554369⟩,⟨110927472263,110930212351⟩,⟨-1875133119563,-1874921695893⟩,⟨468765777639,468904345840⟩,⟨-564835004676,-564728313346⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170625154540,-170625003327⟩,⟨-1676840554369,-1676835120584⟩,⟨-110930212351,-110927472263⟩,⟨1874921695893,1875133119563⟩,⟨-468904345840,-468765777639⟩,⟨564728313346,564835004676⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57077698445,57077908676⟩,⟨-69890795215,-69883726376⟩,⟨131407162390,131410791223⟩,⟨-1992905577013,-1992640392302⟩,⟨-1762281654202,-1762102248522⟩,⟨433297374115,433439781618⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28568953254236,28568978876577⟩,⟨-252778368204197,-252777728398151⟩,⟨-86179616746588,-86179161628424⟩,⟨3610584305985384,3610607090415192⟩,⟨1357382513140006,1357401384591572⟩,⟨315326592284854,315344467866396⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13607421323,13607421436⟩,⟨175120408258,175120411178⟩,⟨41809131048,41809132594⟩,⟨574032154335,574032238900⟩,⟨119085092812,119085133976⟩,⟨27881440614,27881455752⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨353565868579,353566188615⟩,⟨1421853968464,1421866069375⟩,⟨19791283417,19797939227⟩,⟨-20921164738200,-20920661667814⟩,⟨-3444840358842,-3444505423696⟩,⟨-1927096198224,-1926839042482⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-353566188615,-353565868579⟩,⟨-1421866069375,-1421853968464⟩,⟨-19797939227,-19791283417⟩,⟨20920661667814,20921164738200⟩,⟨3444505423696,3444840358842⟩,⟨1926839042482,1927096198224⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84311329447,84311808444⟩,⟨-515495993953,-515480595059⟩,⟨-83073732118,-83064083036⟩,⟨1841083797487,1841682284609⟩,⟨-2197654875240,-2197213571889⟩,⟨637098549047,637475157317⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236741013301,236741013307⟩,⟨1568904335766,1568904335774⟩,⟨310806834460,310806834465⟩,⟨-3931860107264,-3931860107264⟩,⟨-1557837486494,-1557837486486⟩,⟨-350127831123,-350127831121⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1660448183658,-1660446719894⟩,⟨-4160533908205,-4160491946691⟩,⟨460047949926,460073161655⟩,⟨42360723086467,42362256622281⟩,⟨-7809509863421,-7808377809125⟩,⟨2050425147281,2051418706963⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-184719749917,-184719586314⟩,⟨-1651469973427,-1651464240687⟩,⟨-232599038954,-232595974547⟩,⟨2508161141105,2508395586689⟩,⟨-232764438723,-232612161450⟩,⟨632064703186,632184147958⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52021263384,52021426993⟩,⟨-82565637661,-82559904913⟩,⟨78207795506,78210859918⟩,⟨-1423698966159,-1423464520575⟩,⟨-1790601925217,-1790449647936⟩,⟨281936872063,282056316837⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4376758295,4376799282⟩,⟨-32119762732,-32118292288⟩,⟨5763865978,5764718276⟩,⟨8282552027,8343761294⟩,⟨-305549843973,-305507301103⟩,⟨46441006619,46474642439⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2461285334,2461300816⟩,⟨-7812891076,-7812324034⟩,⟨7400500778,7400814028⟩,⟨-122321060061,-122296729786⟩,⟨-181184435586,-181168217516⟩,⟨37804368833,37816627271⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4351601081,4351628541⟩,⟨-31357776941,-31356663764⟩,⟨5197922976,5198526676⟩,⟨-16297964455,-16246302556⟩,⟨-288472602725,-288439497902⟩,⟨37313445451,37337239935⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4351628541,-4351601081⟩,⟨31356663764,31357776941⟩,⟨-5198526676,-5197922976⟩,⟨16246302556,16297964455⟩,⟨288439497902,288472602725⟩,⟨-37337239935,-37313445451⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨25129754,25198201⟩,⟨-763098968,-760515347⟩,⟨565339302,566795300⟩,⟨24528854583,24641725749⟩,⟨-17110346071,-17034698378⟩,⟨9103766684,9161196988⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57077698445,57077908676⟩,⟨-69890795215,-69883726376⟩,⟨131407162390,131410791223⟩,⟨-1992905577013,-1992640392302⟩,⟨-1762281654202,-1762102248522⟩,⟨433297374115,433439781618⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨25129754,25198201⟩,⟨-763098968,-760515347⟩,⟨565339302,566795300⟩,⟨24528854583,24641725749⟩,⟨-17110346071,-17034698378⟩,⟨9103766684,9161196988⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110810156236,111239652967⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121547574476,125413045044⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111239652967,-110810156236⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438516160921,438945657652⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨48476591226,50067239077⟩,⟨-125413045044,-121547574476⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159286747462,161306892044⟩,⟨974098582732,977964053300⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨48047094495,50496735808⟩,⟨-125413045044,-121547574476⟩,⟨438516160921,438945657652⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2124163443584,-2110306599040⟩,⟨6639720750565,6750610865521⟩,⟨2989045364340,3029918447330⟩,⟨-41446353004797,-40095884874511⟩,⟨-26192242681890,-25544789937529⟩,⟨-8349530432922,-8125782360443⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311631268486,-305721072717⟩,⟨-927444460783,-879232729074⟩,⟨-414981519137,-397137064548⟩,⟨5684253443141,6199994859637⟩,⟨3563916004520,3813419019578⟩,⟨1159289778858,1242014739739⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305721072717,311631268486⟩,⟨879232729074,927444460783⟩,⟨397137064548,414981519137⟩,⟨-6199994859637,-5684253443141⟩,⟨-3813419019578,-3563916004520⟩,⟨-1242014739739,-1159289778858⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161306892044,-159286747462⟩,⟨-977964053300,-974098582732⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938204735732,940224880314⟩,⟨-977964053300,-974098582732⟩,⟨-438945657652,-438516160921⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-174441029312,-172076103424⟩,⟨-1146106822103,-1139123991225⟩,⟨-514414217036,-512806699753⟩,⟨-1194676631414,-1180163478588⟩,⟨749569588704,757270539121⟩,⟨-240672294866,-239170468659⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149169678395,-146831203109⟩,⟨-827621134860,-816848539275⟩,⟨-371262006762,-367933845964⟩,⟨996782035173,1031792255134⟩,⟨1373790252439,1390582975519⟩,⟨203237478585,206645297351⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146831203109,149169678395⟩,⟨816848539275,827621134860⟩,⟨367933845964,371262006762⟩,⟨-1031792255134,-996782035173⟩,⟨-1390582975519,-1373790252439⟩,⟨-206645297351,-203237478585⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨452552275826,460800946881⟩,⟨1696081268349,1755065595643⟩,⟨765070910512,786243525899⟩,⟨-7231787114771,-6681035478314⟩,⟨-5204001995097,-4937706256959⟩,⟨-1448660037090,-1362527257443⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨811394175035,821532343908⟩,⟨4092973352428,4166151275493⟩,⟨765070910512,786243525899⟩,⟨-19450088444416,-18686063700965⟩,⟨-5204001995097,-4937706256959⟩,⟨-1448660037090,-1362527257443⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨96094188990,100993471616⟩,⟨-250826090088,-243095148952⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11970336302639,12580633983398⟩,⟨28813057318789,32838106716447⟩,⟨-114933373507041,-103950994779637⟩,⟨138708262001431,171428761721196⟩,⟨-339359582146586,-212532310535926⟩,⟨1805431199672145,2100002331065504⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8833613855287,9399989470903⟩,⟨65822873129689,72205140074138⟩,⟨-77546544740744,-67715327197346⟩,⟨94328046333285,173506892788261⟩,⟨-728551009099889,-574076135324387⟩,⟨1151383963122625,1409580512072382⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨88725894144,94356295424⟩,⟨-763559529612,-615096095495⟩,⟨632780542445,820044157029⟩,⟨6638844951965,11428174209122⟩,⟨-7855675139222,-1012952572687⟩,⟨-5938213773848,3438870767927⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1188237521920,1193867923200⟩,⟨-763559529612,-615096095495⟩,⟨632780542445,820044157029⟩,⟨6638844951965,11428174209122⟩,⟨-7855675139222,-1012952572687⟩,⟨-5938213773848,3438870767927⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨85327631488,90525305088⟩,⟨-706544412056,-566482519593⟩,⟨582769291919,758811322914⟩,⟨5660125404494,10282971459420⟩,⟨-6968840337125,-445283820484⟩,⟨-6018488519581,2873207079639⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨92213207054,98293874528⟩,⟨-830043217540,-659929790578⟩,⟨678903237911,891446002870⟩,⟨7265891937908,13087652564812⟩,⟨-9267575990293,-1211859870913⟩,⟨-6353101403793,4534788038477⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-94356295424,-88725894144⟩,⟨615096095495,763559529612⟩,⟨-820044157029,-632780542445⟩,⟨-11428174209122,-6638844951965⟩,⟨1012952572687,7855675139222⟩,⟨-3438870767927,5938213773848⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1005155332352,1010785733632⟩,⟨615096095495,763559529612⟩,⟨-820044157029,-632780542445⟩,⟨-11428174209122,-6638844951965⟩,⟨1012952572687,7855675139222⟩,⟨-3438870767927,5938213773848⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-98652600384,-92510845632⟩,⟨669088696737,835236658740⟩,⟨-897023630998,-688325469086⟩,⟨-13135445749015,-7628759298849⟩,⟨1520737174432,9274523848497⟩,⟨-4493511836130,6064736599426⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-90691756718,-84571883951⟩,⟨543160184130,716083594782⟩,⟨-771396685981,-555678095337⟩,⟨-10768279314718,-4788638002147⟩,⟨-560492102289,7670746232432⟩,⟨-3871427871564,7221934312121⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1521450336,13721990577⟩,⟨-286883033410,56153804204⟩,⟨-92493448070,335767907533⟩,⟨-3502387376810,8299014562665⟩,⟨-9828068092582,6458886361519⟩,⟨-10224529275357,11756722350598⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨760725168,6860995289⟩,⟨-143441516705,28076902102⟩,⟨-46246724035,167883953767⟩,⟨-1751193688405,4149507281333⟩,⟨-4914034046291,3229443180760⟩,⟨-5112264637679,5878361175299⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6860995289,-760725168⟩,⟨-28076902102,143441516705⟩,⟨-167883953767,46246724035⟩,⟨-4149507281333,1751193688405⟩,⟨-3229443180760,4914034046291⟩,⟨-5878361175299,5112264637679⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755262388327,761362677712⟩,⟨-28076902102,143441516705⟩,⟨-167883953767,46246724035⟩,⟨-4149507281333,1751193688405⟩,⟨-3229443180760,4914034046291⟩,⟨-5878361175299,5112264637679⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7159800854,8097331817⟩,⟨-131052090274,-99271257672⟩,⟨102125376406,140746722066⟩,⟨1759655171806,3021965925827⟩,⟨-2487258707324,-871470481250⟩,⟨-290850290622,1813444260883⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8097331817,-7159800854⟩,⟨99271257672,131052090274⟩,⟨-140746722066,-102125376406⟩,⟨-3021965925827,-1759655171806⟩,⟨871470481250,2487258707324⟩,⟨-1813444260883,290850290622⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091414295959,1092351826922⟩,⟨99271257672,131052090274⟩,⟨-140746722066,-102125376406⟩,⟨-3021965925827,-1759655171806⟩,⟨871470481250,2487258707324⟩,⟨-1813444260883,290850290622⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8127295360,-7183214144⟩,⟨99921929385,132024381241⟩,⟨-141790938653,-102794755390⟩,⟨-3060239138965,-1780269552305⟩,⟨886524348821,2522737588354⟩,⟨-1845183509559,283397729534⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4063647680,-3591607072⟩,⟨49960964692,66012190621⟩,⟨-70895469327,-51397377695⟩,⟨-1530119569483,-890134776152⟩,⟨443262174410,1261368794177⟩,⟨-922591754780,141698864767⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3591607072,4063647680⟩,⟨-66012190621,-49960964692⟩,⟨51397377695,70895469327⟩,⟨890134776152,1530119569483⟩,⟨-1261368794177,-443262174410⟩,⟨-141698864767,922591754780⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765714990688,766187050560⟩,⟨-66012190621,-49960964692⟩,⟨51397377695,70895469327⟩,⟨890134776152,1530119569483⟩,⟨-1261368794177,-443262174410⟩,⟨-141698864767,922591754780⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272853573989,273087956731⟩,⟨24817814418,32763022569⟩,⟨-35186680517,-25531344101⟩,⟨-755491481457,-439913792951⟩,⟨217867620312,621814676831⟩,⟨-453361065221,72712572656⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531429981376,1532374101120⟩,⟨-132024381242,-99921929384⟩,⟨102794755390,141790938654⟩,⟨1780269552304,3060239138966⟩,⟨-2522737588354,-886524348820⟩,⟨-283397729534,1845183509560⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1196025803877,1202725370601⟩,⟨-913642288581,-727820721640⟩,⟨748746081165,981229349264⟩,⟨8741307820934,15062543196924⟩,⟨-10890529534637,-2109862581317⟩,⟨-6167937040483,5715852787152⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1292539979978,1305939113426⟩,⟨-1827284577162,-1455641443280⟩,⟨1497492162329,1962458698528⟩,⟨17482615641871,30125086393844⟩,⟨-21781059069272,-4219725162634⟩,⟨-12331073452537,11431705574303⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨177838477120,189177905408⟩,⟨-1554397288261,-1225550775149⟩,⟨1260786225066,1669384461206⟩,⟨12521693042166,24260157898629⟩,⟨-17122955843080,-1192684983468⟩,⟨-13024167114271,8278774525759⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨60946450246,65337518885⟩,⟨-531140322462,-410204243969⟩,⟨420254251216,571812674747⟩,⟨4004946718129,8102777645535⟩,⟨-5769900399556,-50528943298⟩,⟨-4866832781810,2888965282424⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380037948827,380598896502⟩,⟨1775767085,20864855931⟩,⟨-23529757104,-343850934⟩,⟨-618996369083,142843049638⟩,⟨-318485004148,655065713470⟩,⟨-711306317153,554856597811⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176377626749,3181066057603⟩,⟨-174646993028,-14820081957⟩,⟨2869688860,196953256638⟩,⟨-1195513820970,5200418311557⟩,⟨-5504782129591,2665817092481⟩,⟨-4644361240766,5978300097782⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨176068116153,189032074207⟩,⟨-1547053628033,-1185859959448⟩,⟨1214230995590,1666050891864⟩,⟨11509900801648,23920417780161⟩,⟨-17206346732192,5705722866⟩,⟨-14354332609071,8918357192678⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨353906593273,378209979615⟩,⟨-3101450916294,-2411410734597⟩,⟨2475017220656,3335435353070⟩,⟨24031593843814,48180575678790⟩,⟨-34329302575272,-1186979260602⟩,⟨-27378499723342,17197131718437⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518795127592,527209637779⟩,⟨-38884000544,198653683136⟩,⟨-232504274364,64047580322⟩,⟨-5754022583139,2462673336617⟩,⟨-4516294278040,6817564681280⟩,⟨-8155127739637,7131297962858⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356364077667,365069119230⟩,⟨-40388149649,206338200037⟩,⟨-241498233086,66525131736⟩,⟨-5984214505858,2596811216117⟩,⟨-4736496526615,7093821818598⟩,⟨-8485261497231,7460409300732⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712728155334,730138238460⟩,⟨-80776299298,412676400074⟩,⟨-482996466172,133050263472⟩,⟨-11968429011716,5193622432234⟩,⟨-9472993053230,14187643637196⟩,⟨-16970522994462,14920818601464⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523332649559,1525214300266⟩,⟨-32753123570,31130160890⟩,⟨-37951966676,39665562248⟩,⟨-1241696373523,1300583967160⟩,⟨-1651267107104,1600734358504⟩,⟨-2096841990417,2136033800182⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨987458469608,1012829018210⟩,⟨-133800744843,593126303658⟩,⟨-695202560818,210904098140⟩,⟨-17451440694920,8091489377001⟩,⟨-14265147334847,20772989056848⟩,⟨-24968344882063,22149567658165⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67711037298,67827415580⟩,⟨12317522054,16274838144⟩,⟨-17478775930,-12671659508⟩,⟨-374165576590,-216384496534⟩,⟨106034598228,307730201534⟩,⟨-224018726716,38371636733⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49967949279,50679241852⟩,⟨261146703425,269164574875⟩,⟨34055451758,39151160005⟩,⟨-1387714088255,-1187089765953⟩,⟨-300436656717,-109681129599⟩,⟨-281745674184,-72872380258⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133017722241,2135648524731⟩,⟨-368001096890,-278348013044⟩,⟨286350714908,395224128020⟩,⟨4977378119839,8561731441711⟩,⟨-7065859982064,-2488234562936⟩,⟨-770714140015,5179783496986⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2970925643827,2976423719150⟩,⟨-769317034690,-581536131584⟩,⟨598255705879,826227575884⟩,⟨10436887103244,17964831348498⟩,⟨-14842571626484,-5237556787900⟩,⟨-1571051713772,10904939627311⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135015454254,137190816092⟩,⟨670169387325,702211452415⟩,⟨119207312042,144066715089⟩,⟨-3658952725755,-2655764439463⟩,⟨-1382726820562,-350135209331⟩,⟨-798051115011,364572029473⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8812002538157,8953981055683⟩,⟨-46569395161088,-43046134649000⟩,⟨-9554244325504,-7656891082100⟩,⟨591140199178958,727067276562992⟩,⟨97296748748700,191082639155098⟩,⟨-10871366261788,73314805406797⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7913955906142,8248072701189⟩,⟨-43987605853727,-33829045202273⟩,⟨-14462463204260,-5159045622871⟩,⟨338535265288885,746975199951272⟩,⟨-42875317634689,375792769842757⟩,⟨-217011784888237,259994014256104⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15827911812284,16496145402378⟩,⟨-87975211707454,-67658090404546⟩,⟨-28924926408520,-10318091245742⟩,⟨677070530577770,1493950399902544⟩,⟨-85750635269378,751585539685514⟩,⟨-434023569776474,519988028512208⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10867759718499,10909882818322⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108414,2148278590204846⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9768248090723,9810371190546⟩,⟨-108253100833752,-107418783317397⟩,⟨0,0⟩,⟨2123491006108424,2148278590204831⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2401631390336,2406362620352⟩,⟨-12184942684160,-12039116462039⟩,⟨0,0⟩,⟨102958094106835,109987257462969⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7494570159375,7589619594079⟩,⟨-46597568595605,-45258141657334⟩,⟨-20914675056986,-20374145781355⟩,⟨546608902903705,572185040925096⟩,⟨297155437613425,309206362507986⟩,⟨110775083158214,115268921536075⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6395058531599,6490107966303⟩,⟨-46597568595605,-45258141657334⟩,⟨-20914675056987,-20374145781355⟩,⟨546608902903712,572185040925093⟩,⟨297155437613429,309206362507985⟩,⟨110775083158215,115268921536075⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1935865569792,1952087339712⟩,⟨-8011587109646,-7667338241811⟩,⟨-3595890217860,-3451654473053⟩,⟨34226506281144,44909155141391⟩,⟨24140690199501,29092516022844⟩,⟨7006635446214,8982705922061⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99599284960,100028781692⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135918144959,137938289542⟩,⟨687715838848,695167855170⟩,⟨309785699808,311827366612⟩,⟨-1739706366693,-1725980926276⟩,⟨-1561781306662,-1553893666318⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4337496960128,4358449960064⟩,⟨-20196529793806,-19706454703850⟩,⟨-3595890217860,-3451654473053⟩,⟨137184600387979,154896412604360⟩,⟨24140690199501,29092516022844⟩,⟨7006635446214,8982705922061⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨707813186546,756419959230⟩,⟨-6202901832588,-4822821469194⟩,⟨4950034441312,6670870706140⟩,⟨48063187687628,96361151357580⟩,⟨-68658605150544,-2373958521204⟩,⟨-54756999446684,34394263436874⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5045310146674,5114869919294⟩,⟨-26399431626394,-24529276173044⟩,⟨1354144223452,3219216233087⟩,⟨185247788075607,251257563961940⟩,⟨-44517914951043,26718557501640⟩,⟨-47750364000470,43376969358935⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457029530489,465328600094⟩,⟨1622717799728,1861918930115⟩,⟨122665184233,292870279554⟩,⟨-35605657264064,-26364161749636⟩,⟨-2969904511355,5001081016027⟩,⟨-4344120258172,3946247851187⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35665234997,37743259815⟩,⟨-761585523097,-719760991334⟩,⟨325509421405,328085365043⟩,⟨8878273663409,9588931788898⟩,⟨-6627114036394,-6561817940510⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨492694765486,503071859909⟩,⟨861132276631,1142157938781⟩,⟨448174605638,620955644597⟩,⟨-26727383600655,-16775229960738⟩,⟨-9597018547749,-1560736924483⟩,⟨-4344120258172,3946247851187⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨502387216868,503376923070⟩,⟨2513460839922,2553938535635⟩,⟨0,0⟩,⟨2096765778922,4420352332343⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225121359106,230315677004⟩,⟨1519757321962,1691433279211⟩,⟨204779273915,284285071521⟩,⟨-7359665764194,-336425615151⟩,⟨-3369176144128,729222183421⟩,⟨-1988819248259,1806665842198⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-756419959230,-707813186546⟩,⟨4822821469194,6202901832588⟩,⟨-6670870706140,-4950034441312⟩,⟨-96361151357580,-48063187687628⟩,⟨2373958521204,68658605150544⟩,⟨-34394263436874,54756999446684⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3581077000898,3650636773518⟩,⟨-15373708324612,-13503552871262⟩,⟨-10266760924000,-8401688914365⟩,⟨40823449030399,106833224916732⟩,⟨26514648720705,97751121173388⟩,⟨-27387627990660,63739705368745⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442681396559,457987509689⟩,⟨311174829618,638854070743⟩,⟨-279044794484,-3250097706⟩,⟨-20169867874205,-9111038405882⟩,⟨-12759064297773,-1857345096524⟩,⟨-10422952740206,2122844485281⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨318573494924,322613784088⟩,⟨1948197165464,1955928106600⟩,⟨877032321842,877891315304⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-322613784088,-318573494924⟩,⟨-1955928106600,-1948197165464⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨776897843688,780938132852⟩,⟨-1955928106600,-1948197165464⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1367852552758,1386487785784⟩,⟨-9162882973096,-8847733954714⟩,⟨-4112633464434,-3983040726524⟩,⟨51355047785813,60400860617430⟩,⟨33160968532550,37360901924752⟩,⟨10457247338369,12122235763696⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1386487785784,-1367852552758⟩,⟨8847733954714,9162882973096⟩,⟨3983040726524,4112633464434⟩,⟨-60400860617430,-51355047785813⟩,⟨-37360901924752,-33160968532550⟩,⟨-12122235763696,-10457247338369⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-286976158008,-268340924982⟩,⟨8847733954714,9162882973096⟩,⟨3983040726524,4112633464434⟩,⟨-60400860617430,-51355047785813⟩,⟨-37360901924752,-33160968532550⟩,⟨-12122235763696,-10457247338369⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13179814445,-11726116808⟩,⟨416297641961,453552488183⟩,⟨59486952302,81857009071⟩,⟨-4864283629332,-4200321234174⟩,⟨1612112840966,2055570973664⟩,⟨2620365302948,2826713944553⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429501582114,446261392881⟩,⟨727472471579,1092406558926⟩,⟨-219557842182,78606911365⟩,⟨-25034151503537,-13311359640056⟩,⟨-11146951456807,198225877140⟩,⟨-7802587437258,4949558429834⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100028781692,-99599284960⟩,⟨-877891315304,-877032321842⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4352347110,4593973211⟩,⟨26915532306,29308097793⟩,⟨39722996071,39933365192⟩,⟨-301262427922,-290000553895⟩,⟨249756374792,250871388573⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9506705683,10054250574⟩,⟨7879759327,16486862717⟩,⟨86765789348,87397126939⟩,⟨-901374974739,-763315597624⟩,⟨102988436616,114103164432⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1471549876982,1489936527537⟩,⟨-7650167028055,-7331439203722⟩,⟨-1443753214925,-1370414704417⟩,⟨106523189234004,114276028018779⟩,⟨22499689642134,24382010453481⟩,⟨4993054381687,5458129818984⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12723459420,13624408155⟩,⟨-59409319297,-41048638882⟩,⟨102922358610,106581903829⟩,⟨-529836505410,-81706372267⟩,⟨-297363868676,-210791160882⟩,⟨-186348431745,-166376432625⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13624408155,-12723459420⟩,⟨41048638882,59409319297⟩,⟨-106581903829,-102922358610⟩,⟨81706372267,529836505410⟩,⟨210791160882,297363868676⟩,⟨166376432625,186348431745⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113653189847,-112322744380⟩,⟨-836842676422,-817623002545⟩,⟨-106581903829,-102922358610⟩,⟨2280729627819,2728859760962⟩,⟨210791160882,297363868676⟩,⟨166376432625,186348431745⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨84594572364,89652565901⟩,⟨-590604227132,-549055666441⟩,⟨606930934189,628477475852⟩,⟨3190850214634,3890164237099⟩,⟨-3713979684844,-3247541641591⟩,⟨-2564913591114,-2340689396906⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨113218568508,121487239743⟩,⟨-1424104916586,-1298906465907⟩,⟨694574702079,746205752990⟩,⟨19788344940802,22808016090404⟩,⟨-6990163525358,-5629772383500⟩,⟨-4742019793146,-4200592233549⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-121487239743,-113218568508⟩,⟨1298906465907,1424104916586⟩,⟨-746205752990,-694574702079⟩,⟨-22808016090404,-19788344940802⟩,⟨5629772383500,6990163525358⟩,⟨4200592233549,4742019793146⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨978024388033,986293059268⟩,⟨1298906465907,1424104916586⟩,⟨-746205752990,-694574702079⟩,⟨-22808016090404,-19788344940802⟩,⟨5629772383500,6990163525358⟩,⟨4200592233549,4742019793146⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120900277166,123734551001⟩,⟨772295443085,802245110120⟩,⟨181942254368,193856851491⟩,⟨-2797061772452,-2180661480942⟩,⟨-810852223592,-535810467885⟩,⟨-218374078470,-107621358144⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11474547959,11747986321⟩,⟨167051729502,173003790362⟩,⟨21028466612,22034097766⟩,⟨651859878075,807863860420⟩,⟨91595821968,119172262164⟩,⟨-19255970601,-13329836817⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165180729873,176256881366⟩,⟨1464785290336,1889520424642⟩,⟨-6341838073,222901005795⟩,⟨-11235380250311,7524019143020⟩,⟨-5911900205358,6956814760100⟩,⟨-6085630561160,4969371266192⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176256881366,-165180729873⟩,⟨-1889520424642,-1464785290336⟩,⟨-222901005795,6341838073⟩,⟨-7524019143020,11235380250311⟩,⟨-6956814760100,5911900205358⟩,⟨-4969371266192,6085630561160⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48864477740,65134947131⟩,⟨-369763102680,226647988875⟩,⟨-18121731880,290626909594⟩,⟨-14883684907214,10898954635160⟩,⟨-10325990904228,6641122388779⟩,⟨-6958190514451,7892296403358⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27867562966189,29287472529205⟩,⟨-276391440681566,-229497273956777⟩,⟨-105303397985137,-67854598632549⟩,⟨2628409292247124,4608220259874914⟩,⟨479620786843773,2269333674048090⟩,⟨-604925422658468,1247157151835418⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13293972205,13924581355⟩,⟨169840374152,180562780758⟩,⟨40012071588,43631717706⟩,⟨455378665488,691133462644⟩,⟨73091974878,165057057706⟩,⟨11064121962,44690799481⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336941054678,370906303866⟩,⟨804359132676,2034809858872⟩,⟨-319475300618,341793188923⟩,⟨-47457179340113,5869228025606⟩,⟨-20609465589733,14303180828161⟩,⟨-15738023116515,12046271576028⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370906303866,-336941054678⟩,⟨-2034809858872,-804359132676⟩,⟨-341793188923,319475300618⟩,⟨-5869228025606,47457179340113⟩,⟨-14303180828161,20609465589733⟩,⟨-12046271576028,15738023116515⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58595278248,109320338203⟩,⟨-1307337387293,288047426250⟩,⟨-561351031105,398082211983⟩,⟨-30903379529143,34145819700057⟩,⟨-25450132284968,20807691466873⟩,⟨-19848859013286,20687581546349⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235517429919,237967071234⟩,⟨1564748160690,1573059170474⟩,⟨309785699808,311827366612⟩,⟨-3938729622245,-3925004181828⟩,⟨-1561781306662,-1553893666318⟩,⟨-350470673533,-349785156484⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1705156632998,-1616931051612⟩,⟨-5643538384379,-2676280329941⟩,⟨-545000382173,1508273396055⟩,⟨-20968781390632,105690624436036⟩,⟨-60648627490563,43867993762816⟩,⟨-49422835258798,53267232441538⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-191891367986,-177794765748⟩,⟨-1879247300950,-1430008993889⟩,⟨-361971318632,-97827568642⟩,⟨-7388358093618,12472130208469⟩,⟨-7429866475057,6851853903897⟩,⟨-5595757220767,6864990938169⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43626061933,60172305486⟩,⟨-314499140260,143050176585⟩,⟨-52185618824,213999797970⟩,⟨-11327087715863,8547126026641⟩,⟨-8991647781719,5297960237579⟩,⟨-5946227894300,6515205781685⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2604090395,6476124736⟩,⟨-114210687611,39598661422⟩,⟨-35056149129,52478295293⟩,⟨-3849518396953,3985745774875⟩,⟨-3013772018022,2157866093936⟩,⟨-2164427818115,2220676695625⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1730980584,3293013240⟩,⟨-34422807118,15657240376⟩,⟨-5711861374,23422874106⟩,⟨-1321616109374,1115422469461⟩,⟨-1106583894620,635560701554⟩,⟨-671145159198,796409706039⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3047667373,5846458822⟩,⟨-85109230348,15727243486⟩,⟨-20910525903,36151276734⟩,⟨-2520703990356,2616480887003⟩,⟨-2148515212653,1369711526345⟩,⟨-1333735586930,1478219862109⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5846458822,-3047667373⟩,⟨-15727243486,85109230348⟩,⟨-36151276734,20910525903⟩,⟨-2616480887003,2520703990356⟩,⟨-1369711526345,2148515212653⟩,⟨-1478219862109,1333735586930⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3242368427,3428457363⟩,⟨-129937931097,124707891770⟩,⟨-71207425863,73388821196⟩,⟨-6465999283956,6506449765231⟩,⟨-4383483544367,4306381306589⟩,⟨-3642647680224,3554412282555⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48864477740,65134947131⟩,⟨-369763102680,226647988875⟩,⟨-18121731880,290626909594⟩,⟨-14883684907214,10898954635160⟩,⟨-10325990904228,6641122388779⟩,⟨-6958190514451,7892296403358⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3242368427,3428457363⟩,⟨-129937931097,124707891770⟩,⟨-71207425863,73388821196⟩,⟨-6465999283956,6506449765231⟩,⟨-4383483544367,4306381306589⟩,⟨-3642647680224,3554412282555⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (517/5120) u, BivariateJet2.affineZ (115/1024) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000013

end


