-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000042_000045_data
-- name    : GeneralCK_RB2_cells000042_000045_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T03:33:38.107313+00:00
-- url     : https://prove2.me/theorems/47191c79-cf67-49b4-83d4-6b4c15af76e0
-- title:
--   Exact certificate data for RB2 cells 000042–000045
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000042 through 000045. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000042Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2499969724352,-2499969666496⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2499969724352,-2499969666496⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-119430089600,-119430089536⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-119430089600,-119430089536⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2135881491392,-2135881452288⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2135881491392,-2135881452224⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-170103220736,-170103220672⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-170103220736,-170103220672⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨79657323264,79657323328⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-85882247616,-85882247552⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨79657446848,79657446912⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-85882391296,-85882391232⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6224944448,-6224944384⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6224924352,-6224924288⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨165539570816,165539570880⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨165539838080,165539838144⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1965778231552,1965778270144⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1965778231616,1965778270208⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2497885341504,-2497885283648⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-119669504256,-119669504192⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2142906060864,-2142906021632⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2128896281984,-2128896242880⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-171276311168,-171276311104⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-168932260928,-168932260864⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨77105765120,77105765184⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-82923530688,-82923530624⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨82231622784,82231622848⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-88882419968,-88882419904⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-6650797120,-6650797056⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-5817765568,-5817765504⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨160029295808,160029295872⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨171114042752,171114042816⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2378215779456,2378215837312⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1957619931776,1957619970368⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1973973760768,1973973799360⟩



end LaneCBRB2Cell000042Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000042
open Set LaneCBRB2Cell000042Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨113172388249,113172388250⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113172388250,-113172388249⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436583425638,436583425639⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨44425774366,44425774367⟩,⟨-111883898061,-111883898060⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157598162615,157598162617⟩,⟨987627729715,987627729716⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44425774365,44425774368⟩,⟨-111883898061,-111883898060⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2499969724352,-2499969666496⟩,⟨10682162303971,10682162304067⟩,⟨0,0⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-257321102488,-257321096530⟩,⟨-1400458096586,-1400458038710⟩,⟨0,0⟩,⟨10682162303779,10682162304259⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨257321096530,257321102488⟩,⟨1400458038710,1400458096586⟩,⟨0,0⟩,⟨-10682162304259,-10682162303779⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986339239526,986339239527⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-119430089600,-119430089536⟩,⟨-1225669395649,-1225669395647⟩,⟨0,0⟩,⟨-1366302483285,-1366302483280⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-107137187800,-107137187741⟩,⟨-980081538242,-980081538174⟩,⟨0,0⟩,⟨1225669395643,1225669395653⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨107137187741,107137187800⟩,⟨980081538174,980081538242⟩,⟨0,0⟩,⟨-1225669395653,-1225669395643⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨364458284271,364458290288⟩,⟨2380539576884,2380539634828⟩,⟨0,0⟩,⟨-11907831699912,-11907831699422⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2135881491392,-2135881452224⟩,⟨6890360615273,6890360615369⟩,⟨3045901963653,3045901963699⟩,⟨-43180143083936,-43180143082743⟩,⟨-26758833929191,-26758833928541⟩,⟨-8437854169157,-8437854168901⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-306145919796,-306145914177⟩,⟨-930911133369,-930911098156⟩,⟨-411511705620,-411511690051⟩,⟨6189212591553,6189212591990⟩,⟨3772327467095,3772327506497⟩,⟨1209437244513,1209437244609⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306145914177,306145919796⟩,⟨930911098156,930911133369⟩,⟨411511690051,411511705620⟩,⟨-6189212591990,-6189212591553⟩,⟨-3772327506497,-3772327467095⟩,⟨-1209437244609,-1209437244513⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157598162617,-157598162615⟩,⟨-987627729716,-987627729715⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941913465159,941913465161⟩,⟨-987627729716,-987627729715⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-170103220736,-170103220672⟩,⟨-1152874667265,-1152874667259⟩,⟨-509631267352,-509631267348⟩,⟨-1208827596585,-1208827596573⟩,⟨749113240381,749113240391⟩,⟨-236217627992,-236217627988⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145721527660,-145721527603⟩,⟨-834833840682,-834833840616⟩,⟨-369040486652,-369040486621⟩,⟨1035560663021,1035560663048⟩,⟨1387180711432,1387180711517⟩,⟨202359446581,202359446592⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145721527603,145721527660⟩,⟨834833840616,834833840682⟩,⟨369040486621,369040486652⟩,⟨-1035560663048,-1035560663021⟩,⟨-1387180711517,-1387180711432⟩,⟨-202359446592,-202359446581⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨451867441780,451867447456⟩,⟨1765744938772,1765744974051⟩,⟨780552176672,780552192272⟩,⟨-7224773255038,-7224773254574⟩,⟨-5159508218014,-5159508178527⟩,⟨-1411796691201,-1411796691094⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨816325726051,816325737744⟩,⟨4146284515656,4146284608879⟩,⟨780552176672,780552192272⟩,⟨-19132604954950,-19132604953996⟩,⟨-5159508218014,-5159508178527⟩,⟨-1411796691201,-1411796691094⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨88851548730,88851548736⟩,⟨-223767796122,-223767796120⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13606131089584,13606131090504⟩,⟨34266301611491,34266301616432⟩,⟨-133710923581913,-133710923563524⟩,⟨172595636246451,172595636284549⟩,⟨-336743693501446,-336743693311723⟩,⟨2628022758636704,2628022759181848⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨10101789339796,10101789485177⟩,⟨76749851538634,76749853063793⟩,⟨-89613761792296,-89613760162965⟩,⟨149820333275136,149820341014604⟩,⟨-793761862389487,-793761846278673⟩,⟨1743844028718636,1743844060894495⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨82613790208,82613923072⟩,⟨-622571036826,-622568997916⟩,⟨726916700758,726919080177⟩,⟨8129662023748,8129712766344⟩,⟨-4472575606195,-4472499979902⟩,⟨-1405456927863,-1405346965544⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1182125417984,1182125550848⟩,⟨-622571036826,-622568997916⟩,⟨726916700758,726919080177⟩,⟨8129662023748,8129712766344⟩,⟨-4472575606195,-4472499979902⟩,⟨-1405456927863,-1405346965544⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨79657323264,79657446912⟩,⟨-579062156768,-579060195264⟩,⟨676115463653,676117752777⟩,⟨7256547793081,7256597905431⟩,⟨-3803928362710,-3803855142314⟩,⟨-1722997491196,-1722892251489⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨85642519988,85642662553⟩,⟨-667675149417,-667672752829⟩,⟨779580217289,779583014245⟩,⟨9046513296075,9046577009929⟩,⟨-5179442747061,-5179352483644⟩,⟨-1060284580189,-1060157147171⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-82613923072,-82613790208⟩,⟨622568997916,622571036826⟩,⟨-726919080177,-726916700758⟩,⟨-8129712766344,-8129662023748⟩,⟨4472499979902,4472575606195⟩,⟨1405346965544,1405456927863⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1016897704704,1016897837568⟩,⟨622568997916,622571036826⟩,⟨-726919080177,-726916700758⟩,⟨-8129712766344,-8129662023748⟩,⟨4472499979902,4472575606195⟩,⟨1405346965544,1405456927863⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-85882391296,-85882247552⟩,⟨673147121581,673149414087⟩,⟨-785974810849,-785972135430⟩,⟨-9202299309419,-9202240488884⟩,⟨5317041120672,5317126799501⟩,⟨957672572900,957795492206⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-79429462853,-79429319530⟩,⟨573940154452,573942596701⟩,⟨-670140112100,-670137261836⟩,⟨-7113561481765,-7113495849828⟩,⟨3678106729508,3678199049819⟩,⟨1815190974011,1815320485509⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6213057135,6213343023⟩,⟨-93734994965,-93730156128⟩,⟨109440105189,109445752409⟩,⟨1932951814310,1933081160101⟩,⟨-1501336017553,-1501153433825⟩,⟨754906393822,755163338338⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3106528567,3106671512⟩,⟨-46867497483,-46865078064⟩,⟨54720052594,54722876205⟩,⟨966475907155,966540580051⟩,⟨-750668008777,-750576716912⟩,⟨377453196911,377581669169⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3106671512,-3106528567⟩,⟨46865078064,46867497483⟩,⟨-54722876205,-54720052594⟩,⟨-966540580051,-966475907155⟩,⟨750576716912,750668008777⟩,⟨-377581669169,-377453196911⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨759016712104,759016874313⟩,⟨46865078064,46867497483⟩,⟨-54722876205,-54720052594⟩,⟨-966540580051,-966475907155⟩,⟨750576716912,750668008777⟩,⟨-377581669169,-377453196911⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6207336202,6207356169⟩,⟨-93556147010,-93555690152⟩,⟨109236396046,109236929292⟩,⟨1926699678838,1926713886807⟩,⟨-1495310757490,-1495292921396⟩,⟨749964927892,749988084399⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6207356169,-6207336202⟩,⟨93555690152,93556147010⟩,⟨-109236929292,-109236396046⟩,⟨-1926713886807,-1926699678838⟩,⟨1495292921396,1495310757490⟩,⟨-749988084399,-749964927892⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1093304271607,1093304291574⟩,⟨93555690152,93556147010⟩,⟨-109236929292,-109236396046⟩,⟨-1926713886807,-1926699678838⟩,⟨1495292921396,1495310757490⟩,⟨-749988084399,-749964927892⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6224944448,-6224924288⟩,⟨94086861232,94087322404⟩,⟨-109857134065,-109856595784⟩,⟨-1945704251373,-1945689848421⟩,⟨1513183179094,1513201236060⟩,⟨-765222543444,-765199134123⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3112472224,-3112462144⟩,⟨47043430616,47043661202⟩,⟨-54928567033,-54928297892⟩,⟨-972852125687,-972844924210⟩,⟨756591589547,756600618030⟩,⟨-382611271722,-382599567061⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3112462144,3112472224⟩,⟨-47043661202,-47043430616⟩,⟨54928297892,54928567033⟩,⟨972844924210,972852125687⟩,⟨-756600618030,-756591589547⟩,⟨382599567061,382611271722⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765235845760,765235875104⟩,⟨-47043661202,-47043430616⟩,⟨54928297892,54928567033⟩,⟨972844924210,972852125687⟩,⟨-756600618030,-756591589547⟩,⟨382599567061,382611271722⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273326067901,273326072894⟩,⟨23388922538,23389036753⟩,⟨-27309232323,-27309099011⟩,⟨-481678471702,-481674919709⟩,⟨373823230349,373827689373⟩,⟨-187497021100,-187491231973⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530471691520,1530471750208⟩,⟨-94087322404,-94086861232⟩,⟨109856595784,109857134066⟩,⟨1945689848420,1945704251374⟩,⟨-1513201236060,-1513183179094⟩,⟨765199134122,765222543444⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1188837044344,1188837199674⟩,⟨-727836836091,-727834262242⟩,⟨849825292263,849828296072⟩,⟨10395437059527,10395505052054⟩,⟨-6269383042495,-6269286040959⟩,⟨-428120982527,-427983567973⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1278162460912,1278162771572⟩,⟨-1455673672182,-1455668524484⟩,⟨1699650584526,1699656592144⟩,⟨20790874119058,20791010104103⟩,⟨-12538766084989,-12538572081920⟩,⟨-856241818236,-855967282765⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨165539570816,165539838144⟩,⟨-1252211810125,-1252207077575⟩,⟨1462087319710,1462092842999⟩,⟨16458776696026,16458908800792⟩,⟨-9121066758633,-9120884666585⟩,⟨-2680804419671,-2680553388164⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57030090300,57030194207⟩,⟨-426253082591,-426251395787⟩,⟨497694648126,497696616703⟩,⟨5486383941071,5486428058944⟩,⟨-2969153095440,-2969089877807⟩,⟨-1070945684670,-1070855898950⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380457831376,380457852916⟩,⟨9167311416,9167586717⟩,⟨-10704149857,-10703828522⟩,⟨-190801767244,-190793168899⟩,⟨148854610550,148865378624⟩,⟨-76224979735,-76211035371⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177555175557,3177555355458⟩,⟨-76566998671,-76564690707⟩,⟨89397565216,89400259106⟩,⟨1597179822586,1597252037997⟩,⟨-1247620921952,-1247530587582⟩,⟨641539030994,641655868235⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨164815227067,164815536687⟩,⟨-1235829946538,-1235824875035⟩,⟨1442959324973,1442965243712⟩,⟨15997690397045,15997824715101⟩,⟨-8714791561294,-8714601211734⟩,⟨-2980793203581,-2980524670624⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨330354797883,330355374831⟩,⟨-2488041756663,-2488031952610⟩,⟨2905046644683,2905058086711⟩,⟨32456467093071,32456733515893⟩,⟨-17835858319927,-17835485878319⟩,⟨-5661597623252,-5661078058788⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523965690493,523965914447⟩,⟨64703958676,64707312862⟩,⟨-75552791624,-75548877076⟩,⟨-1330453004677,-1330363016779⟩,⟨1031613551438,1031740295972⟩,⟨-515859163308,-515681115415⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361704874788,361705106689⟩,⟨66999818010,67003305531⟩,⟨-78233611581,-78229541415⟩,⟨-1373524253504,-1373430349568⟩,⟨1063387056251,1063519026662⟩,⟨-528523430359,-528338366655⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨723409749576,723410213378⟩,⟨133999636020,134006611062⟩,⟨-156467223162,-156459082830⟩,⟨-2747048507008,-2746860699136⟩,⟨2126774112502,2127038053324⟩,⟨-1057046860718,-1056676733310⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524264335351,1524264414006⟩,⟨-531632252,-530714222⟩,⟨619666492,620738020⟩,⟨18975961613,19004572536⟩,⟨-17908314664,-17872421604⟩,⟨15211049723,15257615552⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002870413798,1002871108523⟩,⟨185415299650,185425583042⟩,⟨-216504438362,-216492436879⟩,⟨-3795906533575,-3795626914343⟩,⟨2936737420391,2937127368481⟩,⟨-1455563817553,-1455019672502⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67945747463,67945749947⟩,⟨11628439514,11628496514⟩,⟨-13577528490,-13577461960⟩,⟨-238484505409,-238482725344⟩,⟨184694539716,184696771386⟩,⟨-91862671194,-91859778023⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50445907281,50445909849⟩,⟨264858494974,264858552547⟩,⟨38154680729,38154732998⟩,⟨-1271683317580,-1271681518290⟩,⟨-224659238150,-224657272528⟩,⟨-174724288671,-174722041632⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130349092607,2130349255990⟩,⟨-261930816110,-261929522202⟩,⟨305831072134,305832582394⟩,⟨5432731215369,5432771677490⟩,⟨-4231420294240,-4231369679418⟩,⟨2152199312669,2152264778978⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2965351977118,2965352318251⟩,⟨-546894236183,-546891513618⟩,⟨638555045437,638558223246⟩,⟨11376803912798,11376889160880⟩,⟨-8874181993233,-8874075587775⟩,⟨4539484984459,4539622297034⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136051195016,136051217594⟩,⟨689224256703,689224620343⟩,⟨132199189967,132199490065⟩,⟨-3171203488921,-3171192935019⟩,⟨-878207950107,-878196757129⟩,⟨-218636076228,-218623370010⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8885814041166,8885815515788⟩,⟨-45014840366430,-45014801675638⟩,⟨-8634251833369,-8634229367537⟩,⟨663200364950328,663201831322939⟩,⟨144837613804340,144838652173775⟩,⟨31058324522509,31059243668455⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8104798329801,8104805289304⟩,⟨-39559851743608,-39559704656006⟩,⟨-9625055286080,-9624932057771⟩,⟨559048651862414,559053528322763⟩,⟨163247944533260,163252722005607⟩,⟨19965313116907,19970767952418⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16209596659602,16209610578608⟩,⟨-79119703487216,-79119409312012⟩,⟨-19250110572160,-19249864115542⟩,⟨1118097303724828,1118107056645526⟩,⟨326495889066520,326505444011214⟩,⟨39930626233814,39941535904836⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10682162303971,10682162304067⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848532,2016544728902914⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9582650676195,9582650676291⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848550,2016544728902902⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2380539576896,2380539634752⟩,⟨-11907831699843,-11907831699439⟩,⟨0,0⟩,⟨102414856889766,102414856913318⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7670938541032,7670938541130⟩,⟨-48071827047091,-48071827045812⟩,⟨-21250277100847,-21250277100253⟩,⟨602507905170010,602507905194343⟩,⟨319857865989207,319857866001674⟩,⟨117736382431457,117736382436514⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6571426913256,6571426913354⟩,⟨-48071827047092,-48071827045812⟩,⟨-21250277100847,-21250277100253⟩,⟨602507905170013,602507905194341⟩,⟨319857865989207,319857866001674⟩,⟨117736382431456,117736382436515⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1965778231552,1965778270208⟩,⟨-8043235282770,-8043235282380⟩,⟨-3555533231112,-3555533230934⟩,⟨41971315479531,41971315492783⟩,⟨27507947165788,27507947172164⟩,⟨8201636539583,8201636542263⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101523589692,101523589694⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135008878215,135008878218⟩,⟨704505093043,704505093050⟩,⟨311428322278,311428322282⟩,⟨-1774257784753,-1774257784749⟩,⟨-1568630605092,-1568630605084⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4346317808448,4346317904960⟩,⟨-19951066982613,-19951066981819⟩,⟨-3555533231112,-3555533230934⟩,⟨144386172369297,144386172406101⟩,⟨27507947165788,27507947172164⟩,⟨8201636539583,8201636542263⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨660709595766,660710749662⟩,⟨-4976083513326,-4976063905220⟩,⟨5810093289366,5810116173422⟩,⟨64912934186142,64913467031786⟩,⟨-35671716639854,-35670971756638⟩,⟨-11323195246504,-11322156117576⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5007027404214,5007028654622⟩,⟨-24927150495939,-24927130887039⟩,⟨2254560058254,2254582942488⟩,⟨209299106555439,209299639437887⟩,⟨-8163769474066,-8163024584474⟩,⟨-3121558706921,-3120519575313⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨462324711190,462324826657⟩,⟨1674631269996,1674634073644⟩,⟨208175179332,208177292356⟩,⟨-30279715115864,-30279632266337⟩,⟨1036634716580,1036721669406⟩,⟨-288229644291,-288133695894⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨226344776498,226344776500⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-226344776500,-226344776498⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨873166851276,873166851278⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1890483187431,1890483233382⟩,⟨-14217572178026,-14217572061970⟩,⟨0,0⟩,⟨128963125257405,128963125277912⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨790971559655,790971605606⟩,⟨-14217572178026,-14217572061970⟩,⟨0,0⟩,⟨128963125257405,128963125277912⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨31959210935,31959212795⟩,⟨-654948635323,-654948625916⟩,⟨314071324370,314071342618⟩,⟨8104253966461,8104253991289⟩,⟨-6436347433334,-6436347341287⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨494283922125,494284039452⟩,⟨1019682634673,1019685447728⟩,⟨522246503702,522248634974⟩,⟨-22175461149403,-22175378275048⟩,⟨-5399712716754,-5399625671881⟩,⟨-288229644291,-288133695894⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507836879489,507836891833⟩,⟨2540279524621,2540279648204⟩,⟨0,0⟩,⟨3565745386739,3565748309078⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228297362440,228297422180⟩,⟨1612944992288,1612946629643⟩,⟨241212578443,241213568688⟩,⟨-3927624505267,-3927571056866⟩,⟨-1287409052302,-1287363805104⟩,⟨-133126056145,-133081736747⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-660710749662,-660709595766⟩,⟨4976063905220,4976083513326⟩,⟨-5810116173422,-5810093289366⟩,⟨-64913467031786,-64912934186142⟩,⟨35670971756638,35671716639854⟩,⟨11322156117576,11323195246504⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3685607058786,3685608309194⟩,⟨-14975003077393,-14974983468493⟩,⟨-9365649404534,-9365626520300⟩,⟨79472705337511,79473238219959⟩,⟨63178918922426,63179663812018⟩,⟨19523792657159,19524831788767⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨452555172658,452555326206⟩,⟨522750794588,522754003620⟩,⟨-106086551566,-106083387404⟩,⟨-15379219176553,-15379126597256⟩,⟨-7742920216886,-7742806750770⟩,⟨-4070356081975,-4070215129155⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨315196325230,315196325234⟩,⟨1975255459430,1975255459432⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-315196325234,-315196325230⟩,⟨-1975255459432,-1975255459430⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨784315302542,784315302546⟩,⟨-1975255459432,-1975255459430⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1402249789325,1402249816908⟩,⟨-9268975895354,-9268975825596⟩,⟨-4097375080511,-4097375049667⟩,⟨58838517183553,58838517194592⟩,⟨36328737043057,36328737125671⟩,⟨11497665178108,11497665180347⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1402249816908,-1402249789325⟩,⟨9268975825596,9268975895354⟩,⟨4097375049667,4097375080511⟩,⟨-58838517194592,-58838517183553⟩,⟨-36328737125671,-36328737043057⟩,⟨-11497665180347,-11497665178108⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-302738189132,-302738161549⟩,⟨9268975825596,9268975895354⟩,⟨4097375049667,4097375080511⟩,⟨-58838517194592,-58838517183553⟩,⟨-36328737125671,-36328737043057⟩,⟨-11497665180347,-11497665178108⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12232138473,-12232137357⟩,⟨405319000699,405319006352⟩,⟨45346117769,45346129981⟩,⟨-4263752086851,-4263752072029⟩,⟨2098370507558,2098370569431⟩,⟨2789328747487,2789328772113⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨440323034185,440323188849⟩,⟨928069795287,928073009972⟩,⟨-60740433797,-60737257423⟩,⟨-19642971263404,-19642878669285⟩,⟨-5644549709328,-5644436181339⟩,⟨-1281027334488,-1280886357042⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101523589694,-101523589692⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4102061291,4102061293⟩,⟨24949493815,24949493819⟩,⟨40312003485,40312003486⟩,⟨-266554646204,-266554646195⟩,⟨245185044806,245185044811⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8881324220,8881324441⟩,⟨9592078594,9592079942⟩,⟨87279040344,87279042468⟩,⟨-735436175848,-735436161421⟩,⟨94263805138,94263818079⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1480935567406,1480935588620⟩,⟨-7521973449916,-7521973065292⟩,⟨-1416037108010,-1416037039140⟩,⟨111120637111997,111120644827903⟩,⟨23744791048018,23744792616910⟩,⟨5269172979855,5269173278046⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11962282699,11962283169⟩,⟨-47839272421,-47839265799⟩,⟨106118341279,106118346667⟩,⟨-224224951631,-224224808190⟩,⟨-290683212133,-290683128036⟩,⟨-182247724450,-182247704575⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-11962283169,-11962282699⟩,⟨47839265799,47839272421⟩,⟨-106118346667,-106118341279⟩,⟨224224808190,224224951631⟩,⟨290683128036,290683212133⟩,⟨182247704575,182247724450⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113485872863,-113485872391⟩,⟨-825327585479,-825327578855⟩,⟨-106118346667,-106118341279⟩,⟨2423248063742,2423248207183⟩,⟨290683128036,290683212133⟩,⟨182247704575,182247724450⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨79427282040,79427283609⟩,⟨-525020269794,-525020265819⟩,⟨636890833713,636890849083⟩,⟨3332775326369,3332775327114⟩,⟨-3686246152125,-3686246112950⟩,⟨-2492206205438,-2492206205157⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨106980848609,106980852256⟩,⟨-1250528949451,-1250528895447⟩,⟨755537537061,755537577049⟩,⟨19699666427001,19699667629972⟩,⟨-6930655958189,-6930655321131⟩,⟨-4616597768774,-4616597571873⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-106980852256,-106980848609⟩,⟨1250528895447,1250528949451⟩,⟨-755537577049,-755537537061⟩,⟨-19699667629972,-19699666427001⟩,⟨6930655321131,6930655958189⟩,⟨4616597571873,4616597768774⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨992530775520,992530779167⟩,⟨1250528895447,1250528949451⟩,⟨-755537577049,-755537537061⟩,⟨-19699667629972,-19699666427001⟩,⟨6930655321131,6930655958189⟩,⟨4616597571873,4616597768774⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121872714404,121872714856⟩,⟨789510058625,789510067605⟩,⟨188354455076,188354461027⟩,⟨-2418007659668,-2418007436788⟩,⟨-694894071468,-694893947083⟩,⟨-174103599314,-174103551311⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11713421583,11713421682⟩,⟨170372041420,170372043498⟩,⟨21905966670,21905967876⟩,⟨738802872479,738802924061⟩,⟨99305826776,99305853758⟩,⟨-17137499037,-17137492696⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172685612928,172685762672⟩,⟨1668831485576,1668836814056⟩,⟨117872533885,117875456287⟩,⟨-1716334249943,-1716128669967⟩,⟨383094659854,383242309005⟩,⟨-594311617659,-594185216970⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172685762672,-172685612928⟩,⟨-1668836814056,-1668831485576⟩,⟨-117875456287,-117872533885⟩,⟨1716128669967,1716334249943⟩,⟨-383242309005,-383094659854⟩,⟨594185216970,594311617659⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨55611599768,55611809252⟩,⟨-55891821768,-55884855933⟩,⟨123337122156,123341034803⟩,⟨-2211495835300,-2211236806923⟩,⟨-1670651361307,-1670458464958⟩,⟨461059160825,461229880912⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28980568691334,28980594146526⟩,⟨-260033180517251,-260032549962911⟩,⟨-86834241426440,-86833755105470⟩,⟨3775332047202243,3775354358941753⟩,⟨1385937244017550,1385957440975568⟩,⟨316801596623473,316822800870446⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13508687076,13508687177⟩,⟨175022676364,175022679006⟩,⟨41755390538,41755392014⟩,⟨597787174490,597787251681⟩,⟨116450082426,116450122198⟩,⟨25936828810,25936843674⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨356057565782,356057881190⟩,⟨1418402283579,1418414176158⟩,⟨33722572004,33729560559⟩,⟨-20644998823996,-20644506483519⟩,⟨-3600477433604,-3600123503092⟩,⟨-2019403745246,-2019105036343⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-356057881190,-356057565782⟩,⟨-1418414176158,-1418402283579⟩,⟨-33729560559,-33722572004⟩,⟨20644506483519,20644998823996⟩,⟨3600123503092,3600477433604⟩,⟨2019105036343,2019403745246⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84265152995,84265623067⟩,⟨-490344380871,-490329273607⟩,⟨-94469994356,-94459829427⟩,⟨1001535220115,1002120154711⟩,⟨-2044426206236,-2043958747735⟩,⟨738077701855,738517388204⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236532467907,236532467912⟩,⟨1577671944319,1577671944328⟩,⟨311428322278,311428322282⟩,⟨-3973281040305,-3973281040301⟩,⟨-1568630605092,-1568630605084⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1673071715489,-1673070271882⟩,⟨-4001143289828,-4001102346934⟩,⟨422415312497,422442181546⟩,⟨39098612885538,39100095389903⟩,⟨-7329103777000,-7327898611766⟩,⟨2280002279098,2281178697613⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-185447599611,-185447438910⟩,⟨-1644854963582,-1644849373465⟩,⟨-239787932962,-239784698196⟩,⟨2267065267890,2267291986335⟩,⟨-137100341367,-136939320697⟩,⟨662371489423,662511399577⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51084868296,51085029002⟩,⟨-67183019263,-67177429137⟩,⟨71640389316,71643624086⟩,⟨-1706215772415,-1705989053966⟩,⟨-1705730946459,-1705569925781⟩,⟨315662854920,315802765077⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4262001277,4262041109⟩,⟨-29084455821,-29083040548⟩,⟨4674233570,4675118289⟩,⟨-68987116745,-68928794888⟩,⟨-281646341581,-281602256445⟩,⟨51470896101,51509509262⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2373475371,2373490305⟩,⟨-6242856194,-6242317102⟩,⟨6657028012,6657349540⟩,⟨-150338155860,-150315223543⟩,⟨-167257075824,-167240490924⟩,⟨38667968966,38681905217⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4243453274,4243480059⟩,⟨-28524129462,-28523056169⟩,⟨4226619329,4227242707⟩,⟨-86853784594,-86804322100⟩,⟨-268167016572,-268132890135⟩,⟨43781418696,43808527074⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4243480059,-4243453274⟩,⟨28523056169,28524129462⟩,⟨-4227242707,-4226619329⟩,⟨86804322100,86853784594⟩,⟨268132890135,268167016572⟩,⟨-43808527074,-43781418696⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨18521218,18587835⟩,⟨-561399652,-558911086⟩,⟨446990863,448498960⟩,⟨17817205355,17924989706⟩,⟨-13513451446,-13435239873⟩,⟨7662369027,7728090566⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨55611599768,55611809252⟩,⟨-55891821768,-55884855933⟩,⟨123337122156,123341034803⟩,⟨-2211495835300,-2211236806923⟩,⟨-1670651361307,-1670458464958⟩,⟨461059160825,461229880912⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨18521218,18587835⟩,⟨-561399652,-558911086⟩,⟨446990863,448498960⟩,⟨17817205355,17924989706⟩,⟨-13513451446,-13435239873⟩,⟨7662369027,7728090566⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112957639884,113387136615⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113387136615,-112957639884⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436368677273,436798174004⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨43636867727,45215435981⟩,⟨-113816633344,-109951162777⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156594507611,158602572596⟩,⟨985694994432,989560464999⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨43207370996,45644932712⟩,⟨-113816633344,-109951162777⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2502058066176,-2497885283648⟩,⟨10661930935953,10702470597440⟩,⟨0,0⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-258024738076,-256618683435⟩,⟨-1406711255186,-1394193003281⟩,⟨0,0⟩,⟨10580697469779,10783396361089⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256618683435,258024738076⟩,⟨1394193003281,1406711255186⟩,⟨0,0⟩,⟨-10783396361089,-10580697469779⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986124491161,986553987892⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-119669504256,-119190727040⟩,⟨-1225936309717,-1225402597781⟩,⟨0,0⟩,⟨-1366897627561,-1365707727607⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-107375332530,-106899183313⟩,⟨-980799782110,-979363450628⟩,⟨0,0⟩,⟨1224334941456,1227003501238⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106899183313,107375332530⟩,⟨979363450628,980799782110⟩,⟨0,0⟩,⟨-1227003501238,-1224334941456⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨363517866748,365400070606⟩,⟨2373556453909,2387511037296⟩,⟨0,0⟩,⟨-12010399862327,-11805032411235⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2142906060864,-2128896242880⟩,⟨6833326156563,6948093226595⟩,⟨3025123910701,3066931775806⟩,⟨-43906765754805,-42468260618969⟩,⟨-27100824406581,-26423123202447⟩,⟨-8554771300118,-8323126780938⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309110340900,-303201394589⟩,⟨-955400331082,-906272280096⟩,⟨-420459096121,-402506309853⟩,⟨5918468352873,6458158502582⟩,⟨3643603755015,3900152507499⟩,⟨1167181747249,1251377815506⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨303201394589,309110340900⟩,⟨906272280096,955400331082⟩,⟨402506309853,420459096121⟩,⟨-6458158502582,-5918468352873⟩,⟨-3900152507499,-3643603755015⟩,⟨-1251377815506,-1167181747249⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158602572596,-156594507611⟩,⟨-989560464999,-985694994432⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940909055180,942917120165⟩,⟨-989560464999,-985694994432⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-171276311168,-168932260864⟩,⟨-1156363871370,-1149393816954⟩,⟨-510426240098,-508838395653⟩,⟨-1216155763367,-1201539040677⟩,⟨745293738061,752925580246⟩,⟨-236955153542,-235483196675⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146882817789,-144564086403⟩,⟨-840227228331,-829447148331⟩,⟨-370685386905,-367397182458⟩,⟨1017878615983,1053235770994⟩,⟨1378841489310,1395527478687⟩,⟨200682920265,204034429029⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144564086403,146882817789⟩,⟨829447148331,840227228331⟩,⟨367397182458,370685386905⟩,⟨-1053235770994,-1017878615983⟩,⟨-1395527478687,-1378841489310⟩,⟨-204034429029,-200682920265⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨447765480992,455993158689⟩,⟨1735719428427,1795627559413⟩,⟨769903492311,791144483026⟩,⟨-7511394273576,-6936346968856⟩,⟨-5295679986186,-5022445244325⟩,⟨-1455412244535,-1367864667514⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨811283347740,821393229295⟩,⟨4109275882336,4183138596709⟩,⟨769903492311,791144483026⟩,⟨-19521794135903,-18741379380091⟩,⟨-5295679986186,-5022445244325⟩,⟨-1455412244535,-1367864667514⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨86414741992,91289865424⟩,⟨-227633266688,-219902325554⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13242716636723,13989809976249⟩,⟨31899534209439,36851885127805⟩,⟨-141427800660550,-126601276394228⟩,⟨153681500660876,194150090641476⟩,⟨-426101420857614,-253920339044009⟩,⟨2420633715019065,2859484558208856⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9771243172702,10451126575949⟩,⟨73030184463891,80755128695281⟩,⟨-96381176363467,-83347500876674⟩,⟨103446859752080,199724926903642⟩,⟨-901431947192637,-694487032946868⟩,⟨1564039152760086,1942412820010935⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨79873696768,85384756992⟩,⟨-699924552004,-553597339117⟩,⟨631806629630,835359348412⟩,⟨5901884562029,10655064099034⟩,⟨-8388230062657,-898359881973⟩,⟨-6893392172520,4438473377043⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1179385324544,1184896384768⟩,⟨-699924552004,-553597339117⟩,⟨631806629630,835359348412⟩,⟨5901884562029,10655064099034⟩,⟨-8388230062657,-898359881973⟩,⟨-6893392172520,4438473377043⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨77105765120,82231622848⟩,⟨-652522265183,-513704589945⟩,⟨586278044826,778784760024⟩,⟨5089339683974,9693442713113⟩,⟨-7546222516588,-371441296595⟩,⟨-6978151929590,3825265135051⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨82707090605,88617482676⟩,⟨-755541991365,-589844786130⟩,⟨673174923353,901738714262⟩,⟨6390230599094,12073852437789⟩,⟨-9751102605125,-1051798855206⟩,⟨-7361825835646,5637644751403⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-85384756992,-79873696768⟩,⟨553597339117,699924552004⟩,⟨-835359348412,-631806629630⟩,⟨-10655064099034,-5901884562029⟩,⟨898359881973,8388230062657⟩,⟨-4438473377043,6893392172520⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1014126870784,1019637931008⟩,⟨553597339117,699924552004⟩,⟨-835359348412,-631806629630⟩,⟨-10655064099034,-5901884562029⟩,⟨898359881973,8388230062657⟩,⟨-4438473377043,6893392172520⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-88882419968,-82923530624⟩,⟨596963581830,758854937845⟩,⟨-905692713025,-681299424686⟩,⟨-12075913208506,-6688323320268⟩,⟨1338634669518,9719566003763⟩,⟨-5558211822051,7051624511500⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-82425582877,-76483939325⟩,⟨494024626491,661976658063⟩,⟨-792249018230,-560862911873⟩,⟨-10152415736988,-4341453052550⟩,⟨-596495675866,8259677906513⟩,⟨-4928702759448,8274368002363⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨281507728,12133543351⟩,⟨-261517364874,72131871933⟩,⟨-119074094877,340875802389⟩,⟨-3762185137894,7732399385239⟩,⟨-10347598280991,7207879051307⟩,⟨-12290528595094,13912012753766⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨140753864,6066771676⟩,⟨-130758682437,36065935967⟩,⟨-59537047439,170437901195⟩,⟨-1881092568947,3866199692620⟩,⟨-5173799140496,3603939525654⟩,⟨-6145264297547,6956006376883⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6066771676,-140753864⟩,⟨-36065935967,130758682437⟩,⟨-170437901195,59537047439⟩,⟨-3866199692620,1881092568947⟩,⟨-3603939525654,5173799140496⟩,⟨-6956006376883,6145264297547⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨756056611940,761982649016⟩,⟨-36065935967,130758682437⟩,⟨-170437901195,59537047439⟩,⟨-3866199692620,1881092568947⟩,⟨-3603939525654,5173799140496⟩,⟨-6956006376883,6145264297547⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨5802401060,6630722716⟩,⟨-108708059608,-80431829694⟩,⟨91794811216,129742975270⟩,⟨1414947022101,2545992969915⟩,⟨-2366351515218,-766743676286⟩,⟨-344536598745,1958693631777⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6630722716,-5802401060⟩,⟨80431829694,108708059608⟩,⟨-129742975270,-91794811216⟩,⟨-2545992969915,-1414947022101⟩,⟨766743676286,2366351515218⟩,⟨-1958693631777,344536598745⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092880905060,1093709226716⟩,⟨80431829694,108708059608⟩,⟨-129742975270,-91794811216⟩,⟨-2545992969915,-1414947022101⟩,⟨766743676286,2366351515218⟩,⟨-1958693631777,344536598745⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6650797120,-5817765504⟩,⟨80858540672,109367612719⟩,⟨-130530151338,-92281805653⟩,⟨-2572318724397,-1428400040612⟩,⟨777597885527,2393692371923⟩,⟨-1986073490294,338881775118⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3325398560,-2908882752⟩,⟨40429270336,54683806360⟩,⟨-65265075669,-46140902826⟩,⟨-1286159362199,-714200020306⟩,⟨388798942763,1196846185962⟩,⟨-993036745147,169440887559⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨2908882752,3325398560⟩,⟨-54683806360,-40429270336⟩,⟨46140902826,65265075669⟩,⟨714200020306,1286159362199⟩,⟨-1196846185962,-388798942763⟩,⟨-169440887559,993036745147⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765032266368,765448801440⟩,⟨-54683806360,-40429270336⟩,⟨46140902826,65265075669⟩,⟨714200020306,1286159362199⟩,⟨-1196846185962,-388798942763⟩,⟨-169440887559,993036745147⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273220226265,273427306679⟩,⟨20107957423,27177014902⟩,⟨-32435743818,-22948702804⟩,⟨-636498242479,-353736755525⟩,⟨191685919071,591587878805⟩,⟨-489673407945,86134149687⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530064532736,1530897602880⟩,⟨-109367612720,-80858540672⟩,⟨92281805652,130530151338⟩,⟨1428400040612,2572318724398⟩,⟨-2393692371924,-777597885526⟩,⟨-338881775118,1986073490294⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1185642258737,1192085383440⟩,⟨-822746987574,-643726934454⟩,⟨734669255290,981947819205⟩,⟨7561757506772,13660487858641⟩,⟨-11215623560725,-1842374898196⟩,⟨-7192583136948,6835040090257⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1271772889698,1284659139104⟩,⟨-1645493975149,-1287453868908⟩,⟨1469338510580,1963895638410⟩,⟨15123515013545,27320975717274⟩,⟨-22431247121445,-3684749796392⟩,⟨-14380602801921,13670080180512⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨160029295808,171114042816⟩,⟨-1422612302690,-1101903575820⟩,⟨1257574658012,1697886554795⟩,⟨11103226540416,22516056906099⟩,⟨-18132630863935,-956871968425⟩,⟨-15054662785875,10380111428989⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨54923508797,59173274457⟩,⟨-487861912394,-370515527053⟩,⟨421213172578,583543519963⟩,⟨3591596305650,7576161322183⟩,⟨-6158376638576,-8115591236⟩,⟨-5576417543692,3643637008677⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380209328645,380704667220⟩,⟨784330672,17747004849⟩,⟨-22230366666,525243639⟩,⟨-536684112229,144473521681⟩,⟨-325142386684,636918989646⟩,⟨-773768135851,609974261476⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175495137589,3179632188203⟩,⟨-148415474348,-6542179410⟩,⟨-4392531839,185909140259⟩,⟨-1208182903892,4502061915543⟩,⟨-5343810970723,2719525874609⟩,⟨-5101634664948,6492643766699⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨158624366235,171120744331⟩,⟨-1418815072288,-1070411211918⟩,⟨1216267683882,1697530580599⟩,⟨10312262406215,22283184682849⟩,⟨-18258004508725,122362987262⟩,⟨-16405432335864,11083637814115⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨318653662043,342234787147⟩,⟨-2841427374978,-2172314787738⟩,⟨2473842341894,3395417135394⟩,⟨21415488946631,44799241588948⟩,⟨-36390635372660,-834508981163⟩,⟨-31460095121739,21463749243104⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519886817035,528068592213⟩,⟨-49988770894,181236550316⟩,⟨-236233469778,82520631846⟩,⟨-5367279332270,2638367244371⟩,⟨-5035736871014,7185244904452⟩,⟨-9659749657729,8570412040195⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357489503112,365961663881⟩,⟨-51964765681,188400608807⟩,⟨-245571489024,85782571186⟩,⟨-5588358621159,2774988817426⟩,⟨-5276934231888,7483989386699⟩,⟨-10060775288811,8964118578199⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714979006224,731923327762⟩,⟨-103929531362,376801217614⟩,⟨-491142978048,171565142372⟩,⟨-11176717242318,5549977634852⟩,⟨-10553868463776,14967978773398⟩,⟨-20121550577622,17928237156398⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523433810020,1525095201820⟩,⟨-28935783026,27849518936⟩,⟨-37461169618,38735340122⟩,⟨-1117592929303,1157371702297⟩,⟨-1626948695638,1588753629692⟩,⟨-2297575406895,2330610089039⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨990642721750,1015225966758⟩,⟨-163419103240,541187038471⟩,⟨-706184894769,263757533026⟩,⟨-16266636749434,8487712943147⟩,⟨-15747218065507,21845376597287⟩,⟨-29473975207399,26452556937525⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67893135601,67996090400⟩,⟨9993347114,13516797460⟩,⟨-16132286096,-11405154096⟩,⟨-315834168207,-174458266415⟩,⟨93661516960,293393584486⟩,⟨-242586680774,44753516777⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50095486893,50796669051⟩,⟨261115074683,268791769571⟩,⟨35488675740,40510640421⟩,⟨-1368515664237,-1183126026900⟩,⟨-312765388860,-123847018700⟩,⟨-294446488572,-67002585296⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2129215749243,2131534957247⟩,⟨-304554516600,-225043159390⟩,⟨256836061170,363485552566⟩,⟨3987374555978,7184858702635⟩,⟨-6691650351516,-2177760902684⟩,⟨-928189120776,5561584231772⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2962985945905,2967828328569⟩,⟨-636066642176,-469750225217⟩,⟨536114040992,759144988167⟩,⟨8347984087266,15051125090376⟩,⟨-14029844846286,-4574142768079⟩,⟨-1906208362099,11680179058413⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134998320952,137111595365⟩,⟨674272296084,704126670799⟩,⟨120061796560,144419266668⟩,⟨-3624574842996,-2716075414498⟩,⟨-1388510441687,-371728468622⟩,⟨-848234513454,414996403200⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8817093962012,8955117449531⟩,⟨-46708262679759,-43359733177398⟩,⟨-9580056150824,-7720690133459⟩,⟨601119297112366,727679868385783⟩,⟨99840277746269,192042537932896⟩,⟨-14007550384584,76764873722332⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7944063291191,8268641768274⟩,⟨-44458718910079,-34658669935687⟩,⟨-14597290320179,-4808012637250⟩,⟨363133041250177,754911533438760⟩,⟨-54220800981190,386666868635105⟩,⟨-257584690663051,298632611923727⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15888126582382,16537283536548⟩,⟨-88917437820158,-69317339871374⟩,⟨-29194580640358,-9616025274500⟩,⟨726266082500354,1509823066877520⟩,⟨-108441601962380,773333737270210⟩,⟨-515169381326102,597265223847454⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10661930935953,10702470597440⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710694,2028067813858452⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9562419308177,9602958969664⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710699,2028067813858436⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2378215779456,2382867339072⟩,⟨-11978441145317,-11837681660582⟩,⟨0,0⟩,⟨99082204851667,105744330752101⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7622359460045,7720103585100⟩,⟨-48785295283087,-47372003130528⟩,⟨-21534134246077,-20971658030740⟩,⟨588822054998052,616573342474680⟩,⟨313514394723900,326365210599889⟩,⟨115400078640674,120132827912575⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6522847832269,6620591957324⟩,⟨-48785295283088,-47372003130527⟩,⟨-21534134246078,-20971658030740⟩,⟨588822054998053,616573342474680⟩,⟨313514394723899,326365210599891⟩,⟨115400078640672,120132827912576⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1957619931776,1973973799360⟩,⟨-8223401926232,-7867282655174⟩,⟨-3629861006506,-3482858029475⟩,⟨36284361573065,47639141549551⟩,⟨24918512043839,30092413948698⟩,⟨7181609615462,9217521503097⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101308883270,101738380002⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134006031842,136014096828⟩,⟨700767950927,708240878866⟩,⟨310415931144,312440113859⟩,⟨-1781208837000,-1767320322048⟩,⟨-1572559325762,-1564701884412⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4335835711232,4356841138432⟩,⟨-20201843071549,-19704964315756⟩,⟨-3629861006506,-3482858029475⟩,⟨135366566424732,153383472301652⟩,⟨24918512043839,30092413948698⟩,⟨7181609615462,9217521503097⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨637307324086,684469574294⟩,⟨-5682854749956,-4344629575476⟩,⟨4947684683788,6790834270788⟩,⟨42830977893262,89598483177896⟩,⟨-72781270745320,-1669017962326⟩,⟨-62920190243478,42927498486208⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4973143035318,5041310712726⟩,⟨-25884697821505,-24049593891232⟩,⟨1317823677282,3307976241313⟩,⟨178197544317994,242981955479548⟩,⟨-47862758701481,28423395986372⟩,⟨-55738580628016,52145019989305⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458224865042,466475089524⟩,⟨1552307797483,1789551904580⟩,⟨121424132059,306088753747⟩,⟨-34795921466640,-25641770270087⟩,⟨-3382743291556,5258322039952⟩,⟨-5157519714617,4825005688767⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨225915279768,226774273230⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-226774273230,-225915279768⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨872737354546,873596348008⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1887708774940,1893262565501⟩,⟨-14282980494402,-14152591376986⟩,⟨0,0⟩,⟨125997226743230,131930939874303⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨788197147164,793750937725⟩,⟨-14282980494402,-14152591376986⟩,⟨0,0⟩,⟨125997226743230,131930939874303⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨30973684766,32951637098⟩,⟨-675106769486,-634972328959⟩,⟨312815742780,315329962371⟩,⟨7781815544854,8433981184840⟩,⟨-6467888110707,-6405006849897⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨489198549808,499426726622⟩,⟨877201027997,1154579575621⟩,⟨434239874839,621418716118⟩,⟨-27014105921786,-17207789085247⟩,⟨-9850631402263,-1146684809945⟩,⟨-5157519714617,4825005688767⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507340798957,508333108400⟩,⟨2520383226112,2560338836291⟩,⟨0,0⟩,⟨2439291441574,4695713285828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225727838467,230898095071⟩,⟨1526139103192,1696764837674⟩,⟨200368599543,287298196402⟩,⟨-7382460429934,-430026278257⟩,⟨-3558808369929,917937072560⟩,⟨-2384456846054,2230726877150⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-684469574294,-637307324086⟩,⟨4344629575476,5682854749956⟩,⟨-6790834270788,-4947684683788⟩,⟨-89598483177896,-42830977893262⟩,⟨1669017962326,72781270745320⟩,⟨-42927498486208,62920190243478⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3651366136938,3719533814346⟩,⟨-15857213496073,-14022109565800⟩,⟨-10420695277294,-8430542713263⟩,⟨45768083246836,110552494408390⟩,⟨26587530006165,102873684694018⟩,⟨-35745888870746,72137711746575⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨445020384007,460121584529⟩,⟨365576664979,686921918421⟩,⟨-258223041889,29456708197⟩,⟨-20876105667741,-10067129436908⟩,⟨-13297804040501,-1802226055557⟩,⟨-11518290822346,3013229720520⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨313189015222,317205145192⟩,⟨1971389988864,1979120929998⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-317205145192,-313189015222⟩,⟨-1979120929998,-1971389988864⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨782306482584,786322612554⟩,⟨-1979120929998,-1971389988864⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1392853630990,1411699699953⟩,⟨-9434170122676,-9107551301864⟩,⟨-4164301655718,-4031926850841⟩,⟨54028037818149,63673676758351⟩,⟨34134162131188,38536225135212⟩,⟨10638778224682,12360044118131⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1411699699953,-1392853630990⟩,⟨9107551301864,9434170122676⟩,⟨4031926850841,4164301655718⟩,⟨-63673676758351,-54028037818149⟩,⟨-38536225135212,-34134162131188⟩,⟨-12360044118131,-10638778224682⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-312188072177,-293342003214⟩,⟨9107551301864,9434170122676⟩,⟨4031926850841,4164301655718⟩,⟨-63673676758351,-54028037818149⟩,⟨-38536225135212,-34134162131188⟩,⟨-12360044118131,-10638778224682⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12960120829,-11527424032⟩,⟨387232505371,423964825849⟩,⟨34420535848,56455980428⟩,⟨-4596505873157,-3944643308910⟩,⟨1877045051773,2315500974801⟩,⟨2687229235958,2890597061870⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨432060263178,448594160497⟩,⟨752809170350,1110886744270⟩,⟨-223802506041,85912688625⟩,⟨-25472611540898,-14011772745818⟩,⟨-11420758988728,513274919244⟩,⟨-8831061586388,5903826782390⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101738380002,-101308883270⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨3981122522,4223549249⟩,⟨23764338735,26135437118⟩,⟨40206963047,40417161119⟩,⟨-272151609348,-260962212900⟩,⟨244629257582,245740915920⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8611067097,9153297979⟩,⟨5388928242,13778861498⟩,⟨86966641867,87592282552⟩,⟨-800506654358,-669967828310⟩,⟨88809042402,99690417602⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1471799104860,1490140063866⟩,⟨-7683459093579,-7363134184137⟩,⟨-1453149622445,-1379538119377⟩,⟨107254164870077,115091917517776⟩,⟨22802520391256,24712398588687⟩,⟨5037105587703,5507410846146⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11526718340,12405231278⟩,⟨-56750260075,-38991864995⟩,⟨104315690031,107907430182⟩,⟨-437496841437,-10865039698⟩,⟨-332849017566,-248318112635⟩,⟨-192080306487,-172382554020⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12405231278,-11526718340⟩,⟨38991864995,56750260075⟩,⟨-107907430182,-104315690031⟩,⟨10865039698,437496841437⟩,⟨248318112635,332849017566⟩,⟨172382554020,192080306487⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114143611280,-112835601610⟩,⟨-834604483013,-815987094471⟩,⟨-107907430182,-104315690031⟩,⟨2209888295250,2636520096989⟩,⟨248318112635,332849017566⟩,⟨172382554020,192080306487⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨76928345753,81947201804⟩,⟨-545721995641,-504921616253⟩,⟨626240997767,647326498517⟩,⟨2999318552159,3680184139962⟩,⟨-3913343249340,-3454949214416⟩,⟨-2601823187485,-2381863991215⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨102975782663,111060952377⟩,⟨-1312255501337,-1191053265909⟩,⟨729978086908,780784434406⟩,⟨18281653924273,21192605054375⟩,⟨-7598298399381,-6255468209150⟩,⟨-4884813537829,-4349344670857⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-111060952377,-102975782663⟩,⟨1191053265909,1312255501337⟩,⟨-780784434406,-729978086908⟩,⟨-21192605054375,-18281653924273⟩,⟨6255468209150,7598298399381⟩,⟨4349344670857,4884813537829⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨988450675399,996535845113⟩,⟨1191053265909,1312255501337⟩,⟨-780784434406,-729978086908⟩,⟨-21192605054375,-18281653924273⟩,⟨6255468209150,7598298399381⟩,⟨4349344670857,4884813537829⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120470169969,123275570268⟩,⟨775146760377,804241307913⟩,⟨182474784314,194210139083⟩,⟨-2717777148442,-2126375770554⟩,⟨-829552673275,-559065420162⟩,⟨-228197586374,-119287032165⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11579571028,11849591826⟩,⟨167478710336,173285606584⟩,⟨21410457778,22404390194⟩,⟨663736524548,813471283947⟩,⟨85724728594,112851742146⟩,⟨-20087057514,-14200624175⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167326734538,178224636165⟩,⟨1461819561236,1876294980658⟩,⟨-5249422208,235703105708⟩,⟨-10787375404302,7389676259018⟩,⟨-6342929708149,7217163237565⟩,⟨-7043950798039,5857110221544⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178224636165,-167326734538⟩,⟨-1876294980658,-1461819561236⟩,⟨-235703105708,5249422208⟩,⟨-7389676259018,10787375404302⟩,⟨-7217163237565,6342929708149⟩,⟨-5857110221544,7043950798039⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47503202302,63571360533⟩,⟨-350155877466,234945276438⟩,⟨-35334506165,292547618610⟩,⟨-14772136688952,10357349126045⟩,⟨-10775971607494,7260866780709⟩,⟨-8241567067598,9274677675189⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28287934834453,29689694578095⟩,⟨-283319806705829,-237099255932367⟩,⟨-107008761852030,-67448683678400⟩,⟨2809357920209606,4757185548278412⟩,⟨453766947584344,2352884647113211⟩,⟨-760197541837135,1403680661933473⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13199552861,13821469316⟩,⟨169860981210,180340622804⟩,⟨39986422564,43549090420⟩,⟨483518255871,710568621539⟩,⟨71270113122,161601037828⟩,⟨9396643355,42468034887⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339594490629,373215882622⟩,⟨808650249732,2023310889028⟩,⟨-316399566808,366223255794⟩,⟨-46773620398612,5729848383139⟩,⟨-21492034203255,14898030515291⟩,⟨-17791084114803,13885918678720⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-373215882622,-339594490629⟩,⟨-2023310889028,-808650249732⟩,⟨-366223255794,316399566808⟩,⟨-5729848383139,46773620398612⟩,⟨-14898030515291,21492034203255⟩,⟨-13885918678720,17791084114803⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58844380556,108999669868⟩,⟨-1270501718678,302236494538⟩,⟨-590025761835,402312255433⟩,⟨-31202459924037,32761847652794⟩,⟨-26318789504019,22005309122499⟩,⟨-22716980265108,23694910897193⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235314915112,237752476830⟩,⟨1573505305473,1581837226874⟩,⟨310415931144,312440113859⟩,⟨-3980232092552,-3966343577600⟩,⟨-1572559325762,-1564701884412⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1716785176198,-1630493280917⟩,⟨-5439348779028,-2560362907377⟩,⟨-636160413411,1523398146997⟩,⟨-21920243637567,100111714792836⟩,⟨-62981014004023,47151038174885⟩,⟨-57688311316555,62100666072996⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-192483341038,-178648226833⟩,⟨-1865599531933,-1430015744656⟩,⟨-374566412203,-99795337923⟩,⟨-7261666797353,11857859341185⟩,⟨-7658373917419,7271149025672⟩,⟨-6515765904294,7857106529371⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨42831574074,59104249997⟩,⟨-292094226460,151821482218⟩,⟨-64150481059,212644775936⟩,⟨-11241898889905,7891515763585⟩,⟨-9230933243181,5706447141260⟩,⟨-6862815703484,7510738891787⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2542307369,6302122812⟩,⟨-108170204715,40765865133⟩,⟨-37616873612,52262413453⟩,⟨-3811453649823,3730210803553⟩,⟨-3056132170180,2260420912553⟩,⟨-2444447723342,2503516509661⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1668507809,3177149091⟩,⟨-31403051588,16322328230⟩,⟨-6896818506,22861440808⟩,⟨-1289281828283,1003611319317⟩,⟨-1105399310198,672224493430⟩,⟨-762634662704,889730272057⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨2970686312,5703995214⟩,⟨-80140830515,17365187638⟩,⟨-22870834644,35758338846⟩,⟨-2503764280125,2409195925959⟩,⟨-2171599720336,1449066663532⟩,⟨-1509220943282,1669521835295⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5703995214,-2970686312⟩,⟨-17365187638,80140830515⟩,⟨-35758338846,22870834644⟩,⟨-2409195925959,2503764280125⟩,⟨-1449066663532,2171599720336⟩,⟨-1669521835295,1509220943282⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3161687845,3331436500⟩,⟨-125535392353,120906695648⟩,⟨-73375212458,75133248097⟩,⟨-6220649575782,6233975083678⟩,⟨-4505198833712,4432020632889⟩,⟨-4113969558637,4012737452943⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47503202302,63571360533⟩,⟨-350155877466,234945276438⟩,⟨-35334506165,292547618610⟩,⟨-14772136688952,10357349126045⟩,⟨-10775971607494,7260866780709⟩,⟨-8241567067598,9274677675189⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3161687845,3331436500⟩,⟨-125535392353,120906695648⟩,⟨-73375212458,75133248097⟩,⟨-6220649575782,6233975083678⟩,⟨-4505198833712,4432020632889⟩,⟨-4113969558637,4012737452943⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (527/5120) u, BivariateJet2.affineZ (521/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000042

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000043Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2499969724352,-2499969666496⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2499969724352,-2499969666496⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-119430089600,-119430089536⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-119430089600,-119430089536⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2125225050432,-2125225011392⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2125225050368,-2125225011392⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-171896354496,-171896354432⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-171896354496,-171896354432⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨82023712704,82023712768⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-88639549568,-88639549504⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨82023836480,82023836544⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-88639694144,-88639694080⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6615857600,-6615857536⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6615836800,-6615836736⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨170663262272,170663262336⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨170663530624,170663530688⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1953328656896,1953328695488⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1953328656960,1953328695552⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2497885341504,-2497885283648⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-119669504256,-119669504192⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2132186901504,-2132186862400⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2118301819264,-2118301780288⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-173072244352,-173072244288⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-170722602688,-170722602624⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨79472640192,79472640256⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-85667595904,-85667595840⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨84597263040,84597263104⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-91652874944,-91652874880⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7055611904,-7055611840⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6194955648,-6194955584⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨165140236096,165140236160⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨176250137920,176250137984⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2378215779456,2378215837312⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1945229536000,1945229574592⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1961464259712,1961464298368⟩



end LaneCBRB2Cell000043Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000043
open Set LaneCBRB2Cell000043Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨113172388249,113172388250⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨115749368627,115749368628⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113172388250,-113172388249⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436583425638,436583425639⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨45960637972,45960637973⟩,⟨-115749368628,-115749368627⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159133026221,159133026223⟩,⟨983762259148,983762259149⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨45960637971,45960637974⟩,⟨-115749368628,-115749368627⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2499969724352,-2499969666496⟩,⟨10682162303971,10682162304067⟩,⟨0,0⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-257321102488,-257321096530⟩,⟨-1400458096586,-1400458038710⟩,⟨0,0⟩,⟨10682162303779,10682162304259⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨257321096530,257321102488⟩,⟨1400458038710,1400458096586⟩,⟨0,0⟩,⟨-10682162304259,-10682162303779⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986339239526,986339239527⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-119430089600,-119430089536⟩,⟨-1225669395649,-1225669395647⟩,⟨0,0⟩,⟨-1366302483285,-1366302483280⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-107137187800,-107137187741⟩,⟨-980081538242,-980081538174⟩,⟨0,0⟩,⟨1225669395643,1225669395653⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨107137187741,107137187800⟩,⟨980081538174,980081538242⟩,⟨0,0⟩,⟨-1225669395653,-1225669395643⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨364458284271,364458290288⟩,⟨2380539576884,2380539634828⟩,⟨0,0⟩,⟨-11907831699912,-11907831699422⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2125225050432,-2125225011392⟩,⟨6797193948819,6797193948914⟩,⟨3016523749824,3016523749871⟩,⟨-42020333766360,-42020333765199⟩,⟨-26245136774839,-26245136774203⟩,⟨-8275870216979,-8275870216728⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-307585190677,-307585185022⟩,⟨-917733044778,-917733009818⟩,⟨-407280349278,-407280333760⟩,⟨6081629976299,6081629976728⟩,⟨3724677308901,3724677348172⟩,⟨1197772027968,1197772028064⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307585185022,307585190677⟩,⟨917733009818,917733044778⟩,⟨407280333760,407280349278⟩,⟨-6081629976728,-6081629976299⟩,⟨-3724677348172,-3724677308901⟩,⟨-1197772028064,-1197772027968⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159133026223,-159133026221⟩,⟨-983762259149,-983762259148⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940378601553,940378601555⟩,⟨-983762259149,-983762259148⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-171896354496,-171896354432⟩,⟨-1150236767527,-1150236767522⟩,⟨-510463075396,-510463075392⟩,⟨-1203302073347,-1203302073337⟩,⟨751560605676,751560605685⟩,⟨-236989354874,-236989354870⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147017684370,-147017684314⟩,⟨-829962024845,-829962024780⟩,⟨-368328486470,-368328486438⟩,⟨1029147389055,1029147389079⟩,⟨1384340146000,1384340146084⟩,⟨202689732861,202689732871⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147017684314,147017684370⟩,⟨829962024780,829962024845⟩,⟨368328486438,368328486470⟩,⟨-1029147389079,-1029147389055⟩,⟨-1384340146084,-1384340146000⟩,⟨-202689732871,-202689732861⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨454602869336,454602875047⟩,⟨1747695034598,1747695069623⟩,⟨775608820198,775608835748⟩,⟨-7110777365807,-7110777365354⟩,⟨-5109017494256,-5109017454901⟩,⟨-1400461760935,-1400461760829⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨819061153607,819061165335⟩,⟨4128234611482,4128234704451⟩,⟨775608820198,775608835748⟩,⟨-19018609065719,-19018609064776⟩,⟨-5109017494256,-5109017454901⟩,⟨-1400461760935,-1400461760829⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨91921275942,91921275948⟩,⟨-231498737256,-231498737254⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13151751943679,13151751944539⟩,⟨33121972429556,33121972434176⟩,⟨-124929443336373,-124929443319747⟩,⟨166831774553291,166831774588904⟩,⟨-314628012797287,-314628012625810⟩,⟨2373427642951136,2373427643427629⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9797157980704,9797158121629⟩,⟨74053276442474,74053277914488⟩,⟨-83786508762541,-83786507230980⟩,⟨145508186442306,145508193910451⟩,⟨-741184055372096,-741184040316116⟩,⟨1575036637729799,1575036666960535⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨85160722432,85160855808⟩,⟨-638143391696,-638141355246⟩,⟨722015795172,722018098130⟩,⟨8268315407175,8268365895997⟩,⟨-4386794673082,-4386721752260⟩,⟨-1382826521407,-1382723805012⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1184672350208,1184672483584⟩,⟨-638143391696,-638141355246⟩,⟨722015795172,722018098130⟩,⟨8268315407175,8268365895997⟩,⟨-4386794673082,-4386721752260⟩,⟨-1382826521407,-1382723805012⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨82023712704,82023836544⟩,⟨-592270157429,-592268200688⟩,⟨670113278758,670115491613⟩,⟨7354906713401,7354956544842⟩,⟨-3710481470443,-3710410948634⟩,⟨-1691834330325,-1691736155943⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨88376713849,88376857231⟩,⟨-685749116753,-685746712815⟩,⟨775878187598,775880906259⟩,⟨9228873944940,9228937691201⟩,⟨-5102980661279,-5102893242313⟩,⟨-1045945801566,-1045826286243⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-85160855808,-85160722432⟩,⟨638141355246,638143391696⟩,⟨-722018098130,-722015795172⟩,⟨-8268365895997,-8268315407175⟩,⟨4386721752260,4386794673082⟩,⟨1382723805012,1382826521407⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1014350771968,1014350905344⟩,⟨638141355246,638143391696⟩,⟨-722018098130,-722015795172⟩,⟨-8268365895997,-8268315407175⟩,⟨4386721752260,4386794673082⟩,⟨1382723805012,1382826521407⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-88639694144,-88639549504⟩,⟨691717074003,691719372380⟩,⟨-782635865519,-782633266305⟩,⟨-9397716110826,-9397657312807⟩,⟨5247377608286,5247460547677⟩,⟨941728905773,941844143160⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-81774263895,-81774119704⟩,⟨586695853542,586698305933⟩,⟨-663811300843,-663808527369⟩,⟨-7200338177639,-7200272405551⟩,⟨3578833983106,3578923507061⟩,⟨1785171919292,1785293500184⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6602449954,6602737527⟩,⟨-99053263211,-99048406882⟩,⟨112066886755,112072378890⟩,⟨2028535767301,2028665285650⟩,⟨-1524146678173,-1523969735252⟩,⟨739226117726,739467213941⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3301224977,3301368764⟩,⟨-49526631606,-49524203441⟩,⟨56033443377,56036189445⟩,⟨1014267883650,1014332642825⟩,⟨-762073339087,-761984867626⟩,⟨369613058863,369733606971⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3301368764,-3301224977⟩,⟨49524203441,49526631606⟩,⟨-56036189445,-56033443377⟩,⟨-1014332642825,-1014267883650⟩,⟨761984867626,762073339087⟩,⟨-369733606971,-369613058863⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758822014852,758822177903⟩,⟨49524203441,49526631606⟩,⟨-56036189445,-56033443377⟩,⟨-1014332642825,-1014267883650⟩,⟨761984867626,762073339087⟩,⟨-369733606971,-369613058863⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6595972668,6595993329⟩,⟨-98852683306,-98852213024⟩,⟨111844904902,111845436816⟩,⟨2021552250235,2021566804985⟩,⟨-1517645190000,-1517627482044⟩,⟨734042475379,734064771439⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6595993329,-6595972668⟩,⟨98852213024,98852683306⟩,⟨-111845436816,-111844904902⟩,⟨-2021566804985,-2021552250235⟩,⟨1517627482044,1517645190000⟩,⟨-734064771439,-734042475379⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092915634447,1092915655108⟩,⟨98852213024,98852683306⟩,⟨-111845436816,-111844904902⟩,⟨-2021566804985,-2021552250235⟩,⟨1517627482044,1517645190000⟩,⟨-734064771439,-734042475379⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6615857600,-6615836736⟩,⟨99448806633,99449281634⟩,⟨-112520449354,-112519912101⟩,⟨-2042762466182,-2042747699214⟩,⟨1536963897999,1536981838896⟩,⟨-750009995934,-749987441388⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3307928800,-3307918368⟩,⟨49724403316,49724640817⟩,⟨-56260224677,-56259956050⟩,⟨-1021381233091,-1021373849607⟩,⟨768481948999,768490919448⟩,⟨-375004997967,-374993720694⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3307918368,3307928800⟩,⟨-49724640817,-49724403316⟩,⟨56259956050,56260224677⟩,⟨1021373849607,1021381233091⟩,⟨-768490919448,-768481948999⟩,⟨374993720694,375004997967⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765431301984,765431331680⟩,⟨-49724640817,-49724403316⟩,⟨56259956050,56260224677⟩,⟨1021373849607,1021381233091⟩,⟨-768490919448,-768481948999⟩,⟨374993720694,375004997967⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273228908611,273228913777⟩,⟨24713053256,24713170827⟩,⟨-27961359204,-27961226225⟩,⟨-505391701247,-505388062558⟩,⟨379406870511,379411297500⟩,⟨-183516192860,-183510618844⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530862603968,1530862663360⟩,⟨-99449281634,-99448806632⟩,⟨112519912100,112520449354⟩,⟨2042747699214,2042762466182⟩,⟨-1536981838896,-1536963897998⟩,⟨749987441388,750009995934⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1191822093563,1191822250275⟩,⟨-749793379281,-749790789352⟩,⟨848339930544,848342859526⟩,⟨10658349041527,10658417312136⟩,⟨-6221721767831,-6221627501269⟩,⟨-417068661255,-416939365663⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1284132559350,1284132872774⟩,⟨-1499586758562,-1499581578703⟩,⟨1696679861087,1696685719052⟩,⟨21316698083061,21316834624267⟩,⟨-12443443535659,-12443255002539⟩,⟨-834137176010,-833878877826⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨170663262272,170663530688⟩,⟨-1283989776518,-1283985027982⟩,⟨1452746265927,1452751636268⟩,⟨16752552112991,16752684568896⟩,⟨-8957953574258,-8957777000804⟩,⟨-2633689531623,-2633454003622⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨58773212897,58773317575⟩,⟨-436575502462,-436573808305⟩,⟨493955113231,493957029167⟩,⟨5570280459706,5570324671305⟩,⟨-2903463056473,-2903401739375⟩,⟨-1056582322132,-1056498004952⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380419731769,380419753721⟩,⟨9695095161,9695378698⟩,⟨-10969695762,-10969375065⟩,⟨-200509908208,-200501092903⟩,⟨151370234175,151380932176⟩,⟨-74862589004,-74849155445⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177873409016,3177873592395⟩,⟨-80991298189,-80988920287⟩,⟨91633741391,91636430941⟩,⟨1679033425434,1679107500424⟩,⟨-1269246377706,-1269156591012⟩,⟨630544203304,630656803934⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨169869809203,169870121553⟩,⟨-1266145670935,-1266140566748⟩,⟨1432556408849,1432562181277⟩,⟨16253619492412,16253754461811⟩,⟨-8532378011318,-8532192965969⟩,⟨-2937758873291,-2937506183674⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨340533071475,340533652241⟩,⟨-2550135447453,-2550125594730⟩,⟨2885302674776,2885313817545⟩,⟨33006171605403,33006439030707⟩,⟨-17490331585576,-17489969966773⟩,⟨-5571448404914,-5570960187296⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523696917502,523697142560⟩,⟨68357723354,68361089616⟩,⟨-77346163956,-77342356966⟩,⟨-1395611358786,-1395521234065⟩,⟨1046711274878,1046834111984⟩,⟨-504628249674,-504461188963⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361426600748,361426833733⟩,⟨70765070676,70768570695⟩,⟨-80070073527,-80066115260⟩,⟨-1440142326682,-1440048263053⟩,⟨1078347208924,1078475119012⟩,⟨-516487510841,-516313872891⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722853201496,722853667466⟩,⟨141530141352,141537141390⟩,⟨-160140147054,-160132230520⟩,⟨-2880284653364,-2880096526106⟩,⟨2156694417848,2156950238024⟩,⟨-1032975021682,-1032627745782⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524266610639,1524266690692⟩,⟨-597068610,-596123326⟩,⟨674475284,675544452⟩,⟨21180894229,21210215947⟩,⟨-19354356852,-19318707998⟩,⟨15922669949,15967520555⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002100361287,1002101059897⟩,⟨195812459084,195822795343⟩,⟨-221560863228,-221549173587⟩,⟨-3979203297058,-3978922747239⟩,⟨2977301701124,2977680233619⟩,⟨-1421754885537,-1421243563330⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67897450663,67897453231⟩,⟨12282399564,12282458232⟩,⟨-13896809476,-13896743120⟩,⟨-250069007167,-250067183414⟩,⟨187308453498,187310669242⟩,⟨-89785498612,-89782713068⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50578968754,50578971393⟩,⟨264077827718,264077886938⟩,⟨37543508950,37543561303⟩,⟨-1268497433557,-1268495585209⟩,⟨-219474852290,-219472893472⟩,⟨-172971866484,-172969693195⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131437497362,2131437662747⟩,⟨-276928753286,-276927419840⟩,⟨313325518864,313327027072⟩,⟨5706271853721,5706313366698⟩,⟨-4300269555254,-4300219236162⟩,⟨2111461905015,2111525011870⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2967624784475,2967625129876⟩,⟨-578356624124,-578353816826⟩,⟨654370050640,654373225870⟩,⟨11954932629617,11955020150830⟩,⟨-9023481996723,-9023376150856⟩,⟨4457815652947,4457948081796⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136514610173,136514633186⟩,⟨686151200551,686151573876⟩,⟨131433271236,131433571969⟩,⟨-3151598400537,-3151587547700⟩,⟨-870046706666,-870035538825⟩,⟨-217104792150,-217092490261⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8855650060367,8855651553212⟩,⟨-44510395211427,-44510355987267⟩,⟨-8526046510894,-8526024127900⟩,⟨651879016742620,651880502858771⟩,⟨142146033737260,142147063302911⟩,⟨30500038793246,30500924992114⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8071083470827,8071090458136⟩,⟨-38989917450362,-38989769904327⟩,⟨-9555175027231,-9555054758820⟩,⟨546222018156920,546226902636627⟩,⟨160982537706300,160987184442894⟩,⟨19782784177207,19787921760135⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16142166941654,16142180916272⟩,⟨-77979834900724,-77979539808654⟩,⟨-19110350054462,-19110109517640⟩,⟨1092444036313840,1092453805273254⟩,⟨321965075412600,321974368885788⟩,⟨39565568354414,39575843520270⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10682162303971,10682162304067⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848532,2016544728902914⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9582650676195,9582650676291⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848550,2016544728902902⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2380539576896,2380539634752⟩,⟨-11907831699843,-11907831699439⟩,⟨0,0⟩,⟨102414856889766,102414856913318⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7596951106305,7596951106402⟩,⟨-46964442017838,-46964442016589⟩,⟨-20842329321628,-20842329321047⟩,⟨580669477285185,580669477308629⟩,⟨310185328628202,310185328640276⟩,⟨114362376550364,114362376555274⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6497439478529,6497439478626⟩,⟨-46964442017839,-46964442016589⟩,⟨-20842329321629,-20842329321046⟩,⟨580669477285194,580669477308623⟩,⟨310185328628207,310185328640273⟩,⟨114362376550365,114362376555274⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1953328656896,1953328695552⟩,⟨-7947430716565,-7947430716224⟩,⟨-3526986825321,-3526986825165⟩,⟨40817031685821,40817031698112⟩,⟨26996697377039,26996697382954⟩,⟨8038880860631,8038880863135⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101523589692,101523589694⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136101600818,136101600821⟩,⟨699001168082,699001168089⟩,⟨310209424734,310209424739⟩,⟨-1760396448892,-1760396448888⟩,⟨-1562491150668,-1562491150660⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4333868233792,4333868330304⟩,⟨-19855262416408,-19855262415663⟩,⟨-3526986825321,-3526986825165⟩,⟨143231888575587,143231888611430⟩,⟨26996697377039,26996697382954⟩,⟨8038880860631,8038880863135⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨681066142950,681067304482⟩,⟨-5100270894906,-5100251189460⟩,⟨5770605349552,5770627635090⟩,⟨66012343210806,66012878061414⟩,⟨-34980663171152,-34979939933546⟩,⟨-11142896809828,-11141920374592⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5014934376742,5014935634786⟩,⟨-24955533311314,-24955513605123⟩,⟨2243618524231,2243640809925⟩,⟨209244231786393,209244766672844⟩,⟨-7983965794113,-7983242550592⟩,⟨-3104015949197,-3103039511457⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463054802818,463054918990⟩,⟨1678289786107,1678292604802⟩,⟨207164890961,207166948720⟩,⟨-30345675840634,-30345592636270⟩,⟨1044547802715,1044632281522⟩,⟨-286609830828,-286519671280⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨226344776498,226344776500⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-226344776500,-226344776498⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨873166851276,873166851278⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1890483187431,1890483233382⟩,⟨-14217572178026,-14217572061970⟩,⟨0,0⟩,⟨128963125257405,128963125277912⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨790971559655,790971605606⟩,⟨-14217572178026,-14217572061970⟩,⟨0,0⟩,⟨128963125257405,128963125277912⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33063367935,33063369859⟩,⟨-677576419272,-677576409542⟩,⟨314071324370,314071342618⟩,⟨8384247385699,8384247411372⟩,⟨-6436347433334,-6436347341287⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨496118170753,496118288849⟩,⟨1000713366835,1000716195260⟩,⟨521236215331,521238291338⟩,⟨-21961428454935,-21961345224898⟩,⟨-5391799630619,-5391715059765⟩,⟨-286609830828,-286519671280⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507836879489,507836891833⟩,⟨2540279524621,2540279648204⟩,⟨0,0⟩,⟨3565745386739,3565748309078⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229144555935,229144616052⟩,⟨1608421357043,1608423003266⟩,⟨240745951551,240746916259⟩,⟨-3910471729394,-3910418044989⟩,⟨-1286088336660,-1286044360034⟩,⟨-132377904863,-132336259207⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-681067304482,-681066142950⟩,⟨5100251189460,5100270894906⟩,⟨-5770627635090,-5770605349552⟩,⟨-66012878061414,-66012343210806⟩,⟨34979939933546,34980663171152⟩,⟨11141920374592,11142896809828⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3652800929310,3652802187354⟩,⟨-14755011226948,-14754991520757⟩,⟨-9297614460411,-9297592174717⟩,⟨77219010514173,77219545400624⟩,⟨61976637310585,61977360554106⟩,⟨19180801235223,19181777672963⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨452157159041,452157314778⟩,⟨495794182132,495797421289⟩,⟨-120314268252,-120311154666⟩,⟨-15050581369150,-15050488088358⟩,⟨-7592951492001,-7592840450507⟩,⟨-4023909761437,-4023775922431⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨318266052442,318266052446⟩,⟨1967524518296,1967524518298⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-318266052446,-318266052442⟩,⟨-1967524518298,-1967524518296⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨781245575330,781245575334⟩,⟨-1967524518298,-1967524518296⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1387915627097,1387915654571⟩,⟨-9142347319889,-9142347250439⟩,⟨-4057278345636,-4057278314809⟩,⟨57445190564894,57445190575028⟩,⟨35711611076315,35711611158501⟩,⟨11313783092386,11313783094458⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1387915654571,-1387915627097⟩,⟨9142347250439,9142347319889⟩,⟨4057278314809,4057278345636⟩,⟨-57445190575028,-57445190564894⟩,⟨-35711611158501,-35711611076315⟩,⟨-11313783094458,-11313783092386⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-288404026795,-288403999321⟩,⟨9142347250439,9142347319889⟩,⟨4057278314809,4057278345636⟩,⟨-57445190575028,-57445190564894⟩,⟨-35711611158501,-35711611076315⟩,⟨-11313783094458,-11313783092386⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12055564245,-12055563094⟩,⟨412520142175,412520147997⟩,⟨55081438211,55081450422⟩,⟨-4326156583809,-4326156568587⟩,⟨1998655527985,1998655589828⟩,⟨2749122579162,2749122603770⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨440101594796,440101751684⟩,⟨908314324307,908317569286⟩,⟨-65232830041,-65229704244⟩,⟨-19376737952959,-19376644656945⟩,⟨-5594295964016,-5594184860679⟩,⟨-1274787182275,-1274653318661⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101523589694,-101523589692⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4243783179,4243783180⟩,⟨25811472488,25811472493⟩,⟨40312003485,40312003486⟩,⟨-275763827840,-275763827831⟩,⟨245185044806,245185044811⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9188164597,9188164824⟩,⟨9923474787,9923476171⟩,⟨87279040344,87279042468⟩,⟨-760844719298,-760844704453⟩,⟨94263805138,94263818079⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1475989670588,1475989691723⟩,⟨-7439288070189,-7439287689602⟩,⟨-1397686413685,-1397686345634⟩,⟨109263537530647,109263545113004⟩,⟨23295954067804,23295955607412⟩,⟨5170777210993,5170777503316⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12334236122,12334236605⟩,⟨-48845739622,-48845732854⟩,⟨105483912979,105483918368⟩,⟨-242575689475,-242575543400⟩,⟨-281929154989,-281929071170⟩,⟨-178686160876,-178686141161⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12334236605,-12334236122⟩,⟨48845732854,48845739622⟩,⟨-105483918368,-105483912979⟩,⟨242575543400,242575689475⟩,⟨281929071170,281929154989⟩,⟨178686141161,178686160876⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113857826299,-113857825814⟩,⟨-824321118424,-824321111654⟩,⟨-105483918368,-105483912979⟩,⟨2441598798952,2441598945027⟩,⟨281929071170,281929154989⟩,⟨178686141161,178686160876⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨81651006656,81651008278⟩,⟨-537843833828,-537843829719⟩,⟨628177396544,628177411913⟩,⟨3379497676707,3379497677421⟩,⟨-3609231687886,-3609231648744⟩,⟨-2464890610862,-2464890610602⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨109608702057,109608705805⟩,⟨-1274454303974,-1274454248881⟩,⟨739474529528,739474569353⟩,⟨19928785564371,19928786782498⟩,⟨-6681608661201,-6681608030638⟩,⟨-4521956758633,-4521956564732⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-109608705805,-109608702057⟩,⟨1274454248881,1274454303974⟩,⟨-739474569353,-739474529528⟩,⟨-19928786782498,-19928785564371⟩,⟨6681608030638,6681608661201⟩,⟨4521956564732,4521956758633⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨989902921971,989902925719⟩,⟨1274454248881,1274454303974⟩,⟨-739474569353,-739474529528⟩,⟨-19928786782498,-19928785564371⟩,⟨6681608030638,6681608661201⟩,⟨4521956564732,4521956758633⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122533831322,122533831789⟩,⟨787075407231,787075416445⟩,⟨187750213909,187750219905⟩,⟨-2431326139625,-2431325912714⟩,⟨-690199959358,-690199835077⟩,⟨-169662895055,-169662847374⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11790329607,11790329709⟩,⟨170721995428,170721997560⟩,⟨21846370126,21846371338⟩,⟨730342701977,730342754691⟩,⟨99776617662,99776644654⟩,⟨-16767375146,-16767368835⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨173096367519,173096518871⟩,⟨1670209700639,1670215073369⟩,⟨115806347499,115809224067⟩,⟨-1779114683841,-1778907830381⟩,⟨400679359466,400824044502⟩,⟨-581307648181,-581187554991⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-173096518871,-173096367519⟩,⟨-1670215073369,-1670209700639⟩,⟨-115809224067,-115806347499⟩,⟨1778907830381,1779114683841⟩,⟨-400824044502,-400679359466⟩,⟨581187554991,581307648181⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56048037064,56048248533⟩,⟨-61793716326,-61786697373⟩,⟨124936727484,124940568760⟩,⟨-2131563899013,-2131303361148⟩,⟨-1686912381162,-1686723719500⟩,⟨448809650128,448971388974⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28677238580286,28677263974302⟩,⟨-255212502117795,-255211874117159⟩,⟨-85730839206976,-85730366381589⟩,⟨3667311431442502,3667333609761700⟩,⟨1356600373733306,1356619923751212⟩,⟨310912332098977,310932233146216⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13655644414,13655644519⟩,⟨175429459318,175429462042⟩,⟨41847221002,41847222500⟩,⟨584928763509,584928842537⟩,⟨114961458800,114961498822⟩,⟨26303856754,26303871624⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨356163739368,356164057495⟩,⟨1405843480049,1405855426742⟩,⟨26696285267,26703171384⟩,⟨-20636381431396,-20635888399473⟩,⟨-3544864617878,-3544518081280⟩,⟨-1978300842918,-1978016427214⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-356164057495,-356163739368⟩,⟨-1405855426742,-1405843480049⟩,⟨-26703171384,-26696285267⟩,⟨20635888399473,20636381431396⟩,⟨3544518081280,3544864617878⟩,⟨1978016427214,1978300842918⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83937537301,83938012316⟩,⟨-497541102435,-497525910763⟩,⟨-91936001425,-91925989511⟩,⟨1259150446514,1259736774451⟩,⟨-2049777882736,-2049320242801⟩,⟨703229244939,703647524257⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237625190510,237625190515⟩,⟨1572168019358,1572168019367⟩,⟨310209424734,310209424739⟩,⟨-3959419704444,-3959419704440⟩,⟨-1562491150668,-1562491150660⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1671572709577,-1671571255340⟩,⟨-4027024048006,-4026982879528⟩,⟨430277420211,430303756775⟩,⟨39643638683096,39645127378398⟩,⟨-7394102722236,-7392926254148⟩,⟨2191864280000,2192977223262⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186286533079,-186286370303⟩,⟨-1645367295912,-1645361651215⟩,⟨-237482347967,-237479155296⟩,⟨2348932124917,2349160616071⟩,⟨-154362541512,-154204418198⟩,⟨649152227291,649285554861⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51338657431,51338820212⟩,⟨-73199276554,-73193631848⟩,⟨72727076767,72730269443⟩,⟨-1610487579527,-1610259088369⟩,⟨-1716853692180,-1716695568858⟩,⟨302443592788,302576920361⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4278748930,4278789289⟩,⟨-30079853867,-30078421242⟩,⟨4851271447,4852146716⟩,⟨-42623796749,-42564795937⟩,⟨-284640734628,-284597266711⟩,⟨49215962388,49252878578⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2397116756,2397131958⟩,⟨-6835697602,-6835148798⟩,⟨6791579798,6791899482⟩,⟨-140650126116,-140626808615⟩,⟨-170011928532,-169995482074⟩,⟨37864584914,37877969968⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4258578749,4258605842⟩,⟨-29470724653,-29469639555⟩,⟨4376065234,4376682172⟩,⟨-62072098243,-62022170730⟩,⟨-270343310839,-270309642595⟩,⟨41220332440,41246274990⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4258605842,-4258578749⟩,⟨29469639555,29470724653⟩,⟨-4376682172,-4376065234⟩,⟨62022170730,62072098243⟩,⟨270309642595,270343310839⟩,⟨-41246274990,-41220332440⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨20143088,20210540⟩,⟨-610214312,-607696589⟩,⟨474589275,476081482⟩,⟨19398373981,19507302306⟩,⟨-14331092033,-14253955872⟩,⟨7969687398,8032546138⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56048037064,56048248533⟩,⟨-61793716326,-61786697373⟩,⟨124936727484,124940568760⟩,⟨-2131563899013,-2131303361148⟩,⟨-1686912381162,-1686723719500⟩,⟨448809650128,448971388974⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨20143088,20210540⟩,⟨-610214312,-607696589⟩,⟨474589275,476081482⟩,⟨19398373981,19507302306⟩,⟨-14331092033,-14253955872⟩,⟨7969687398,8032546138⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112957639884,113387136615⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨113816633344,117682103911⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113387136615,-112957639884⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436368677273,436798174004⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨45170976358,46751054562⟩,⟨-117682103911,-113816633344⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158128616242,160138191177⟩,⟨981829523865,985694994432⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44741479627,47180551293⟩,⟨-117682103911,-113816633344⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2502058066176,-2497885283648⟩,⟨10661930935953,10702470597440⟩,⟨0,0⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-258024738076,-256618683435⟩,⟨-1406711255186,-1394193003281⟩,⟨0,0⟩,⟨10580697469779,10783396361089⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256618683435,258024738076⟩,⟨1394193003281,1406711255186⟩,⟨0,0⟩,⟨-10783396361089,-10580697469779⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986124491161,986553987892⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-119669504256,-119190727040⟩,⟨-1225936309717,-1225402597781⟩,⟨0,0⟩,⟨-1366897627561,-1365707727607⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-107375332530,-106899183313⟩,⟨-980799782110,-979363450628⟩,⟨0,0⟩,⟨1224334941456,1227003501238⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106899183313,107375332530⟩,⟨979363450628,980799782110⟩,⟨0,0⟩,⟨-1227003501238,-1224334941456⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨363517866748,365400070606⟩,⟨2373556453909,2387511037296⟩,⟨0,0⟩,⟨-12010399862327,-11805032411235⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2132186901504,-2118301780288⟩,⟨6741258721912,6853807574969⟩,⟨2996114987514,3037177474404⟩,⟨-42723221008325,-41331594871519⟩,⟨-26577456713493,-25918863830944⟩,⟨-8389585683311,-8164265653620⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310542012502,-304648100882⟩,⟨-941963701354,-893355609706⟩,⟨-416151877413,-398351802590⟩,⟨5817050213265,6344471089312⟩,⟨3598306555116,3850174367551⟩,⟨1156266436799,1238971089564⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨304648100882,310542012502⟩,⟨893355609706,941963701354⟩,⟨398351802590,416151877413⟩,⟨-6344471089312,-5817050213265⟩,⟨-3850174367551,-3598306555116⟩,⟨-1238971089564,-1156266436799⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160138191177,-158128616242⟩,⟨-985694994432,-981829523865⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939373436599,941383011534⟩,⟨-985694994432,-981829523865⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173072244352,-170722602624⟩,⟨-1153729779440,-1146752134631⟩,⟨-511260647361,-509667615391⟩,⟨-1210621488979,-1196022329424⟩,⟨747730382202,755383642421⟩,⟨-237730500467,-236251324330⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148181489386,-145857737090⟩,⟨-835353714701,-824577044752⟩,⟨-369977071027,-366681505592⟩,⟨1011514270020,1046773587589⟩,⟨1375989575503,1392698289570⟩,⟨201007889600,204370022383⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145857737090,148181489386⟩,⟨824577044752,835353714701⟩,⟨366681505592,369977071027⟩,⟨-1046773587589,-1011514270020⟩,⟨-1392698289570,-1375989575503⟩,⟨-204370022383,-201007889600⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨450505837972,458723501888⟩,⟨1717932654458,1777317416055⟩,⟨765033308182,786128948440⟩,⟨-7391244676901,-6828564483285⟩,⟨-5242872657121,-4974296130619⟩,⟨-1443341111947,-1357274326399⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨814023704720,824123572494⟩,⟨4091489108367,4164828453351⟩,⟨765033308182,786128948440⟩,⟨-19401644539228,-18633596894520⟩,⟨-5242872657121,-4974296130619⟩,⟨-1443341111947,-1357274326399⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89482959254,94361102586⟩,⟨-235364207822,-227633266688⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12811696625872,13510123376487⟩,⟨30906467546888,35535251768537⟩,⟨-131895441782786,-118494230292813⟩,⟨149115259925515,186934505787111⟩,⟨-395272708799079,-239694087858363⟩,⟨2191884966169457,2575314388816416⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9485142755821,10126324143008⟩,⟨70556338338776,77809804573587⟩,⟨-89946086540831,-78067763067927⟩,⟨102019562814818,192199511362090⟩,⟨-838793153000030,-650951192158307⟩,⟨1416422450419404,1749580625524595⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨82415247360,87936850176⟩,⟨-715137427325,-569272713875⟩,⟨629877462382,826680047319⟩,⟨6053647391017,10769632384881⟩,⟨-8148829590234,-943438870062⟩,⟨-6506301659436,4062937137099⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1181926875136,1187448477952⟩,⟨-715137427325,-569272713875⟩,⟨629877462382,826680047319⟩,⟨6053647391017,10769632384881⟩,⟨-8148829590234,-943438870062⟩,⟨-6506301659436,4062937137099⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨79472640192,84597263104⟩,⟨-665271205304,-527115053749⟩,⟨583231699582,769036006880⟩,⟨5202813314242,9765967241526⟩,⟨-7301009098288,-408258808176⟩,⟨-6590510136286,3470257292046⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨85429609754,91363191416⟩,⟨-773501550848,-607772611943⟩,⟨672476057933,894147438273⟩,⟨6576182074892,12241057481830⟩,⟨-9512290203087,-1110989087586⟩,⟨-6949974283772,5216823907741⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-87936850176,-82415247360⟩,⟨569272713875,715137427325⟩,⟨-826680047319,-629877462382⟩,⟨-10769632384881,-6053647391017⟩,⟨943438870062,8148829590234⟩,⟨-4062937137099,6506301659436⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1011574777600,1017096380416⟩,⟨569272713875,715137427325⟩,⟨-826680047319,-629877462382⟩,⟨-10769632384881,-6053647391017⟩,⟨943438870062,8148829590234⟩,⟨-4062937137099,6506301659436⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-91652874944,-85667595840⟩,⟨615400841388,777304786768⟩,⟨-898543878916,-680916388355⟩,⟨-12255362682061,-6888616200863⟩,⟨1400997147847,9492442336217⟩,⟨-5150439727124,6650214067666⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-84782920895,-78816064350⟩,⟨506569966152,674686507708⟩,⟨-782116002497,-557547756323⟩,⟨-10227833438298,-4428805496245⟩,⟨-559170982285,8002327705084⟩,⟨-4526579762358,7841577025128⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨646688859,12547127066⟩,⟨-266931584696,66913895765⟩,⟨-109639944564,336599681950⟩,⟨-3651651363406,7812251985585⟩,⟨-10071461185372,6891338617498⟩,⟨-11476554046130,13058400932869⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨323344429,6273563533⟩,⟨-133465792348,33456947883⟩,⟨-54819972282,168299840975⟩,⟨-1825825681703,3906125992793⟩,⟨-5035730592686,3445669308749⟩,⟨-5738277023065,6529200466435⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6273563533,-323344429⟩,⟨-33456947883,133465792348⟩,⟨-168299840975,54819972282⟩,⟨-3906125992793,1825825681703⟩,⟨-3445669308749,5035730592686⟩,⟨-6529200466435,5738277023065⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755849820083,761800058451⟩,⟨-33456947883,133465792348⟩,⟨-168299840975,54819972282⟩,⟨-3906125992793,1825825681703⟩,⟨-3445669308749,5035730592686⟩,⟨-6529200466435,5738277023065⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6177536304,7033022138⟩,⟨-114390664390,-85341073880⟩,⟨94426480916,132232597872⟩,⟨1496999666275,2652939819093⟩,⟨-2378823863270,-793672007172⟩,⟨-319047206376,1892989157450⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7033022138,-6177536304⟩,⟨85341073880,114390664390⟩,⟨-132232597872,-94426480916⟩,⟨-2652939819093,-1496999666275⟩,⟨793672007172,2378823863270⟩,⟨-1892989157450,319047206376⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092478605638,1093334091472⟩,⟨85341073880,114390664390⟩,⟨-132232597872,-94426480916⟩,⟨-2652939819093,-1496999666275⟩,⟨793672007172,2378823863270⟩,⟨-1892989157450,319047206376⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7055611904,-6194955584⟩,⟨85823266456,115127074304⟩,⟨-133083868354,-94960007692⟩,⟨-2682073247277,-1512156990679⟩,⟨805568578192,2408072832404⟩,⟨-1921283954383,312899848274⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3527805952,-3097477792⟩,⟨42911633228,57563537152⟩,⟨-66541934177,-47480003846⟩,⟨-1341036623639,-756078495339⟩,⟨402784289096,1204036416202⟩,⟨-960641977192,156449924137⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3097477792,3527805952⟩,⟨-57563537152,-42911633228⟩,⟨47480003846,66541934177⟩,⟨756078495339,1341036623639⟩,⟨-1204036416202,-402784289096⟩,⟨-156449924137,960641977192⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765220861408,765651208832⟩,⟨-57563537152,-42911633228⟩,⟨47480003846,66541934177⟩,⟨756078495339,1341036623639⟩,⟨-1204036416202,-402784289096⟩,⟨-156449924137,960641977192⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273119651409,273333522868⟩,⟨21335268470,28597666098⟩,⟨-33058149468,-23606620229⟩,⟨-663234954774,-374249916568⟩,⟨198418001793,594705965818⟩,⟨-473247289363,79761801594⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530441722816,1531302417664⟩,⟨-115127074304,-85823266456⟩,⟨94960007692,133083868354⟩,⟨1512156990678,2682073247278⟩,⟨-2408072832404,-805568578192⟩,⟨-312899848274,1921283954384⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1188604976767,1195092885257⟩,⟨-844876395007,-665266727792⟩,⟨736090994870,976654879909⟩,⟨7819152600324,13918018533920⟩,⟨-11008077138198,-1926512777526⟩,⟨-6774956043150,6396313563517⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1277698325758,1290674142738⟩,⟨-1689752790013,-1330533455584⟩,⟨1472181989740,1953309759818⟩,⟨15638305200653,27836037067830⟩,⟨-22016154276388,-3853025555052⟩,⟨-13545333611818,12792627127031⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨165140236096,176250137984⟩,⟨-1454101334590,-1133467354087⟩,⟨1254136239598,1680902878460⟩,⟨11399061194782,22785575812505⟩,⟨-17652933367942,-1059361861660⟩,⟨-14226030855394,9578072715196⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨56655653578,60927320742⟩,⟨-498161018687,-380667294826⟩,⟨419543547391,577152244713⟩,⟨3675507385556,7651321148832⟩,⟨-5982330702966,-35998519443⟩,⟨-5283180643026,3356389161065⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380163064471,380674723053⟩,⟨1077111152,18509722049⟩,⟨-22452313721,225305523⟩,⟨-554062563257,142491187337⟩,⟨-318766840418,635072729035⟩,⟨-744885027428,584629907848⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175744924483,3180019135465⟩,⟨-154831638865,-8985703717⟩,⟨-1884654091,187810952565⟩,⟨-1191871103554,4649745069427⟩,⟨-5330596991645,2666630495887⟩,⟨-4890582746116,6253059394672⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨163639837677,176214640153⟩,⟨-1449366253737,-1099953188146⟩,⟨1211672919727,1679652996618⟩,⟨10556229916457,22527189092191⟩,⟨-17763910933486,41216029153⟩,⟨-15553051625109,10251055700176⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨328780073773,352464778137⟩,⟨-2903467588327,-2233420542233⟩,⟨2465809159325,3360555875078⟩,⟨21955291111239,45312764904696⟩,⟨-35416844301428,-1018145832507⟩,⟨-29779082480503,19829128415372⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519602463572,527815545007⟩,⟨-46361501252,184944380476⟩,⟨-233214138812,75964377336⟩,⟨-5420865577772,2562459901620⟩,⟨-4815544075312,6991352076312⟩,⟨-9064336135610,8003088820355⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357196248483,365698645545⟩,⟨-48182565975,192208935720⟩,⟨-242374714497,78948233425⟩,⟨-5642236904126,2696787102351⟩,⟨-5047160631700,7279801683851⟩,⟨-9437821868988,8370993919395⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714392496966,731397291090⟩,⟨-96365131950,384417871440⟩,⟨-484749428994,157896466850⟩,⟨-11284473808252,5393574204702⟩,⟨-10094321263400,14559603367702⟩,⟨-18875643737976,16741987838790⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523408700678,1525124881360⟩,⟨-29786000424,28567397934⟩,⟨-37272590180,38657387438⟩,⟨-1140782828415,1185073581003⟩,⟨-1614400825232,1573255285078⟩,⟨-2205889005724,2240331160760⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989813766479,1014516062061⟩,⟨-153481105786,552226427350⟩,⟨-697186339380,244732053694⟩,⟨-16432293514490,8289678100986⟩,⟨-15101291127557,21268703994617⟩,⟨-27683721284741,24745832062858⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67843160637,67949453954⟩,⟨10599398750,14218495964⟩,⟨-16436207178,-11727810284⟩,⟨-328926313155,-184440396417⟩,⟨96854763910,294766183522⟩,⟨-234280516946,41644699135⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50227700705,50930563468⟩,⟨260304400090,268042292107⟩,⟨34885317147,39899821067⟩,⟨-1366672614909,-1178583051152⟩,⟨-307184882963,-119466538299⟩,⟨-288302811485,-68853962990⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130265663196,2132662388562⟩,⟨-320677585880,-238919724820⟩,⟨264355108394,370694850722⟩,⟨4223027250275,7494817493620⟩,⟨-6735370892008,-2257412308056⟩,⟨-855155833211,5383804965067⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2965177783732,2970183296990⟩,⟨-669917011531,-498838810838⟩,⟨551945169070,774406436622⟩,⟨8845202462381,15707543052745⟩,⟨-14128863873911,-4744186936596⟩,⟨-1752237591450,11314432955195⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135454740537,137582091083⟩,⟨670961138239,701292458337⟩,⟨119293057777,143655359586⟩,⟨-3614446699327,-2687024003513⟩,⟨-1377922871597,-365942105989⟩,⟨-824952693138,394614799788⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8786941745821,8924942861520⟩,⟨-46207279974551,-42852208372517⟩,⟨-9465271359079,-7618877872229⟩,⟨589575690857254,716611052633002⟩,⟨97683163559925,188799075142534⟩,⟨-12788500291177,74431721851004⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7910271874846,8235017854521⟩,⟨-43881152867285,-34094333805499⟩,⟨-14392770088626,-4872209144607⟩,⟨350954989894955,741403905876751⟩,⟨-49681508166124,377467119340348⟩,⟨-240727495304406,281548118752315⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15820543749692,16470035709042⟩,⟨-87762305734570,-68188667610998⟩,⟨-28785540177252,-9744418289214⟩,⟨701909979789910,1482807811753502⟩,⟨-99363016332248,754934238680696⟩,⟨-481454990608812,563096237504630⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10661930935953,10702470597440⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710694,2028067813858452⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9562419308177,9602958969664⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710699,2028067813858436⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2378215779456,2382867339072⟩,⟨-11978441145317,-11837681660582⟩,⟨0,0⟩,⟨99082204851667,105744330752101⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7549266110283,7645205835259⟩,⟨-47656403390549,-46285600556061⟩,⟨-21118327777027,-20571378024900⟩,⟨567566909826403,594132540852841⟩,⟨304085353371292,316441475698585⟩,⟨112111982187759,116670179379896⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6449754482507,6545694207483⟩,⟨-47656403390549,-46285600556060⟩,⟨-21118327777028,-20571378024899⟩,⟨567566909826408,594132540852832⟩,⟨304085353371294,316441475698582⟩,⟨112111982187759,116670179379895⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1945229536000,1961464298368⟩,⟨-8124149501845,-7774814159749⟩,⟨-3600113308668,-3455472959886⟩,⟨35308641965344,46306904162768⟩,⟨24477901638928,29510681295750⟩,⟨7044193637422,9029529534280⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101308883270,101738380002⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135097999795,137107574731⟩,⟨695269737231,702731247947⟩,⟨309196434044,311221815873⟩,⟨-1767320322048,-1753486165276⟩,⟨-1566419871340,-1558562429988⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4323445315456,4344331637440⟩,⟨-20102590647162,-19612495820331⟩,⟨-3600113308668,-3455472959886⟩,⟨134390846817011,152051234914869⟩,⟨24477901638928,29510681295750⟩,⟨7044193637422,9029529534280⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨657560147546,704929556274⟩,⟨-5806935176654,-4466841084466⟩,⟨4931618318650,6721111750156⟩,⟨43910582222478,90625529809392⟩,⟨-70833688602856,-2036291665014⟩,⟨-59558164961006,39658256830744⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4981005463002,5049261193714⟩,⟨-25909525823816,-24079336904797⟩,⟨1331505009982,3265638790270⟩,⟨178301429039489,242676764724261⟩,⟨-46355786963928,27474389630736⟩,⟨-52513971323584,48687786365024⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458949308284,467210751645⟩,⟨1556251251553,1793128292103⟩,⟨122684728584,302171247490⟩,⟨-34841703748960,-25732951618036⟩,⟨-3232442858873,5136871562781⟩,⟨-4859144946689,4505106072121⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨225915279768,226774273230⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-226774273230,-225915279768⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨872737354546,873596348008⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1887708774940,1893262565501⟩,⟨-14282980494402,-14152591376986⟩,⟨0,0⟩,⟨125997226743230,131930939874303⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨788197147164,793750937725⟩,⟨-14282980494402,-14152591376986⟩,⟨0,0⟩,⟨125997226743230,131930939874303⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32073427611,34060218997⟩,⟨-697845438632,-657489931166⟩,⟨312815742780,315329962371⟩,⟨8057125306216,8718668018697⟩,⟨-6467888110707,-6405006849897⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨491022735895,501270970642⟩,⟨858405812921,1135638360937⟩,⟨435500471364,617501209861⟩,⟨-26784578442744,-17014283599339⟩,⟨-9700330969580,-1268135287116⟩,⟨-4859144946689,4505106072121⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507340798957,508333108400⟩,⟨2520383226112,2560338836291⟩,⟨0,0⟩,⟨2439291441574,4695713285828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226569561286,231750737528⟩,⟨1521648080729,1692302350125⟩,⟨200950268743,285487030351⟩,⟨-7358464459260,-421075564506⟩,⟨-3486430897543,852774573390⟩,⟨-2246510352886,2082828880988⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-704929556274,-657560147546⟩,⟨4466841084466,5806935176654⟩,⟨-6721111750156,-4931618318650⟩,⟨-90625529809392,-43910582222478⟩,⟨2036291665014,70833688602856⟩,⟨-39658256830744,59558164961006⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3618515759182,3686771489894⟩,⟨-15635749562696,-13805560643677⟩,⟨-10321225058824,-8387091278536⟩,⟨43765317007619,108140652692391⟩,⟨26514193303942,100344369898606⟩,⟨-32614063193322,68587694495286⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨444610342394,459735290467⟩,⟨338390963778,660025671987⟩,⟨-269470517012,13028022264⟩,⟨-20535079778962,-9745501069290⟩,⟨-13016916799359,-1802282340789⟩,⟨-11073561128316,2695777095982⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨316257232484,320276382354⟩,⟨1963659047730,1971389988864⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-320276382354,-316257232484⟩,⟨-1971389988864,-1963659047730⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨779235245422,783254395292⟩,⟨-1971389988864,-1963659047730⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1378604260832,1397279932376⟩,⟨-9304209822082,-8984149461102⟩,⟨-4123041999598,-3992955316042⟩,⟨52794263525177,62120143602259⟩,⟨33580718228957,37855107721927⟩,⟨10477856101068,12153132386520⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1397279932376,-1378604260832⟩,⟨8984149461102,9304209822082⟩,⟨3992955316042,4123041999598⟩,⟨-62120143602259,-52794263525177⟩,⟨-37855107721927,-33580718228957⟩,⟨-12153132386520,-10477856101068⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-297768304600,-279092633056⟩,⟨8984149461102,9304209822082⟩,⟨3992955316042,4123041999598⟩,⟨-62120143602259,-52794263525177⟩,⟨-37855107721927,-33580718228957⟩,⟨-12153132386520,-10477856101068⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12777375349,-11356876126⟩,⟨394474704048,431118450538⟩,⟨44188779791,66156745946⟩,⟨-4657286440979,-4008311185477⟩,⟨1779002471659,2214206526753⟩,⟨2647911763605,2849519340319⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨431832967045,448378414341⟩,⟨732865667826,1091144122525⟩,⟨-225281737221,79184768210⟩,⟨-25192366219941,-13753812254767⟩,⟨-11237914327700,411924185964⟩,⟨-8425649364711,5545296436301⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101738380002,-101308883270⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4122475126,4365640831⟩,⟨24624363468,26999370026⟩,⟨40206963047,40417161119⟩,⟨-281365320833,-270166864687⟩,⟨244629257582,245740915920⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8916809197,9461239598⟩,⟨5701147531,14129335628⟩,⟨86966641867,87592282552⟩,⟨-826560643023,-694730337601⟩,⟨88809042402,99690417602⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1466922995487,1485123605867⟩,⟨-7598409007743,-7282766394708⟩,⟨-1434231769683,-1361743541310⟩,⟨105480262232486,113149014991965⟩,⟨22375318133272,24241275035829⟩,⟨4944131425405,5403432549948⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11896438497,12779410343⟩,⟨-57777673440,-39977047427⟩,⟨103685812412,107268496483⟩,⟨-456310128791,-28763877773⟩,⟨-323811274733,-239848426592⟩,⟨-188419464635,-168919865006⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12779410343,-11896438497⟩,⟨39977047427,57777673440⟩,⟨-107268496483,-103685812412⟩,⟨28763877773,456310128791⟩,⟨239848426592,323811274733⟩,⟨168919865006,188419464635⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114517790345,-113205321767⟩,⟨-833619300581,-814959681106⟩,⟨-107268496483,-103685812412⟩,⟨2227787133325,2655333384343⟩,⟨239848426592,323811274733⟩,⟨168919865006,188419464635⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨79155550024,84167338117⟩,⟨-558548979518,-517735467110⟩,⟨617530448831,638611755554⟩,⟨3046413649121,3726126377662⟩,⟨-3835156016858,-3379217326628⟩,⟨-2573759222970,-2355320383113⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨105606065108,113685837897⟩,⟨-1336095133067,-1215038939292⟩,⟨714093535412,764546561326⟩,⟨18516671236086,21414395486149⟩,⟨-7341405313516,-6014460559487⟩,⟨-4786515703108,-4258360875444⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-113685837897,-105606065108⟩,⟨1215038939292,1336095133067⟩,⟨-764546561326,-714093535412⟩,⟨-21414395486149,-18516671236086⟩,⟨6014460559487,7341405313516⟩,⟨4258360875444,4786515703108⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨985825789879,993905562668⟩,⟨1215038939292,1336095133067⟩,⟨-764546561326,-714093535412⟩,⟨-21414395486149,-18516671236086⟩,⟨6014460559487,7341405313516⟩,⟨4258360875444,4786515703108⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121129316866,123938644910⟩,⟨772674109844,801844416583⟩,⟨181888657631,193588208022⟩,⟨-2731272361819,-2139463986448⟩,⟨-823926606306,-555314211119⟩,⟨-223304439289,-115306593116⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11655579215,11927408474⟩,⟨167815911348,173648441508⟩,⟨21350907912,22344740848⟩,⟨654975101540,805309862782⟩,⟨86252120938,113266597884⟩,⟨-19693530800,-13853600344⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167708641037,178665544339⟩,⟨1462614907958,1878304479353⟩,⟨-5051263654,231413505756⟩,⟨-10856043088827,7333483025464⟩,⟨-6166535966085,7074736958186⟩,⟨-6687764072205,5530640000380⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178665544339,-167708641037⟩,⟨-1878304479353,-1462614907958⟩,⟨-231413505756,5051263654⟩,⟨-7333483025464,10856043088827⟩,⟨-7074736958186,6166535966085⟩,⟨-5530640000380,6687764072205⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47904016947,64042096491⟩,⟨-356656398624,229687442167⟩,⟨-30463237013,290538294005⟩,⟨-14691947484724,10434967524321⟩,⟨-10561167855729,7019310539475⟩,⟨-7777150353266,8770592953193⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27989325624258,29381578348086⟩,⟨-278257777464932,-232507225352886⟩,⟨-105279290544129,-66959356813705⟩,⟨2714192647734527,4635821036627203⟩,⟨458150537323864,2288862386460779⟩,⟨-696282453565578,1328291776057784⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13344389485,13970555031⟩,⟨170245561248,180770276384⟩,⟨40076063386,43643122214⟩,⟨470236199577,698132966624⟩,⟨69893411880,160003387794⟩,⟨9836065448,42763322984⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339696691801,373326617782⟩,⟨798211528469,2008754623054⟩,⟨-317511998513,353586144865⟩,⟨-46584894096395,5557553971338⟩,⟨-21014235209043,14515828679912⟩,⟨-16954419501067,13139008318301⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-373326617782,-339696691801⟩,⟨-2008754623054,-798211528469⟩,⟨-353586144865,317511998513⟩,⟨-5557553971338,46584894096395⟩,⟨-14515828679912,21014235209043⟩,⟨-13139008318301,16954419501067⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58506349263,108681722540⟩,⟨-1275888955228,292932594056⟩,⟨-578867882086,396696766723⟩,⟨-30749920191279,32831081841628⟩,⟨-25753743007612,21426159395007⟩,⟨-21564657683012,22499715937368⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236406883065,238845954733⟩,⟨1568007091777,1576327595955⟩,⟨309196434044,311221815873⟩,⟨-3966343577600,-3952509420828⟩,⟨-1566419871340,-1558562429988⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1715408958538,-1628877494761⟩,⟨-5466444773038,-2585475122820⟩,⟨-603537009437,1506205556781⟩,⟨-21301312406598,100584833847837⟩,⟨-61524918167585,45585992469264⟩,⟨-54379976884318,58584191916854⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-193363541064,-179447686786⟩,⟨-1867187941758,-1429514944638⟩,⟨-370059301906,-99678132122⟩,⟨-7204660046902,11965437538651⟩,⟨-7515116698379,7094705444304⟩,⟨-6171499650937,7482477544055⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43043342001,59398267947⟩,⟨-299180849981,146812651317⟩,⟨-60862867862,211543683751⟩,⟨-11171003624502,8012928117823⟩,⟨-9081536569719,5536143014316⟩,⟨-6518549450127,7136109906471⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2549030929,6330269900⟩,⟨-109569223551,39765695251⟩,⟨-36727860637,51824367683⟩,⟨-3776355567716,3771464867924⟩,⟨-3009798683572,2206990755549⟩,⟨-2330713467753,2387099205058⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1685047473,3208837584⟩,⟨-32324941080,15862346484⟩,⟨-6575917602,22856199230⟩,⟨-1286865518223,1028571627791⟩,⟨-1096336494180,654644455134⟩,⟨-727715272908,852420814153⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨2981145475,5724378171⟩,⟨-81375486967,16382269101⟩,⟨-22237697065,35478463185⟩,⟨-2475990351241,2447744162645⟩,⟨-2139105972952,1408401566039⟩,⟨-1437081246483,1590083579536⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5724378171,-2981145475⟩,⟨-16382269101,81375486967⟩,⟨-35478463185,22237697065⟩,⟨-2447744162645,2475990351241⟩,⟨-1408401566039,2139105972952⟩,⟨-1590083579536,1437081246483⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3175347242,3349124425⟩,⟨-125951492652,121141182218⟩,⟨-72206323822,74062064748⟩,⟨-6224099730361,6247455219165⟩,⟨-4418200249611,4346096728501⟩,⟨-3920797047289,3824180451541⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47904016947,64042096491⟩,⟨-356656398624,229687442167⟩,⟨-30463237013,290538294005⟩,⟨-14691947484724,10434967524321⟩,⟨-10561167855729,7019310539475⟩,⟨-7777150353266,8770592953193⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3175347242,3349124425⟩,⟨-125951492652,121141182218⟩,⟨-72206323822,74062064748⟩,⟨-6224099730361,6247455219165⟩,⟨-4418200249611,4346096728501⟩,⟨-3920797047289,3824180451541⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (527/5120) u, BivariateJet2.affineZ (539/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000043

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000044Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2504150381952,-2504150324096⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-118951416704,-118951416640⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2117293482048,-2117293443136⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2117293482048,-2117293443136⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-173244231360,-173244231296⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-173244231360,-173244231296⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨84606148992,84606149056⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-91663305920,-91663305856⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨84606272960,84606273024⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-91663451456,-91663451392⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-7057178496,-7057178432⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-7057156928,-7057156864⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨176269454848,176269454912⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨176269724352,176269724416⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1944049211840,1944049250432⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1944049211840,1944049250432⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2506246686976,-2506246629120⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2124215558592,-2124215519552⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2110409564992,-2110409526144⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-174423333888,-174423333824⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-172067274752,-172067274688⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨82048171648,82048171712⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-88668116160,-88668116096⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨87186464640,87186464704⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-94700038528,-94700038464⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-7513573824,-7513573760⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-6619944448,-6619944384⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨170716287808,170716287872⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨181886503104,181886503168⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1935986192320,1935986230912⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1952148244864,1952148283456⟩



end LaneCBRB2Cell000044Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000044
open Set LaneCBRB2Cell000044Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112742891520,112742891520⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨119614839193,119614839194⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112742891520,-112742891520⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437012922368,437012922368⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨47542226124,47542226125⟩,⟨-119614839194,-119614839193⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160285117644,160285117645⟩,⟨979896788582,979896788583⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47542226124,47542226125⟩,⟨-119614839194,-119614839193⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2117293482048,-2117293443136⟩,⟨6721821270097,6721821270147⟩,⟨2997787921247,2997787921267⟩,⟨-41093591051142,-41093591050532⟩,⟨-25869205060740,-25869205060438⟩,⟨-8173385523054,-8173385522949⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308655794342,-308655788667⟩,⟨-907058320525,-907058285829⟩,⟨-404528529973,-404528514500⟩,⟨5990560635739,5990560635968⟩,⟨3689443199034,3689443238058⟩,⟨1191503597589,1191503597629⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨308655788667,308655794342⟩,⟨907058285829,907058320525⟩,⟨404528514500,404528529973⟩,⟨-5990560635968,-5990560635739⟩,⟨-3689443238058,-3689443199034⟩,⟨-1191503597629,-1191503597589⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160285117645,-160285117644⟩,⟨-979896788583,-979896788582⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939226510131,939226510132⟩,⟨-979896788583,-979896788582⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173244231360,-173244231296⟩,⟨-1147122553981,-1147122553976⟩,⟨-511592022212,-511592022209⟩,⟨-1196795123045,-1196795123034⟩,⟨753405522895,753405522903⟩,⟨-238038771559,-238038771557⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147988953196,-147988953140⟩,⟨-825499634796,-825499634732⟩,⟨-368155107783,-368155107753⟩,⟨1022328166746,1022328166769⟩,⟨1382203802140,1382203802220⟩,⟨203337844762,203337844768⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147988953140,147988953196⟩,⟨825499634732,825499634796⟩,⟨368155107753,368155107783⟩,⟨-1022328166769,-1022328166746⟩,⟨-1382203802220,-1382203802140⟩,⟨-203337844768,-203337844762⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨456644741807,456644747538⟩,⟨1732557920561,1732557955321⟩,⟨772683622253,772683637756⟩,⟨-7012888802737,-7012888802485⟩,⟨-5071647040278,-5071647001174⟩,⟨-1394841442397,-1394841442351⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨820172218292,820172230016⟩,⟨4117756827951,4117756920635⟩,⟨772683622253,772683637756⟩,⟨-18960880974429,-18960880974165⟩,⟨-5071647040278,-5071647001174⟩,⟨-1394841442397,-1394841442351⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95084452248,95084452250⟩,⟨-239229678388,-239229678386⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12714232358788,12714232359056⟩,⟨31988633747612,31988633749229⟩,⟨-116870502117528,-116870502112599⟩,⟨160964918708853,160964918721726⟩,⟨-294042737538634,-294042737484124⟩,⟨2148570810822148,2148570810958033⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9484083564154,9484083699926⟩,⟨71477466743511,71477468158570⟩,⟨-78243702984463,-78243701555147⟩,⟨140415739283927,140415746422677⟩,⟨-693194135417613,-693194121465874⟩,⟨1422318655769850,1422318682084769⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨87946446848,87946580736⟩,⟨-656713362090,-656711323557⟩,⟨718877251102,718879481508⟩,⟨8472111807524,8472162197535⟩,⟨-4317536631893,-4317466143817⟩,⟨-1369915662413,-1369819615787⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1187458074624,1187458208512⟩,⟨-656713362090,-656711323557⟩,⟨718877251102,718879481508⟩,⟨8472111807524,8472162197535⟩,⟨-4317536631893,-4317466143817⟩,⟨-1369915662413,-1369819615787⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨84606148992,84606273024⟩,⟨-608075344440,-608073388323⟩,⟨665635127925,665637268195⟩,⟨7508351983583,7508401689707⟩,⟨-3629645328663,-3629577242498⟩,⟨-1671428420544,-1671336752977⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨91373526432,91373670688⟩,⟨-707246844432,-707244426860⟩,⟨774193943671,774196588914⟩,⟨9487215086863,9487279107762⟩,⟨-5047339617919,-5047254707858⟩,⟨-1040129931854,-1040017684115⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-87946580736,-87946446848⟩,⟨656711323557,656713362090⟩,⟨-718879481508,-718877251102⟩,⟨-8472162197535,-8472111807524⟩,⟨4317466143817,4317536631893⟩,⟨1369819615787,1369915662413⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1011565047040,1011565180928⟩,⟨656711323557,656713362090⟩,⟨-718879481508,-718877251102⟩,⟨-8472162197535,-8472111807524⟩,⟨4317466143817,4317536631893⟩,⟨1369819615787,1369915662413⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-91663451456,-91663305856⟩,⟨713806435765,713808746010⟩,⟨-781379656406,-781377128664⟩,⟨-9672149723554,-9672090734090⟩,⟨5200103300501,5200183820843⟩,⟨933617266303,933725453130⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-84331582782,-84331437665⟩,⟨601962735695,601965204984⟩,⟨-658948727656,-658946025811⟩,⟨-7339529994008,-7339463815806⟩,⟨3490820297757,3490907375822⟩,⟨1766485984935,1766600295960⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7041943650,7042233023⟩,⟨-105284108737,-105279221876⟩,⟨115245216015,115250563103⟩,⟨2147685092855,2147815291956⟩,⟨-1556519320162,-1556347332036⟩,⟨726356053081,726582611845⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3520971825,3521116512⟩,⟨-52642054369,-52639610938⟩,⟨57622608007,57625281552⟩,⟨1073842546427,1073907645978⟩,⟨-778259660081,-778173666018⟩,⟨363178026540,363291305923⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3521116512,-3520971825⟩,⟨52639610938,52642054369⟩,⟨-57625281552,-57622608007⟩,⟨-1073907645978,-1073842546427⟩,⟨778173666018,778259660081⟩,⟨-363291305923,-363178026540⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758602267104,758602431055⟩,⟨52639610938,52642054369⟩,⟨-57625281552,-57622608007⟩,⟨-1073907645978,-1073842546427⟩,⟨778173666018,778259660081⟩,⟨-363291305923,-363178026540⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7034557268,7034578688⟩,⟨-105056996690,-105056510640⟩,⟨115001421280,115001953164⟩,⟨2139789818571,2139804813236⟩,⟨-1549433991780,-1549416334056⟩,⟨720874784285,720896315949⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7034578688,-7034557268⟩,⟨105056510640,105056996690⟩,⟨-115001953164,-115001421280⟩,⟨-2139804813236,-2139789818571⟩,⟨1549416334056,1549433991780⟩,⟨-720896315949,-720874784285⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092477049088,1092477070508⟩,⟨105056510640,105056996690⟩,⟨-115001953164,-115001421280⟩,⟨-2139804813236,-2139789818571⟩,⟨1549416334056,1549433991780⟩,⟨-720896315949,-720874784285⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7057178496,-7057156864⟩,⟨105732978879,105733470133⟩,⟨-115742463265,-115741925685⟩,⟨-2163751006140,-2163735778211⟩,⟨1570523322387,1570541227798⟩,⟨-737722125898,-737700328183⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3528589248,-3528578432⟩,⟨52866489439,52866735067⟩,⟨-57871231633,-57870962842⟩,⟨-1081875503070,-1081867889105⟩,⟨785261661193,785270613899⟩,⟨-368861062949,-368850164091⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3528578432,3528589248⟩,⟨-52866735067,-52866489439⟩,⟨57870962842,57871231633⟩,⟨1081867889105,1081875503070⟩,⟨-785270613899,-785261661193⟩,⟨368850164091,368861062949⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765651962048,765651992128⟩,⟨-52866735067,-52866489439⟩,⟨57870962842,57871231633⟩,⟨1081867889105,1081875503070⟩,⟨-785270613899,-785261661193⟩,⟨368850164091,368861062949⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273119262272,273119267627⟩,⟨26264127660,26264249173⟩,⟨-28750488291,-28750355320⟩,⟨-534951203309,-534947454642⟩,⟨387354083514,387358497945⟩,⟨-180224078988,-180218696071⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531303924096,1531303984256⟩,⟨-105733470134,-105732978878⟩,⟨115741925684,115742463266⟩,⟨2163735778210,2163751006140⟩,⟨-1570541227798,-1570523322386⟩,⟨737700328182,737722125898⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1195104223047,1195104381229⟩,⟨-775868065572,-775865451779⟩,⟨849310805514,849313665435⟩,⟨11016685889237,11016754725899⟩,⟨-6203672446628,-6203580536430⟩,⟨-411334830626,-411212958854⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1290696818318,1290697134682⟩,⟨-1551736131144,-1551730903558⟩,⟨1698621611028,1698627330869⟩,⟨22033371778477,22033509451786⟩,⟨-12407344893250,-12407161072861⟩,⟨-822669514257,-822426064704⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨176269454848,176269724416⟩,⟨-1321884345898,-1321879568641⟩,⟨1447011976962,1447017204229⟩,⟨17180430381521,17180563749426⟩,⟨-8829840723333,-8829668969195⟩,⟨-2605164605946,-2604943287052⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨60678188640,60678294130⟩,⟨-448885554072,-448883847819⟩,⟨491376309562,491378176481⟩,⟨5696506594022,5696551075535⟩,⟨-2847785561414,-2847725903551⟩,⟨-1049577663310,-1049498357275⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380376694068,380376716471⟩,⟨10314137236,10314430451⟩,⟨-11290820034,-11290499168⟩,⟨-212611675967,-212602585873⟩,⟨154879198460,154889874322⟩,⟨-73808210321,-73795229335⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178232965546,3178233152735⟩,⟨-86182106639,-86179646532⟩,⟨94337626619,94340318725⟩,⟨1781071908578,1781148336566⟩,⟨-1299296919642,-1299207273416⟩,⟨622195466004,622304320426⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨175395525207,175395840466⟩,⟨-1302298490329,-1302293337801⟩,⟨1425571664951,1425577302718⟩,⟨16634900535334,16635036747676⟩,⟨-8380504019867,-8380323525694⟩,⟨-2915238185237,-2914999972031⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨351664980055,351665564882⟩,⟨-2624182836227,-2624172906442⟩,⟨2872583641913,2872594506947⟩,⟨33815330916855,33815600497102⟩,⟨-17210344743200,-17209992494889⟩,⟨-5520402791183,-5519943259083⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523393645976,523393872211⟩,⟨72636845646,72640233012⟩,⟨-79516537292,-79512830908⟩,⟨-1476833899375,-1476743280988⟩,⟨1068275731152,1068395137670⟩,⟨-495262252846,-495105271003⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361112694395,361112928530⟩,⟨75173114667,75176636559⟩,⟨-82293043077,-82289189490⟩,⟨-1523184725527,-1523090126533⟩,⟨1099866236512,1099990583384⟩,⟨-506304894765,-506141738503⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722225388790,722225857060⟩,⟨150346229334,150353273118⟩,⟨-164586086154,-164578378980⟩,⟨-3046369451054,-3046180253066⟩,⟨2199732473024,2199981166768⟩,⟨-1012609789530,-1012283477006⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524269345408,1524269426988⟩,⟨-676959494,-675982188⟩,⟨739972520,741041986⟩,⟨23930964974,23961187569⟩,⟨-21124893742,-21089330606⟩,⟨16804012233,16847341613⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001231813104,1001232515862⟩,⟨207982548927,207992967229⟩,⟨-227682096276,-227670696687⟩,⟨-4207693412557,-4207410760365⟩,⟨3035848145709,3036216747807⟩,⟨-1392980075054,-1392498828938⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67842967313,67842969974⟩,⟨13048046040,13048106666⟩,⟨-14283272878,-14283206536⟩,⟨-264509574595,-264507695430⟩,⟨191064376010,191066585588⟩,⟨-88031966756,-88029276851⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50606938199,50606940908⟩,⟨263810294878,263810355927⟩,⟨37022260548,37022313015⟩,⟨-1269516837911,-1269514931136⟩,⟨-214734372121,-214732414726⟩,⟨-171807608310,-171805503829⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132666584613,2132666752185⟩,⟨-294512727280,-294511347350⟩,⟨322390524128,322392034190⟩,⟨6047260377639,6047303219652⟩,⟨-4396886455378,-4396836202498⟩,⟨2079176921529,2079237944536⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2970192062827,2970192412896⟩,⟨-615257494289,-615254587348⟩,⟨673496117117,673499298202⟩,⟨12675627351714,12675717744395⟩,⟨-9231904245045,-9231798468549⟩,⟨4394449950603,4394578077416⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136708264256,136708287687⟩,⟨684331957274,684332341498⟩,⟨131009802137,131010103734⟩,⟨-3141264812345,-3141253602251⟩,⟨-864114446579,-864103271372⟩,⟨-216499120289,-216487194007⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8843105564912,8843107080570⟩,⟨-44266703315259,-44266663287244⟩,⟨-8474516023311,-8474493609254⟩,⟨646373554702614,646375075019462⟩,⟨140738285661447,140739314278217⟩,⟨30246173380807,30247032779529⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8052664832782,8052671865077⟩,⟨-38637200389925,-38637051567947⟩,⟨-9548219310483,-9548101485389⟩,⟨538008277329891,538013208022152⟩,⟨160137967117953,160142514287581⟩,⟨19848763965361,19853623353010⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16105329665564,16105343730154⟩,⟨-77274400779850,-77274103135894⟩,⟨-19096438620966,-19096202970778⟩,⟨1076016554659782,1076026416044304⟩,⟨320275934235906,320285028575162⟩,⟨39697527930722,39707246706020⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10722856255644,10722856255645⟩,⟨-104573379102681,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974382⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9623344627868,9623344627869⟩,⟨-104573379102680,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974364⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2385198907456,2385198965312⟩,⟨-11947992171781,-11947992171683⟩,⟨0,0⟩,⟨103208265737483,103208265748560⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7542346022992,7542346023040⟩,⟨-46109836989199,-46109836988563⟩,⟨-20563996991664,-20563996991401⟩,⟨563781364745306,563781364757242⟩,⟨303172790409534,303172790415261⟩,⟨112134333527862,112134333530008⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6442834395216,6442834395264⟩,⟨-46109836989199,-46109836988563⟩,⟨-20563996991664,-20563996991400⟩,⟨563781364745310,563781364757237⟩,⟨303172790409535,303172790415260⟩,⟨112134333527861,112134333530008⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1944049211840,1944049250432⟩,⟨-7868943824214,-7868943823978⟩,⟨-3509379943517,-3509379943415⟩,⟨39896795922712,39896795931383⟩,⟨26622610581120,26622610585175⟩,⟨7935346750457,7935346752136⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101182341120,101182341120⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136918999188,136918999190⟩,⟨694201088654,694201088659⟩,⟨309598776114,309598776116⟩,⟨-1746589471214,-1746589471210⟩,⟨-1557882784976,-1557882784972⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4329248119296,4329248215744⟩,⟨-19816935995995,-19816935995661⟩,⟨-3509379943517,-3509379943415⟩,⟨143105061660195,143105061679943⟩,⟨26622610581120,26622610585175⟩,⟨7935346750457,7935346752136⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨703329960110,703331129764⟩,⟨-5248365672454,-5248345812884⟩,⟨5745167283826,5745189013894⟩,⟨67630661833710,67631200994204⟩,⟨-34420689486400,-34419984989778⟩,⟨-11040805582366,-11039886518166⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5032578079406,5032579345508⟩,⟨-25065301668449,-25065281808545⟩,⟨2235787340309,2235809070479⟩,⟨210735723493905,210736262674147⟩,⟨-7798078905280,-7797374404603⟩,⟨-3105458831909,-3104539766030⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463122007152,463122123666⟩,⟨1693876950739,1693879784797⟩,⟨205747889903,205749889618⟩,⟨-30522158416817,-30522074692510⟩,⟨1059659588361,1059741693687⟩,⟨-285779237733,-285694660876⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34441704603,34441706593⟩,⟨-703599230984,-703599220958⟩,⟨316591611439,316591629720⟩,⟨8718395631241,8718395656978⟩,⟨-6467554870054,-6467554778038⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497563711755,497563830259⟩,⟨990277719755,990280563839⟩,⟨522339501342,522341519338⟩,⟨-21803762785576,-21803679035532⟩,⟨-5407895281693,-5407813084351⟩,⟨-285779237733,-285694660876⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506844853278,506844865574⟩,⟨2538898610666,2538898733883⟩,⟨0,0⟩,⟨3504487769187,3504490687699⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229363291947,229363352139⟩,⟨1605422750859,1605424402379⟩,⟨240784254782,240785190866⟩,⟨-3891718572148,-3891664666812⟩,⟨-1286750305404,-1286707635873⟩,⟨-131736432498,-131697441678⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-703331129764,-703329960110⟩,⟨5248345812884,5248365672454⟩,⟨-5745189013894,-5745167283826⟩,⟨-67631200994204,-67630661833710⟩,⟨34419984989778,34420689486400⟩,⟨11039886518166,11040805582366⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3625916989532,3625918255634⟩,⟨-14568590183111,-14568570323207⟩,⟨-9254568957411,-9254547227241⟩,⟨75473860665991,75474399846233⟩,⟨61042595570898,61043300071575⟩,⟨18975233268623,18976152334502⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451524943260,451525100931⟩,⟨475118880804,475122153327⟩,⟨-131464600904,-131461538376⟩,⟨-14757686142018,-14757591909974⟩,⟨-7481334316717,-7481225481223⟩,⟨-3994453748402,-3994326662197⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨320570235288,320570235290⟩,⟨1959793577164,1959793577166⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-320570235290,-320570235288⟩,⟨-1959793577166,-1959793577164⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨778941392486,778941392488⟩,⟨-1959793577166,-1959793577164⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1377248190812,1377248218157⟩,⟨-9039814626281,-9039814557306⟩,⟨-4031563174331,-4031563143574⟩,⟨56316163775008,56316163782095⟩,⟨35259093538396,35259093618879⟩,⟨11201107178517,11201107179885⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1377248218157,-1377248190812⟩,⟨9039814557306,9039814626281⟩,⟨4031563143574,4031563174331⟩,⟨-56316163782095,-56316163775008⟩,⟨-35259093618879,-35259093538396⟩,⟨-11201107179885,-11201107178517⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-277736590381,-277736563036⟩,⟨9039814557306,9039814626281⟩,⟨4031563143574,4031563174331⟩,⟨-56316163782095,-56316163775008⟩,⟨-35259093618879,-35259093538396⟩,⟨-11201107179885,-11201107178517⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12009164296,-12009163113⟩,⟨421090882925,421090888893⟩,⟨63932936967,63932949171⟩,⟨-4401943205043,-4401943189659⟩,⟨1907537603327,1907537664952⟩,⟨2720448548435,2720448572957⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439515778964,439515937818⟩,⟨896209763729,896213042220⟩,⟨-67531663937,-67528589205⟩,⟨-19159629347061,-19159535099633⟩,⟨-5573796713390,-5573687816271⟩,⟨-1274005199967,-1273878089240⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101182341120,-101182341120⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4375064000,4375064002⟩,⟨26784823499,26784823502⟩,⟨40216028160,40216028160⟩,⟨-285253356750,-285253356746⟩,⟨246208790528,246208790528⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9490939076,9490939311⟩,⟨10562781697,10562783138⟩,⟨87241666214,87241668331⟩,⟨-790253549433,-790253534109⟩,⟨97094151476,97094164437⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1473990188123,1473990209194⟩,⟨-7400315750151,-7400315371999⟩,⟨-1388645081432,-1388645013866⟩,⟨108384004682055,108384012188718⟩,⟨23058282395006,23058283917488⟩,⟨5123252123039,5123252412001⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12723422582,12723423079⟩,⟨-49718902199,-49718895217⟩,⟨104968252164,104968257556⟩,⟨-266023444273,-266023293957⟩,⟨-271323432629,-271323348597⟩,⟨-176142706076,-176142686414⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12723423079,-12723422582⟩,⟨49718895217,49718902199⟩,⟨-104968257556,-104968252164⟩,⟨266023293957,266023444273⟩,⟨271323348597,271323432629⟩,⟨176142686414,176142706076⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113905764199,-113905763702⟩,⟨-824306949519,-824306942537⟩,⟨-104968257556,-104968252164⟩,⟨2465046549509,2465046699825⟩,⟨271323348597,271323432629⟩,⟨176142686414,176142706076⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨84059526875,84059528547⟩,⟨-551739726809,-551739722589⟩,⟨620940129429,620940144776⟩,⟨3437223671087,3437223671566⟩,⟨-3538719104228,-3538719065327⟩,⟨-2446563230524,-2446563230361⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨112689047302,112689051155⟩,⟨-1305421399954,-1305421343558⟩,⟨726259538464,726259578218⟩,⟨20321056600362,20321057841914⟩,⟨-6463552856630,-6463552229112⟩,⟨-4456599576094,-4456599384025⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-112689051155,-112689047302⟩,⟨1305421343558,1305421399954⟩,⟨-726259578218,-726259538464⟩,⟨-20321057841914,-20321056600362⟩,⟨6463552229112,6463552856630⟩,⟨4456599384025,4456599576094⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨986822576621,986822580474⟩,⟨1305421343558,1305421399954⟩,⟨-726259578218,-726259538464⟩,⟨-20321057841914,-20321056600362⟩,⟨6463552229112,6463552856630⟩,⟨4456599384025,4456599576094⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122886157957,122886158440⟩,⟨785612692995,785612702459⟩,⟨187428965874,187428971915⟩,⟨-2449690323838,-2449690091842⟩,⟨-684289395493,-684289270886⟩,⟨-165817653981,-165817606445⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11800259930,11800260034⟩,⟨170790939254,170790941448⟩,⟨21748726662,21748727876⟩,⟨725229087738,725229142050⟩,⟨101173565900,101173592978⟩,⟨-16453369576,-16453363280⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172846808993,172846961462⟩,⟨1672366449750,1672371868295⟩,⟨113620873204,113623700060⟩,⟨-1835548339838,-1835339554020⟩,⟨424419577798,424561517132⟩,⟨-570428272402,-570314296740⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172846961462,-172846808993⟩,⟨-1672371868295,-1672366449750⟩,⟨-113623700060,-113620873204⟩,⟨1835339554020,1835548339838⟩,⟨-424561517132,-424419577798⟩,⟨570314296740,570428272402⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56516330485,56516543146⟩,⟨-66949117436,-66942047371⟩,⟨127160554722,127164317662⟩,⟨-2056379018128,-2056116326974⟩,⟨-1711311822536,-1711127213671⟩,⟨438577864242,438730830724⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28475872971069,28475898403991⟩,⟨-251891184230671,-251890554592998⟩,⟨-85168892344028,-85168430127754⟩,⟨3592969132293920,3592991376840993⟩,⟨1339548574477087,1339567642562042⟩,⟨308325058280796,308343849278311⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13734286601,13734286710⟩,⟨175606920464,175606923272⟩,⟨41895737932,41895739450⟩,⟨575081267252,575081348313⟩,⟨114881694666,114881734982⟩,⟨26835410151,26835425043⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355699558529,355699879043⟩,⟨1401544628631,1401556653279⟩,⟨21176424665,21183215184⟩,⟨-20686332207696,-20685836177478⟩,⟨-3492745222922,-3492404825058⟩,⟨-1944173162427,-1943901942484⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355699879043,-355699558529⟩,⟨-1401556653279,-1401544628631⟩,⟨-21183215184,-21176424665⟩,⟨20685836177478,20686332207696⟩,⟨3492404825058,3492745222922⟩,⟨1943901942484,1944173162427⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83815899921,83816379289⟩,⟨-505346889550,-505331586411⟩,⟨-88714879121,-88705013870⟩,⟨1526206830417,1526797108063⟩,⟨-2081391888332,-2080942593349⟩,⟨669896742517,670295073187⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238101340308,238101340310⟩,⟨1568226933390,1568226933395⟩,⟨309598776114,309598776116⟩,⟨-3945612726766,-3945612726762⟩,⟨-1557882784976,-1557882784972⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1668460286302,-1668458821976⟩,⟨-4068880142839,-4068838626446⟩,⟨440757243722,440783086636⟩,⟨40499740397935,40501243495365⟩,⟨-7512516037979,-7511363464895⟩,⟨2112703305292,2113757878778⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186474312699,-186474148306⟩,⟨-1646888126174,-1646882423696⟩,⟨-235154249704,-235151102409⟩,⟨2429202768873,2429433791698⟩,⟨-179931978124,-179776489560⟩,⟨638013433841,638140406922⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51627027609,51627192004⟩,⟨-78661192784,-78655490301⟩,⟨74444526410,74447673707⟩,⟨-1516409957893,-1516178935064⟩,⟨-1737814763100,-1737659274532⟩,⟨290622302193,290749275274⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4308246479,4308287332⟩,⟨-31079154640,-31077702155⟩,⟨5133386397,5134252936⟩,⟨-16777241526,-16717321291⟩,⟨-290486270764,-290443284579⟩,⟨47345720238,47381065632⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2424121684,2424137124⟩,⟨-7387018748,-7386459708⟩,⟨6991012232,6991330056⟩,⟨-131151504136,-131127723744⟩,⟨-173849256054,-173832912086⟩,⟨37372871031,37385734287⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4286095508,4286122893⟩,⟨-30409980457,-30408881254⟩,⟨4623556029,4624167503⟩,⟨-38201526141,-38150913254⟩,⟨-275147211362,-275113874671⟩,⟨38944999364,38969884508⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4286122893,-4286095508⟩,⟨30408881254,30409980457⟩,⟨-4624167503,-4623556029⟩,⟨38150913254,38201526141⟩,⟨275113874671,275147211362⟩,⟨-38969884508,-38944999364⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨22123586,22191824⟩,⟨-670273386,-667721698⟩,⟨509218894,510696907⟩,⟨21373671728,21484204850⟩,⟨-15372396093,-15296073217⟩,⟨8375835730,8436066268⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56516330485,56516543146⟩,⟨-66949117436,-66942047371⟩,⟨127160554722,127164317662⟩,⟨-2056379018128,-2056116326974⟩,⟨-1711311822536,-1711127213671⟩,⟨438577864242,438730830724⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨22123586,22191824⟩,⟨-670273386,-667721698⟩,⟨509218894,510696907⟩,⟨21373671728,21484204850⟩,⟨-15372396093,-15296073217⟩,⟨8375835730,8436066268⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112528143155,112957639885⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨117682103910,121547574477⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112957639885,-112528143155⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436798174003,437227670733⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46751054561,48334152664⟩,⟨-121547574477,-117682103910⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159279197716,161291792549⟩,⟨977964053299,981829523866⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46321557831,48763649394⟩,⟨-121547574477,-117682103910⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2124215558592,-2110409526144⟩,⟨6666692899593,6777614361854⟩,⟨2977613824718,3018202721071⟩,⟨-41778599950711,-40422304862195⟩,⟨-26194797688611,-25549502796577⟩,⟨-8285085337301,-8063747454031⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311609742499,-305721492783⟩,⟨-931097069057,-882874778361⟩,⟨-413359775584,-395640836595⟩,⟨5730750439518,6248675595463⟩,⟨3564684911062,3813344374262⟩,⟨1150434670826,1232270975384⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305721492783,311609742499⟩,⟨882874778361,931097069057⟩,⟨395640836595,413359775584⟩,⟨-6248675595463,-5730750439518⟩,⟨-3813344374262,-3564684911062⟩,⟨-1232270975384,-1150434670826⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161291792549,-159279197716⟩,⟨-981829523866,-977964053299⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938219835227,940232430060⟩,⟨-981829523866,-977964053299⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-174423333888,-172067274688⟩,⟨-1150618370506,-1143635141451⟩,⟨-512392607688,-510793561201⟩,⟨-1204100621677,-1189529336226⟩,⟨749564081178,757239749660⟩,⟨-238784363695,-237296319178⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149155744185,-146826032601⟩,⟨-830889891567,-820116106396⟩,⟨-369809163461,-366502665953⟩,⟨1004749413642,1039900012893⟩,⟨1373838029387,1390577181847⟩,⟨201648242284,205025880171⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146826032601,149155744185⟩,⟨820116106396,830889891567⟩,⟨366502665953,369809163461⟩,⟨-1039900012893,-1004749413642⟩,⟨-1390577181847,-1373838029387⟩,⟨-205025880171,-201648242284⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨452547525384,460765486684⟩,⟨1702990884757,1761986960624⟩,⟨762143502548,783168939045⟩,⟨-7288575608356,-6735499853160⟩,⟨-5203921556109,-4938522940449⟩,⟨-1437296855555,-1352082913110⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨815133863616,825235474794⟩,⟨4081183092110,4154180814737⟩,⟨762143502548,783168939045⟩,⟨-19339907119804,-18579918912237⟩,⟨-5203921556109,-4938522940449⟩,⟨-1437296855555,-1352082913110⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92643115662,97527298788⟩,⟨-243095148954,-235364207820⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12395768514439,13049278524109⟩,⟨29914908676624,34241252400602⟩,⟨-123171713582230,-111034533300060⟩,⟨144388266058433,179697806862737⟩,⟨-366907168059407,-226178679410226⟩,⟨1989173574966567,2325227559324947⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9189726080571,9794100659349⟩,⟨68188506669806,75002534388993⟩,⟨-83853877283086,-73021709346583⟩,⟨99590005922808,184144790821821⟩,⟨-781774678258884,-611106099876134⟩,⟨1282167917527008,1576019409089165⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨85187076096,90736426240⟩,⟨-733722890948,-587621856269⟩,⟨629272504851,820312403555⟩,⟨6257124751050,10965478085679⟩,⟨-7952794470024,-981915909833⟩,⟨-6176219462682,3729880382244⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1184698703872,1190248054016⟩,⟨-733722890948,-587621856269⟩,⟨629272504851,820312403555⟩,⟨6257124751050,10965478085679⟩,⟨-7952794470024,-981915909833⟩,⟨-6176219462682,3729880382244⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨82048171648,87186464704⟩,⟨-680963731561,-542825557683⟩,⟨581301043751,761326929093⟩,⟨5358380818184,9909001872689⟩,⟨-7093953387633,-435546491681⟩,⟨-6259271672858,3154351014370⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨88405033790,94381466580⟩,⟨-795340803308,-628731898852⟩,⟨673296428050,889202087130⟩,⟨6820668913335,12505087233688⟩,⟨-9326091676497,-1163904167735⟩,⟨-6600180441290,4846430862951⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-90736426240,-85187076096⟩,⟨587621856269,733722890948⟩,⟨-820312403555,-629272504851⟩,⟨-10965478085679,-6257124751050⟩,⟨981915909833,7952794470024⟩,⟨-3729880382244,6176219462682⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1008775201536,1014324551680⟩,⟨587621856269,733722890948⟩,⟨-820312403555,-629272504851⟩,⟨-10965478085679,-6257124751050⟩,⟨981915909833,7952794470024⟩,⟨-3729880382244,6176219462682⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-94700038528,-88668116096⟩,⟨636972715126,799719153420⟩,⟨-894097143492,-682121353542⟩,⟨-12533459277426,-7151636522510⟩,⟨1459549977248,9318438359417⟩,⟨-4792431276981,6308574256619⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-87362945237,-81350841978⟩,⟨521212035011,690371460943⟩,⟨-774078468309,-555176929691⟩,⟨-10376961490886,-4549672556756⟩,⟨-539158647453,7788182615921⟩,⟨-4172296487054,7475172900803⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1042088553,13030624602⟩,⟨-274128768297,61639562091⟩,⟨-100782040259,334025157439⟩,⟨-3556292577551,7955414676932⟩,⟨-9865250323950,6624278448186⟩,⟨-10772476928344,12321603763754⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨521044276,6515312301⟩,⟨-137064384149,30819781046⟩,⟨-50391020130,167012578720⟩,⟨-1778146288776,3977707338466⟩,⟨-4932625161975,3312139224093⟩,⟨-5386238464172,6160801881877⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6515312301,-521044276⟩,⟨-30819781046,137064384149⟩,⟨-167012578720,50391020130⟩,⟨-3977707338466,1778146288776⟩,⟨-3312139224093,4932625161975⟩,⟨-6160801881877,5386238464172⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755608071315,761602358604⟩,⟨-30819781046,137064384149⟩,⟨-167012578720,50391020130⟩,⟨-3977707338466,1778146288776⟩,⟨-3312139224093,4932625161975⟩,⟨-6160801881877,5386238464172⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6600055652,7487959963⟩,⟨-121099934360,-91054585546⟩,⟨97508536338,135391412004⟩,⟨1597664974314,2789088419758⟩,⟨-2407414534990,-824767671890⟩,⟨-299085870859,1839632124055⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7487959963,-6600055652⟩,⟨91054585546,121099934360⟩,⟨-135391412004,-97508536338⟩,⟨-2789088419758,-1597664974314⟩,⟨824767671890,2407414534990⟩,⟨-1839632124055,299085870859⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092023667813,1092911572124⟩,⟨91054585546,121099934360⟩,⟨-135391412004,-97508536338⟩,⟨-2789088419758,-1597664974314⟩,⟨824767671890,2407414534990⟩,⟨-1839632124055,299085870859⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7513573824,-6619944384⟩,⟨91604461077,121930311473⟩,⟨-136319785173,-98097387058⟩,⟨-2821734539241,-1614945131704⟩,⟨837921279027,2439039253124⟩,⟨-1869147619773,292384533936⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3756786912,-3309972192⟩,⟨45802230538,60965155737⟩,⟨-68159892587,-49048693529⟩,⟨-1410867269621,-807472565852⟩,⟨418960639513,1219519626562⟩,⟨-934573809887,146192266968⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3309972192,3756786912⟩,⟨-60965155737,-45802230538⟩,⟨49048693529,68159892587⟩,⟨807472565852,1410867269621⟩,⟨-1219519626562,-418960639513⟩,⟨-146192266968,934573809887⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765433355808,765880189792⟩,⟨-60965155737,-45802230538⟩,⟨49048693529,68159892587⟩,⟨807472565852,1410867269621⟩,⟨-1219519626562,-418960639513⟩,⟨-146192266968,934573809887⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273005916953,273227893031⟩,⟨22763646386,30274983590⟩,⟨-33847853001,-24377134084⟩,⟨-697272104940,-399416243578⟩,⟨206191917972,601853633748⟩,⟨-459908031014,74771467715⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530866711616,1531760379584⟩,⟨-121930311474,-91604461076⟩,⟨98097387058,136319785174⟩,⟨1614945131704,2821734539242⟩,⟨-2439039253124,-837921279026⟩,⟨-292384533936,1869147619774⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1191853058877,1198409534428⟩,⟨-871651589772,-690468258602⟩,⟨739408662179,974518608441⟩,⟨8152264223753,14294795227111⟩,⟨-10865411761590,-2010485557641⟩,⟨-6419817199428,6015952421433⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1284194489978,1297307441080⟩,⟨-1743303179544,-1380936517205⟩,⟨1478817324358,1949037216883⟩,⟨16304528447511,28589590454213⟩,⟨-21730823523173,-4020971115283⟩,⟨-12835003997353,12031904842862⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨170716287808,181886503168⟩,⟨-1492594876872,-1170390078563⟩,⟨1253347350057,1668741845302⟩,⟨11792427273167,23232220336853⟩,⟨-17271522919809,-1142579111676⟩,⟨-13521842863389,8872863225746⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨58542393407,62850700702⟩,⟨-510773644326,-392515253310⟩,⟨418667022305,572366991421⟩,⟨3788842572456,7783367409998⟩,⟨-5838640932691,-54022385625⟩,⟨-5035724311999,3103274578485⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380110277853,380641414397⟩,⟨1394570414,19431773093⟩,⟨-22797060463,-65279356⟩,⟨-577117210911,141292774387⟩,⟨-314953562578,637912527862⟩,⟨-721761147745,564298326362⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176022823290,3180460750610⟩,⟨-162589635793,-11636115504⟩,⟨544682519,190747686281⟩,⟨-1182140394474,4845481837608⟩,⟨-5357047697330,2635277142797⟩,⟨-4721599788760,6062003868480⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨169104148508,181802703748⟩,⟨-1486764086406,-1134429666356⟩,⟨1209380484595,1666539334929⟩,⟨10885093468005,22942303517463⟩,⟨-17368395089165,-10034244742⟩,⟨-14835880664712,9521681517677⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨339820436316,363689206916⟩,⟨-2979358963278,-2304819744919⟩,⟨2462727834652,3335281180231⟩,⟨22677520741172,46174523854316⟩,⟨-34639918008974,-1152613356418⟩,⟨-28357723528101,18394544743423⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519270140499,527541626645⟩,⟨-42696079502,189881681306⟩,⟨-231370311430,69809029418⟩,⟨-5518187363343,2497521659967⟩,⟨-4630100231848,6845959017686⟩,⟨-8550154558809,7512544688812⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356853624320,365414004696⟩,⟨-44361652071,197288959051⟩,⟨-240396059185,72532277214⟩,⟨-5741435356394,2630455677635⟩,⟨-4853983982317,7126073159821⟩,⟨-8899601468024,7858325497827⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713707248640,730828009392⟩,⟨-88723304142,394577918102⟩,⟨-480792118370,145064554428⟩,⟨-11482870712788,5260911355270⟩,⟨-9707967964634,14252146319642⟩,⟨-17799202936048,15716650995654⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523378751653,1525160323932⟩,⟨-30875725928,29495473284⟩,⟨-37294024946,38811248836⟩,⟨-1174143288054,1224069564928⟩,⟨-1614271581234,1569493255964⟩,⟨-2132016657991,2168233490633⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988844892598,1013749973521⟩,⟨-143592941281,566934162103⟩,⟨-691707628914,227019927981⟩,⟨-16730774748111,8132332473142⟩,⟨-14565429448158,20840158501454⟩,⟨-26140783930637,23274769442677⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67786668925,67896945921⟩,⟨11304310018,15046625738⟩,⟨-16822336984,-12105559732⟩,⟨-345600718913,-196680818029⟩,⟨100529851696,298111058878⟩,⟨-227492742192,39245292529⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50254320142,50959868899⟩,⟨259992096277,267821814723⟩,⟨34361419267,39387602944⟩,⟨-1369746936113,-1177594821565⟩,⟨-302545792855,-114937533098⟩,⟨-283464588945,-70684961033⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131448935628,2133938196915⟩,⟨-339729049640,-255084560370⟩,⟨273164958968,379821805624⟩,⟨4512289016019,7889117423058⟩,⟨-6826021865076,-2349646731616⟩,⟨-797153820422,5241726014708⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2967648672949,2972848944879⟩,⟨-709929051527,-532737152003⟩,⟨570497571695,793710559934⟩,⟨9455670712890,16542336335124⟩,⟨-14327463260310,-4941310764032⟩,⟨-1629255735944,11024229193362⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135639462750,137784802508⟩,⟨668830860467,699784737597⟩,⟨118818741517,143282504662⟩,⟨-3617179940576,-2663643787304⟩,⟨-1372596793302,-359385951685⟩,⟨-806283287930,377030897995⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8774014242568,8912788322104⟩,⟨-45982438375895,-42590557077335⟩,⟨-9415008054604,-7566272269349⟩,⟨583102090652362,712143607183443⟩,⟨96341323585131,187339451491811⟩,⟨-11724924121911,72871448644274⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7890902608183,8217592881494⟩,⟨-43559802339752,-33708138889262⟩,⟨-14287714150988,-4964466940288⟩,⟨341371232994702,734528683070300⟩,⟨-45773579831623,371817457045144⟩,⟨-226598971645894,267701933096067⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15781805216366,16435185762988⟩,⟨-87119604679504,-67416277778524⟩,⟨-28575428301976,-9928933880576⟩,⟨682742465989404,1469057366140600⟩,⟨-91547159663246,743634914090288⟩,⟨-453197943291788,535403866192134⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10702470597344,10743319721800⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803854,2051378711294242⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9602958969568,9643808094024⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803861,2051378711294240⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2382867281216,2387534528576⟩,⟨-12019099426619,-11877349255562⟩,⟨0,0⟩,⟨99839973091184,106573343585493⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7495271771174,7589979337856⟩,⟨-46786183671818,-45446245255706⟩,⟨-20834792203812,-20298125351357⟩,⟨551110425584575,576799194078273⟩,⟨297242727568732,309253810048782⟩,⟨109939680736863,114384650300937⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6395760143398,6490467710080⟩,⟨-46786183671818,-45446245255705⟩,⟨-20834792203812,-20298125351356⟩,⟨551110425584577,576799194078268⟩,⟨297242727568732,309253810048781⟩,⟨109939680736862,114384650300937⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1935986192320,1952148283456⟩,⟨-8043133546782,-7698778782890⟩,⟨-3581762883038,-3438584989985⟩,⟨34523318793962,45252200047900⟩,⟨24152860460064,29087653395995⟩,⟨6956298472664,8910416205693⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100967634698,101397131429⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135913890186,137926485020⟩,⟨690474034001,697926797626⟩,⟨308583799847,310613152237⟩,⟨-1753486165281,-1739706366688⟩,⟨-1561814525546,-1553951044400⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4318853473536,4339682812032⟩,⟨-20062232973401,-19576128038452⟩,⟨-3581762883038,-3438584989985⟩,⟨134363291885146,151825543633393⟩,⟨24152860460064,29087653395995⟩,⟨6956298472664,8910416205693⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨679640872632,727378413832⟩,⟨-5958717926556,-4609639489838⟩,⟨4925455669304,6670562360462⟩,⟨45355041482344,92349047708632⟩,⟨-69279836017948,-2305226712836⟩,⟨-56715447056202,36789089486846⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4998494346168,5067061225864⟩,⟨-26020950899957,-24185767528290⟩,⟨1343692786266,3231977370477⟩,⟨179718333367490,244174591342025⟩,⟨-45126975557884,26782426683159⟩,⟨-49759148583538,45699505692539⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459009380559,467285165613⟩,⟨1571803866708,1808929495206⟩,⟨123390675426,298053450215⟩,⟨-35020247605629,-25911866535271⟩,⟨-3094010717826,5040311510576⟩,⟨-4588796335812,4214415443991⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33440099137,35450262758⟩,⟨-724080144224,-683303003986⟩,⟨315329944105,317856354168⟩,⟨8383731201457,9060451982784⟩,⟨-6499332721185,-6435979379349⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨492449479696,502735428371⟩,⟨847723722484,1125626491220⟩,⟨438720619531,615909804383⟩,⟨-26636516404172,-16851414552487⟩,⟨-9593343439011,-1395667868773⟩,⟨-4588796335812,4214415443991⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506349041299,507340811276⟩,⟨2518951804351,2559009350623⟩,⟨0,0⟩,⟨2371496934072,4641016220299⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226783706177,231974081623⟩,⟨1518583848881,1689460004255⟩,⟨202040396377,284195429985⟩,⟨-7344350715440,-398828790741⟩,⟨-3421499556703,790736395386⟩,⟨-2117379750227,1944631504020⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-727378413832,-679640872632⟩,⟨4609639489838,5958717926556⟩,⟨-6670562360462,-4925455669304⟩,⟨-92349047708632,-45355041482344⟩,⟨2305226712836,69279836017948⟩,⟨-36789089486846,56715447056202⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3591475059704,3660041939400⟩,⟨-15452593483563,-13617410111896⟩,⟨-10252325243500,-8364040659289⟩,⟨42014244176514,106470502151049⟩,⟨26458087172900,98367489413943⟩,⟨-29832791014182,65625863261895⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443952873747,459128131959⟩,⟨316957420051,639962461153⟩,⟨-278119990198,61718710⟩,⟨-20260878687470,-9429592039279⟩,⟨-12801534838307,-1810585141197⟩,⟨-10692440030278,2403893677567⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨318558395432,322583585098⟩,⟨1955928106598,1963659047732⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-322583585098,-318558395432⟩,⟨-1963659047732,-1955928106598⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨776928042678,780953232344⟩,⟨-1963659047732,-1955928106598⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1367990956215,1386557880305⟩,⟨-9199234028400,-8883986937094⟩,⟨-4096596780801,-3967946734748⟩,⟨51785400604067,60870475700173⟩,⟨33172512593707,37358075677482⟩,⟨10379530009020,12026068095330⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1386557880305,-1367990956215⟩,⟨8883986937094,9199234028400⟩,⟨3967946734748,4096596780801⟩,⟨-60870475700173,-51785400604067⟩,⟨-37358075677482,-33172512593707⟩,⟨-12026068095330,-10379530009020⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-287046252529,-268479328439⟩,⟨8883986937094,9199234028400⟩,⟨3967946734748,4096596780801⟩,⟨-60870475700173,-51785400604067⟩,⟨-37358075677482,-33172512593707⟩,⟨-12026068095330,-10379530009020⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12730581892,-11310822391⟩,⟨403011042092,439720678162⟩,⟨53020730553,75027609191⟩,⟨-4733515835948,-4083406544500⟩,⟨1688074834178,2122953063621⟩,⟨2619298182588,2820793212990⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨431222291855,447817309568⟩,⟨719968462143,1079683139315⟩,⟨-225099259645,75089327901⟩,⟨-24994394523418,-13512998583779⟩,⟨-11113460004129,312367922424⟩,⟨-8073141847690,5224686890557⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101397131429,-100967634698⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4253686829,4496991248⟩,⟨25594789231,27975647758⟩,⟨40110970503,40321203045⟩,⟨-290863909441,-279647333906⟩,⟨245652667759,246764997182⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9218612075,9764991664⟩,⟨6311166450,14797752457⟩,⟨86928702539,87555476515⟩,⟨-856965773181,-723138864948⟩,⟨91616271808,102543659135⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1464946498957,1483100964855⟩,⟨-7558353111708,-7244859273505⟩,⟨-1424942161022,-1352946510253⟩,⟨104641383147536,112227659735718⟩,⟨22148728810453,23992225975002⟩,⟨4899217299205,5353227768991⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12282519932,13171728423⟩,⟨-58718554951,-40782639400⟩,⟨103165211947,106757691049⟩,⟨-482042854386,-49935453933⟩,⟨-313291524653,-229154830682⟩,⟨-185863424193,-166388003837⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13171728423,-12282519932⟩,⟨40782639400,58718554951⟩,⟨-106757691049,-103165211947⟩,⟨49935453933,482042854386⟩,⟨229154830682,313291524653⟩,⟨166388003837,185863424193⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114568859852,-113250154630⟩,⟨-833672702066,-814877793055⟩,⟨-106757691049,-103165211947⟩,⟨2248958709485,2681066109938⟩,⟨229154830682,313291524653⟩,⟨166388003837,185863424193⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨81561571612,86578324463⟩,⟨-572519123288,-531554501205⟩,⟨610248575193,631419091798⟩,⟨3102460029775,3785234334878⟩,⟨-3764973593368,-3308448068680⟩,⟨-2555557423827,-2336883769884⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨108669463572,116783118344⟩,⟨-1367419110701,-1245644865775⟩,⟨700867903073,751342504911⟩,⟨18900872181616,21814203888986⟩,⟨-7121956958017,-5797893302318⟩,⟨-4720307687225,-4193865212836⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-116783118344,-108669463572⟩,⟨1245644865775,1367419110701⟩,⟨-751342504911,-700867903073⟩,⟨-21814203888986,-18900872181616⟩,⟨5797893302318,7121956958017⟩,⟨4193865212836,4720307687225⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨982728509432,990842164204⟩,⟨1245644865775,1367419110701⟩,⟨-751342504911,-700867903073⟩,⟨-21814203888986,-18900872181616⟩,⟨5797893302318,7121956958017⟩,⟨4193865212836,4720307687225⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121477982896,124294617234⟩,⟨771114134960,800481402716⟩,⟨181557031200,193277560157⟩,⟨-2752143356719,-2155350765685⟩,⟨-818084748434,-549333191740⟩,⟨-219458657071,-111461527725⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11664812994,11938048964⟩,⟨167865502712,173737009328⟩,⟨21252119414,22248253926⟩,⟨649122976411,800928778636⟩,⟨87627245102,114685740764⟩,⟨-19374237386,-13544672699⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167430522703,178446546098⟩,⟨1463543012467,1881746128833⟩,⟨-5218728993,227223635403⟩,⟨-10971601639263,7337218728199⟩,⟨-6014349220118,6969428074190⟩,⟨-6366667728499,5234957286025⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178446546098,-167430522703⟩,⟨-1881746128833,-1463543012467⟩,⟨-227223635403,5218728993⟩,⟨-7337218728199,10971601639263⟩,⟨-6969428074190,6014349220118⟩,⟨-5234957286025,6366667728499⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48337160079,64543558920⟩,⟨-363162279952,225916991788⟩,⟨-25183239026,289414158978⟩,⟨-14681569443639,10572772848522⟩,⟨-10390927630893,6805085615504⟩,⟨-7352337036252,8311299232519⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27788116302661,29180154956974⟩,⟨-274904578589797,-229208681114226⟩,⟨-104273941952150,-66838181218477⟩,⟨2641778608140381,4559274529620877⟩,⟨464496565612813,2247929260599606⟩,⟨-642688677111222,1269957375213060⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13421322663,14050921776⟩,⟨170390903254,180981313960⟩,⟨40118142224,43698237932⟩,⟨459368318912,689292960753⟩,⟨69699421850,160040516490⟩,⟨10341729282,43321222079⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339199027707,372900171635⟩,⟨793242640527,2005234927561⟩,⟨-318630008841,343847712304⟩,⟨-46642562954599,5516573545825⟩,⟨-20657814081062,14253092314587⟩,⟨-16240088555987,12501317897598⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372900171635,-339199027707⟩,⟨-2005234927561,-793242640527⟩,⟨-343847712304,318630008841⟩,⟨-5516573545825,46642562954599⟩,⟨-14253092314587,20657814081062⟩,⟨-12501317897598,16240088555987⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58322120220,108618281861⟩,⟨-1285266465418,286440498788⟩,⟨-568946971949,393719336742⟩,⟨-30510968069243,33129564370820⟩,⟨-25366552318716,20970182003486⟩,⟨-20574459745288,21464775446544⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨236881524884,239323616449⟩,⟨1564070382007,1572382139092⟩,⟨308583799847,310613152237⟩,⟨-3952509420833,-3938729622240⟩,⟨-1561814525546,-1553951044400⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1712542593234,-1625532496376⟩,⟨-5517596801829,-2618479653617⟩,⟨-573099156766,1496774493979⟩,⟨-20867031615924,101864863778323⟩,⟨-60513270943886,44347598738421⟩,⟨-51537487076254,55550449402181⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-193594884080,-179594652574⟩,⟨-1870526902875,-1429324321514⟩,⟨-365825321218,-99212994742⟩,⟨-7206412421421,12129133781828⟩,⟨-7415744912332,6944819271058⟩,⟨-5862768655269,7147755230029⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43286640804,59728963875⟩,⟨-306456520868,143057817578⟩,⟨-57241521371,211400157495⟩,⟨-11158921842254,8190404159588⟩,⟨-8977559437878,5390868226658⟩,⟨-6210501287149,6800705430841⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2563979852,6376113084⟩,⟨-111323729220,39132469013⟩,⟨-35886134867,51702696423⟩,⟨-3769583036321,3838265011956⟩,⟨-2983916233948,2166568174961⟩,⟨-2233600471426,2288350463316⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1704150483,3244667029⟩,⟨-33295383154,15542710060⟩,⟨-6219082502,22967856004⟩,⟨-1292122470948,1060689016145⟩,⟨-1093222236030,640708856250⟩,⟨-696759659440,820162523438⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3000615656,5760804171⟩,⟨-82850251875,15663133293⟩,⟨-21611594243,35449188001⟩,⟨-2468010205723,2503883470155⟩,⟨-2122192779828,1377352894006⟩,⟨-1375933081393,1522985943400⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5760804171,-3000615656⟩,⟨-15663133293,82850251875⟩,⟨-35449188001,21611594243⟩,⟨-2503883470155,2468010205723⟩,⟨-1377352894006,2122192779828⟩,⟨-1522985943400,1375933081393⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3196824319,3375497428⟩,⟨-126986862513,121982720888⟩,⟨-71335322868,73314290666⟩,⟨-6273466506476,6306275217679⟩,⟨-4361269127954,4288760954789⟩,⟨-3756586414826,3664283544709⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48337160079,64543558920⟩,⟨-363162279952,225916991788⟩,⟨-25183239026,289414158978⟩,⟨-14681569443639,10572772848522⟩,⟨-10390927630893,6805085615504⟩,⟨-7352337036252,8311299232519⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3196824319,3375497428⟩,⟨-126986862513,121982720888⟩,⟨-71335322868,73314290666⟩,⟨-6273466506476,6306275217679⟩,⟨-4361269127954,4288760954789⟩,⟨-3756586414826,3664283544709⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (105/1024) u, BivariateJet2.affineZ (557/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000044

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000045Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2504150381952,-2504150324096⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-118951416704,-118951416640⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2106804573312,-2106804534464⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-175044269696,-175044269632⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨86936010368,86936010432⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-94404602304,-94404602240⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨86936133568,86936133632⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-94404747648,-94404747584⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨-7468614016,-7468613952⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-7468591872,-7468591808⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨181340612608,181340612672⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨181340881152,181340881216⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨1931760264832,1931760303424⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨1931760264832,1931760303424⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨-2506246686976,-2506246629120⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2113665886400,-2113665847488⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2099980713600,-2099980674816⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-176226191360,-176226191296⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-173864501440,-173864501376⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨84378781440,84378781504⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-91396463232,-91396463168⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨89515317888,89515317952⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-97454197696,-97454197632⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨-7938879744,-7938879680⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-7017681792,-7017681728⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨175775244608,175775244672⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨186969515520,186969515584⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨1923754483520,1923754522112⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨1939801346112,1939801384704⟩



end LaneCBRB2Cell000045Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000045
open Set LaneCBRB2Cell000045Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112742891520,112742891520⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨123480309760,123480309760⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112742891520,-112742891520⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437012922368,437012922368⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49078599680,49078599680⟩,⟨-123480309760,-123480309760⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161821491200,161821491200⟩,⟨976031318016,976031318016⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49078599680,49078599680⟩,⟨-123480309760,-123480309760⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2106804573312,-2106804534464⟩,⟨6631738314076,6631738314078⟩,⟨2969326175829,2969326175831⟩,⟨-39999534298118,-39999534298104⟩,⟨-25380319574202,-25380319574194⟩,⟨-8018921961112,-8018921961108⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310070625092,-310070619374⟩,⟨-894169226068,-894169191580⟩,⟨-400359598471,-400359583028⟩,⟨5886963015129,5886963015137⟩,⟨3643149834252,3643149873107⟩,⟨1180191165587,1180191165591⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨310070619374,310070625092⟩,⟨894169191580,894169226068⟩,⟨400359583028,400359598471⟩,⟨-5886963015137,-5886963015129⟩,⟨-3643149873107,-3643149834252⟩,⟨-1180191165591,-1180191165587⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161821491200,-161821491200⟩,⟨-976031318016,-976031318016⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937690136576,937690136576⟩,⟨-976031318016,-976031318016⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175044269696,-175044269632⟩,⟨-1144469522898,-1144469522896⟩,⟨-512430248426,-512430248425⟩,⟨-1191265699928,-1191265699924⟩,⟨755876404373,755876404376⟩,⟨-238819447534,-238819447532⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149281991215,-149281991160⟩,⟨-820645340386,-820645340325⟩,⟨-367439662858,-367439662829⟩,⟨1015940230770,1015940230780⟩,⟨1379349287588,1379349287658⟩,⟨203671006940,203671006945⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149281991160,149281991215⟩,⟨820645340325,820645340386⟩,⟨367439662829,367439662858⟩,⟨-1015940230780,-1015940230770⟩,⟨-1379349287658,-1379349287588⟩,⟨-203671006945,-203671006940⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨459352610534,459352616307⟩,⟨1714814531905,1714814566454⟩,⟨767799245857,767799261329⟩,⟨-6902903245917,-6902903245899⟩,⟨-5022499160765,-5022499121840⟩,⟨-1383862172536,-1383862172527⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨822880087019,822880098785⟩,⟨4100013439295,4100013531768⟩,⟨767799245857,767799261329⟩,⟨-18850895417609,-18850895417579⟩,⟨-5022499160765,-5022499121840⟩,⟨-1383862172536,-1383862172527⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98157199360,98157199360⟩,⟨-246960619520,-246960619520⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12316221606739,12316221606740⟩,⟨30987250430713,30987250430720⟩,⟨-109667921089589,-109667921089570⟩,⟨155926016909340,155926016909380⟩,⟨-275921256009273,-275921256009088⟩,⟨1953042629490765,1953042629491252⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9217522808738,9217522940537⟩,⟨69117473176329,69117474543777⟩,⟨-73475497700461,-73475496353566⟩,⟨136636022343351,136636029224657⟩,⟨-650067064308804,-650067051260374⟩,⟨1293001367329353,1293001391316011⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨90465334272,90465467648⟩,⟨-671746834090,-671744813238⟩,⟨714099941844,714102089077⟩,⟨8599237645093,8599287394784⟩,⟨-4235246179783,-4235178590179⟩,⟨-1348045297500,-1347955880347⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1189976962048,1189977095424⟩,⟨-671746834090,-671744813238⟩,⟨714099941844,714102089077⟩,⟨8599237645093,8599287394784⟩,⟨-4235246179783,-4235178590179⟩,⟨-1348045297500,-1347955880347⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨86936010368,86936133632⟩,⟨-620678785019,-620676848229⟩,⟨659812018626,659814076576⟩,⟨7595123267484,7595172312281⟩,⟨-3540805665997,-3540740452150⟩,⟨-1641515888255,-1641430659303⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨94088909018,94089052970⟩,⟨-724860556443,-724858149912⟩,⟨770562202337,770564759485⟩,⟨9658359005952,9658422553143⟩,⟨-4973234903257,-4973153135255⟩,⟨-1026107117166,-1026002205242⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-90465467648,-90465334272⟩,⟨671744813238,671746834090⟩,⟨-714102089077,-714099941844⟩,⟨-8599287394784,-8599237645093⟩,⟨4235178590179,4235246179783⟩,⟨1347955880347,1348045297500⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1009046160128,1009046293504⟩,⟨671744813238,671746834090⟩,⟨-714102089077,-714099941844⟩,⟨-8599287394784,-8599237645093⟩,⟨4235178590179,4235246179783⟩,⟨1347955880347,1348045297500⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-94404747648,-94404602240⟩,⟨731969621025,731971919809⟩,⟨-778124511430,-778122068834⟩,⟨-9857543385006,-9857484875757⟩,⟨5132893904626,5132971416882⟩,⟨918127104287,918228189482⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-86637338158,-86637193261⟩,⟨614068126260,614070587046⟩,⟨-652789215723,-652786600906⟩,⟨-7413760989496,-7413695190184⟩,⟨3396138876100,3396222841763⟩,⟨1737575622578,1737682569743⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7451570860,7451859709⟩,⟨-110792430183,-110787562866⟩,⟨117772986614,117778158579⟩,⟨2244598016456,2244727362959⟩,⟨-1577096027157,-1576930293492⟩,⟨711468505412,711680364501⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3725785430,3725929855⟩,⟨-55396215092,-55393781433⟩,⟨58886493307,58889079290⟩,⟨1122299008228,1122363681480⟩,⟨-788548013579,-788465146746⟩,⟨355734252706,355840182251⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3725929855,-3725785430⟩,⟨55393781433,55396215092⟩,⟨-58889079290,-58886493307⟩,⟨-1122363681480,-1122299008228⟩,⟨788465146746,788548013579⟩,⟨-355840182251,-355734252706⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758397453761,758397617450⟩,⟨55393781433,55396215092⟩,⟨-58889079290,-58886493307⟩,⟨-1122363681480,-1122299008228⟩,⟨788465146746,788548013579⟩,⟨-355840182251,-355734252706⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7443283452,7443305401⟩,⟨-110539788670,-110539293154⟩,⟨117509061860,117509588448⟩,⟨2235854485042,2235869696449⟩,⟨-1569495623360,-1569478224936⟩,⟨705744566752,705765186150⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7443305401,-7443283452⟩,⟨110539293154,110539788670⟩,⟨-117509588448,-117509061860⟩,⟨-2235869696449,-2235854485042⟩,⟨1569478224936,1569495623360⟩,⟨-705765186150,-705744566752⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092068322375,1092068344324⟩,⟨110539293154,110539788670⟩,⟨-117509588448,-117509061860⟩,⟨-2235869696449,-2235854485042⟩,⟨1569478224936,1569495623360⟩,⟨-705765186150,-705744566752⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7468614016,-7468591808⟩,⟨111292703227,111293204358⟩,⟨-118310508809,-118309976253⟩,⟨-2262374071392,-2262358609611⟩,⟨1592150773385,1592168429984⟩,⟨-723306071304,-723285182475⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3734307008,-3734295904⟩,⟨55646351613,55646602179⟩,⟨-59155254405,-59154988126⟩,⟨-1131187035696,-1131179304805⟩,⟨796075386692,796084214992⟩,⟨-361653035652,-361642591237⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3734295904,3734307008⟩,⟨-55646602179,-55646351613⟩,⟨59154988126,59155254405⟩,⟨1131179304805,1131187035696⟩,⟨-796084214992,-796075386692⟩,⟨361642591237,361653035652⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765857679520,765857709888⟩,⟨-55646602179,-55646351613⟩,⟨59154988126,59155254405⟩,⟨1131179304805,1131187035696⟩,⟨-796084214992,-796075386692⟩,⟨361642591237,361653035652⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273017080593,273017086081⟩,⟨27634823288,27634947168⟩,⟨-29377397112,-29377265465⟩,⟨-558967424113,-558963621260⟩,⟨392369556234,392373905840⟩,⟨-176441296538,-176436141688⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531715359040,1531715419776⟩,⟨-111293204358,-111292703226⟩,⟨118309976252,118310508810⟩,⟨2262358609610,2262374071392⟩,⟨-1592168429984,-1592150773384⟩,⟨723285182474,723306071304⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1198087567832,1198087726197⟩,⟨-797596451815,-797593841508⟩,⟨847884054497,847886828158⟩,⟨11272226894681,11272295474645⟩,⟨-6157624195906,-6157535375836⟩,⟨-400505738303,-400391452985⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1296663507888,1296663824618⟩,⟨-1595192903630,-1595187683016⟩,⟨1695768108994,1695773656315⟩,⟨22544453789371,22544590949281⟩,⟨-12315248391808,-12315070751676⟩,⟨-801011331029,-800783051549⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨181340612608,181340881216⟩,⟨-1352650965665,-1352646208416⟩,⟨1437933810175,1437938865290⟩,⟨17452595580309,17452728260218⟩,⟨-8673788530823,-8673622908849⟩,⟨-2559754399974,-2559547441385⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62399230196,62399335662⟩,⟨-458785490582,-458783789720⟩,⟨487711212852,487713020149⟩,⟨5771362625446,5771406855560⟩,⟨-2784471195312,-2784413653627⟩,⟨-1035597251234,-1035523026450⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380336546754,380336569481⟩,⟨10862765447,10863064542⟩,⟨-11548006868,-11547689019⟩,⟨-222523925426,-222514696001⟩,⟨157204559374,157215086076⟩,⟨-72523066809,-72510628650⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178568448635,3178568638571⟩,⟨-90785375654,-90782865191⟩,⟨96506943890,96509611769⟩,⟨1864797011174,1864874652554⟩,⟨-1319399165496,-1319310729660⟩,⟨611849817879,611954162801⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨180389383167,180389698838⟩,⟨-1331451239207,-1331446091763⟩,⟨1415396975265,1415402444881⟩,⟨16865972119112,16866107941627⟩,⟨-8205021792630,-8204847294134⟩,⟨-2873460243815,-2873236824630⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨361729995775,361730580054⟩,⟨-2684102204872,-2684092300179⟩,⟨2853330785440,2853341310171⟩,⟨34318567699421,34318836201845⟩,⟨-16878810323453,-16878470202983⟩,⟨-5433214643789,-5432784266015⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523111064350,523111290162⟩,⟨76416659418,76420033188⟩,⟨-81238499530,-81234914586⟩,⟨-1542738520449,-1542648477973⟩,⟨1081767054652,1081882126900⟩,⟨-484580100091,-484433308534⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360820285311,360820518945⟩,⟨79063556668,79067064364⟩,⟨-84052432371,-84048705109⟩,⟨-1590400930808,-1590306915444⟩,⟨1113097470024,1113217311229⟩,⟨-494838906611,-494686346780⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721640570622,721641037890⟩,⟨158127113336,158134128728⟩,⟨-168104864742,-168097410218⟩,⟨-3180801861616,-3180613830888⟩,⟨2226194940048,2226434622458⟩,⟨-989677813222,-989372693560⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524272053639,1524272136324⟩,⟨-753911204,-752914556⟩,⟨800387804,801446950⟩,⟨26488913161,26519586350⟩,⟨-22690205048,-22655150024⟩,⟨17519996324,17561504552⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000422848456,1000423550508⟩,⟨218719548244,218729940146⟩,⟨-232521387257,-232510344789⟩,⟨-4392432504214,-4392151155507⟩,⟨3071550669069,3071906444555⟩,⟨-1360753802829,-1360303150511⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67792212844,67792215571⟩,⟨13723872646,13723934444⟩,⟨-14589261548,-14589195876⟩,⟨-276202579494,-276200672903⟩,⟨193379942972,193382120210⟩,⟨-86053596388,-86051020577⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50736036432,50736039199⟩,⟨263064144070,263064206340⟩,⟨36421258220,36421310386⟩,⟨-1266643673427,-1266641733619⟩,⟨-209762976929,-209761041082⟩,⟨-170102906030,-170100881795⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133812760002,2133812929224⟩,⟨-310082245472,-310080836934⟩,⟨329632180642,329633677514⟩,⟨6325854875808,6325898407868⟩,⟨-4460009387410,-4459959801488⟩,⟨2040659225607,2040717734652⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2972586824226,2972587177838⟩,⟨-647957345048,-647954376030⟩,⟨688809460266,688812615488⟩,⟨13265778953009,13265870868939⟩,⟨-9369820608221,-9369716169784⟩,⟨4317427538661,4317550451132⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137167511103,137167534902⟩,⟨681308137546,681308529135⟩,⟨130251295719,130251595797⟩,⟨-3122353944214,-3122342523608⟩,⟨-856129832539,-856118765600⟩,⟨-215024503680,-215013019394⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8813498182921,8813499712092⟩,⟨-43776492531591,-43776452179887⟩,⟨-8369127593155,-8369105407942⟩,⟨635494881690829,635496411374714⟩,⟨138146977966318,138147990741319⟩,⟨29709584745626,29710408954571⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8019219382749,8019226401641⟩,⟨-38078132771465,-38077984500521⟩,⟨-9478753346270,-9478638978679⟩,⟨525597386446497,525602288949258⟩,⟨157910470675870,157914868192436⟩,⟨19664140669332,19668701301552⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16038438765498,16038452803282⟩,⟨-76156265542930,-76155969001042⟩,⟨-18957506692540,-18957277957358⟩,⟨1051194772892994,1051204577898516⟩,⟨315820941351740,315829736384872⟩,⟨39328281338664,39337402603104⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10722856255644,10722856255645⟩,⟨-104573379102681,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974382⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9623344627868,9623344627869⟩,⟨-104573379102680,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974364⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2385198907456,2385198965312⟩,⟨-11947992171781,-11947992171683⟩,⟨0,0⟩,⟨103208265737483,103208265748560⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7470737110687,7470737110688⟩,⟨-45059981431543,-45059981431528⟩,⟨-20175371224024,-20175371224017⟩,⟨543561337128360,543561337128597⟩,⟨294137387455586,294137387455708⟩,⟨108970667283860,108970667283909⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6371225482911,6371225482912⟩,⟨-45059981431543,-45059981431527⟩,⟨-20175371224025,-20175371224016⟩,⟨543561337128363,543561337128594⟩,⟨294137387455587,294137387455707⟩,⟨108970667283859,108970667283909⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1931760264832,1931760303424⟩,⟨-7776207836994,-7776207836949⟩,⟨-3481756424265,-3481756424244⟩,⟨38808268597307,38808268599625⟩,⟨26136195978151,26136195979241⟩,⟨7780102513396,7780102513877⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101182341120,101182341120⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138005285575,138005285575⟩,⟨688734959616,688734959616⟩,⟨308377479168,308377479168⟩,⟨-1732836851712,-1732836851712⟩,⟨-1551737290752,-1551737290752⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4316959172288,4316959268736⟩,⟨-19724200008775,-19724200008632⟩,⟨-3481756424265,-3481756424244⟩,⟨142016534334790,142016534348185⟩,⟨26136195978151,26136195979241⟩,⟨7780102513396,7780102513877⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨723459991550,723461160108⟩,⟨-5368204409744,-5368184600358⟩,⟨5706661570880,5706682620342⟩,⟨68637135398842,68637672403690⟩,⟨-33757620646906,-33756940405966⟩,⟨-10866429287578,-10865568532030⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5040419163838,5040420428844⟩,⟨-25092404418519,-25092384608990⟩,⟨2224905146615,2224926196098⟩,⟨210653669733632,210654206751875⟩,⟨-7621424668755,-7620744426725⟩,⟨-3086326774182,-3085466018153⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463843581404,463843697817⟩,⟨1697615875037,1697618703588⟩,⟨204746458170,204748395246⟩,⟨-30588480702433,-30588397259365⟩,⟨1067265665890,1067344997725⟩,⟨-284018613887,-283939402982⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35554721987,35554724041⟩,⟨-726336728572,-726336718235⟩,⟨316591611439,316591629720⟩,⟨9000139116744,9000139143165⟩,⟨-6467554870054,-6467554778038⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨499398303391,499398421858⟩,⟨971279146465,971281985353⟩,⟨521338069609,521340024966⟩,⟨-21588341585689,-21588258116200⟩,⟨-5400289204164,-5400209780313⟩,⟨-284018613887,-283939402982⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506844853278,506844865574⟩,⟨2538898610666,2538898733883⟩,⟨0,0⟩,⟨3504487769187,3504490687699⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨230208988622,230209048818⟩,⟨1600901209830,1600902858863⟩,⟨240322622084,240323529281⟩,⟨-3874307632688,-3874253882592⟩,⟨-1285556532029,-1285515285839⟩,⟨-130924832935,-130888315692⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-723461160108,-723459991550⟩,⟨5368184600358,5368204409744⟩,⟨-5706682620342,-5706661570880⟩,⟨-68637672403690,-68637135398842⟩,⟨33756940405966,33757620646906⟩,⟨10865568532030,10866429287578⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3593498012180,3593499277186⟩,⟨-14356015408417,-14355995598888⟩,⟨-9188439044607,-9188417995124⟩,⟨73378861931100,73379398949343⟩,⟨59893136384117,59893816626147⟩,⟨18645671045426,18646531801455⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451038176273,451038335052⟩,⟨449073652034,449076930832⟩,⟨-145427562483,-145424565660⟩,⟨-14438461733576,-14438367518622⟩,⟨-7336046545693,-7335940638414⟩,⟨-3949175118803,-3949054873863⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨323642982400,323642982400⟩,⟨1952062636032,1952062636032⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-323642982400,-323642982400⟩,⟨-1952062636032,-1952062636032⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨775868645376,775868645376⟩,⟨-1952062636032,-1952062636032⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1363143583026,1363143610260⟩,⟨-8916897923642,-8916897855092⟩,⟨-3992494449860,-3992494419165⟩,⟨54996606489143,54996606490941⟩,⟨34669441413306,34669441491334⟩,⟨11025465753558,11025465753934⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1363143610260,-1363143583026⟩,⟨8916897855092,8916897923642⟩,⟨3992494419165,3992494449860⟩,⟨-54996606490941,-54996606489143⟩,⟨-34669441491334,-34669441413306⟩,⟨-11025465753934,-11025465753558⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-263631982484,-263631955250⟩,⟨8916897855092,8916897923642⟩,⟨3992494419165,3992494449860⟩,⟨-54996606490941,-54996606489143⟩,⟨-34669441491334,-34669441413306⟩,⟨-11025465753934,-11025465753558⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11767668667,-11767667451⟩,⟨427628234059,427628240179⟩,⟨73428466045,73428478242⟩,⟨-4457687345301,-4457687329822⟩,⟨1811844321212,1811844382626⟩,⟨2681580451545,2681580475964⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439270507606,439270667601⟩,⟨876701886093,876705171011⟩,⟨-71999096438,-71996087418⟩,⟨-18896149078877,-18896054848444⟩,⟨-5524202224481,-5524096255788⟩,⟨-1267594667258,-1267474397899⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101182341120,-101182341120⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4516448475,4516448475⟩,⟨27650401280,27650401280⟩,⟨40216028160,40216028160⟩,⟨-294471598080,-294471598080⟩,⟨246208790528,246208790528⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9797648061,9797648299⟩,⟨10904128339,10904129797⟩,⟨87241666214,87241668331⟩,⟨-815791365984,-815791350436⟩,⟨97094151476,97094164437⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1469139697751,1469139718758⟩,⟨-7320012747895,-7320012373457⟩,⟨-1370800446683,-1370800379857⟩,⟨106599852323031,106599859705091⟩,⟨22627054450955,22627055946229⟩,⟨5028783483440,5028783766949⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13091370156,13091370663⟩,⟨-50658147881,-50658140802⟩,⟨104355035061,104355040452⟩,⟨-285327041466,-285326889406⟩,⟨-263044714129,-263044630444⟩,⟨-172723580445,-172723560944⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13091370663,-13091370156⟩,⟨50658140802,50658147881⟩,⟨-104355040452,-104355035061⟩,⟨285326889406,285327041466⟩,⟨263044630444,263044714129⟩,⟨172723560944,172723580445⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114273711783,-114273711276⟩,⟨-823367703934,-823367696855⟩,⟨-104355040452,-104355035061⟩,⟨2484350144958,2484350297018⟩,⟨263044630444,263044714129⟩,⟨172723560944,172723580445⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86227454371,86227456095⟩,⟨-564050198691,-564050194353⟩,⟨612385037055,612385052397⟩,⟨3478883248763,3478883248878⟩,⟨-3464847364862,-3464847326197⟩,⟨-2420446037977,-2420446037937⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨115214949121,115214953073⟩,⟨-1327730049620,-1327729992203⟩,⟨710750585234,710750624827⟩,⟨20518662668624,20518663923255⟩,⟨-6228890695114,-6228890074129⟩,⟨-4366729281063,-4366729091950⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-115214953073,-115214949121⟩,⟨1327729992203,1327730049620⟩,⟨-710750624827,-710750585234⟩,⟨-20518663923255,-20518662668624⟩,⟨6228890074129,6228890695114⟩,⟨4366729091950,4366729281063⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨984296674703,984296678655⟩,⟨1327729992203,1327730049620⟩,⟨-710750624827,-710750585234⟩,⟨-20518663923255,-20518662668624⟩,⟨6228890074129,6228890695114⟩,⟨4366729091950,4366729281063⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123544071978,123544072475⟩,⟨783214352160,783214361845⟩,⟨186853489454,186853495534⟩,⟨-2463276820906,-2463276585268⟩,⟨-680144587764,-680144463334⟩,⟨-161583751574,-161583704378⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11876619363,11876619469⟩,⟨171147407788,171147410022⟩,⟨21691516206,21691517424⟩,⟨716751736789,716751791895⟩,⟨101615058200,101615085260⟩,⟨-16094038633,-16094032372⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨173242763043,173242916223⟩,⟨1673887012336,1673892440519⟩,⟨111637710989,111640478262⟩,⟨-1898730419872,-1898521825274⟩,⟨440339921639,440478223205⟩,⟨-557948282990,-557840389900⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-173242916223,-173242763043⟩,⟨-1673892440519,-1673887012336⟩,⟨-111640478262,-111637710989⟩,⟨1898521825274,1898730419872⟩,⟨-440478223205,-440339921639⟩,⟨557840389900,557948282990⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56966072399,56966285775⟩,⟨-72991230689,-72984153473⟩,⟨128682143822,128685818292⟩,⟨-1975785807414,-1975523462720⟩,⟨-1726034755234,-1725855207478⟩,⟨426915556965,427059967298⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28178345671340,28178370897622⟩,⟨-247231576408913,-247230953452055⟩,⟨-84094922352636,-84094475363613⟩,⟨3490176475970098,3490198429586935⟩,⟨1311351654109685,1311370007873915⟩,⟨302645964941787,302663539688723⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13881742889,13881743002⟩,⟨176008125522,176008128408⟩,⟨41990717272,41990718810⟩,⟨562252300989,562252383769⟩,⟨113356695594,113356736130⟩,⟨27196641540,27196656428⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355762085425,355762406813⟩,⟨1389355562637,1389367565257⟩,⟨14410803856,14417458719⟩,⟨-20678691658540,-20678198364112⟩,⟨-3442229031699,-3441897623400⟩,⟨-1905211900147,-1904954599214⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355762406813,-355762085425⟩,⟨-1389367565257,-1389355562637⟩,⟨-14417458719,-14410803856⟩,⟨20678198364112,20678691658540⟩,⟨3441897623400,3442229031699⟩,⟨1904954599214,1905211900147⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83508100793,83508582176⟩,⟨-512665679164,-512650391626⟩,⟨-86416555157,-86406891274⟩,⟨1782049285235,1782636810096⟩,⟨-2082304601081,-2081867224089⟩,⟨637359931956,637737502248⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239187626695,239187626695⟩,⟨1562760804352,1562760804352⟩,⟨308377479168,308377479168⟩,⟨-3931860107264,-3931860107264⟩,⟨-1551737290752,-1551737290752⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1666897817893,-1666896351531⟩,⟨-4095380832700,-4095339362152⟩,⟨448039933692,448065126158⟩,⟨41044384769080,41045883348189⟩,⟨-7563487055977,-7562368323375⟩,⟨2029592051259,2030586148835⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187297105024,-187296939505⟩,⟨-1647548139872,-1647542419062⟩,⟨-232933422153,-232930332841⟩,⟨2511746977876,2511978176698⟩,⟨-195558265012,-195406442559⟩,⟨625298529312,625419084232⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51890521671,51890687190⟩,⟨-84787335520,-84781614710⟩,⟨75444057015,75447146327⟩,⟨-1420113129388,-1419881930566⟩,⟨-1747295555764,-1747143733311⟩,⟨277907397664,278027952584⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4326583180,4326624328⟩,⟨-32105211879,-32103750863⟩,⟨5296143407,5296996286⟩,⟨10324571904,10384777145⟩,⟨-293245050483,-293202893176⟩,⟨45217920305,45251600710⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2448929298,2448944922⟩,⟨-8002958758,-8002393252⟩,⟨7121036970,7121351282⟩,⟨-120967750226,-120943735643⟩,⟨-176560806036,-176544688162⟩,⟨36584543666,36596854274⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4302586884,4302614421⟩,⟨-31380571031,-31379466696⟩,⟨4756208498,4756810447⟩,⟨-12901587678,-12850841130⟩,⟨-277015882338,-276983173132⟩,⟨36503358929,36527090221⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4302614421,-4302586884⟩,⟨31379466696,31380571031⟩,⟨-4756810447,-4756208498⟩,⟨12850841130,12901587678⟩,⟨276983173132,277015882338⟩,⟨-36527090221,-36503358929⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨23968759,24037444⟩,⟨-725745183,-723179832⟩,⟨539332960,540787788⟩,⟨23175413034,23286364823⟩,⟨-16261877351,-16187010838⟩,⟨8690830084,8748241781⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56966072399,56966285775⟩,⟨-72991230689,-72984153473⟩,⟨128682143822,128685818292⟩,⟨-1975785807414,-1975523462720⟩,⟨-1726034755234,-1725855207478⟩,⟨426915556965,427059967298⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨23968759,24037444⟩,⟨-725745183,-723179832⟩,⟨539332960,540787788⟩,⟨23175413034,23286364823⟩,⟨-16261877351,-16187010838⟩,⟨8690830084,8748241781⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112528143155,112957639885⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121547574476,125413045044⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112957639885,-112528143155⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436798174003,437227670733⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨48286673141,49871281194⟩,⟨-125413045044,-121547574476⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160814816296,162828921079⟩,⟨974098582732,977964053300⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47857176411,50300777924⟩,⟨-125413045044,-121547574476⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2113665886400,-2099980674816⟩,⟨6577656544160,6686466290340⟩,⟨2949504720200,2989381942716⟩,⟨-40662445327920,-39349802694177⟩,⟨-25696848066343,-25069466531330⟩,⟨-8127612454187,-7912220184591⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313017095145,-307143642608⟩,⟨-917957212349,-870239188966⟩,⟨-409117230881,-391546461992⟩,⟨5633000667829,6139285741994⟩,⟨3520635673072,3764830332855⟩,⟨1139838955286,1220249734627⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307143642608,313017095145⟩,⟨870239188966,917957212349⟩,⟨391546461992,409117230881⟩,⟨-6139285741994,-5633000667829⟩,⟨-3764830332855,-3520635673072⟩,⟨-1220249734627,-1139838955286⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162828921079,-160814816296⟩,⟨-977964053300,-974098582732⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨936682706697,938696811480⟩,⟨-977964053300,-974098582732⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-176226191360,-173864501376⟩,⟨-1147969147357,-1140978327842⟩,⟨-513233461576,-511629170818⟩,⟨-1198562279827,-1184008892419⟩,⟨752024158702,759721410645⟩,⟨-239568713443,-238073342581⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150451309245,-148116552506⟩,⟨-826033841736,-815263581902⟩,⟨-369097431032,-365783516258⟩,⟨998410681607,1033462892085⟩,⟨1370972111827,1387734098544⟩,⟨201976024727,205364412044⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148116552506,150451309245⟩,⟨815263581902,826033841736⟩,⟨365783516258,369097431032⟩,⟨-1033462892085,-998410681607⟩,⟨-1387734098544,-1370972111827⟩,⟨-205364412044,-201976024727⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨455260195114,463468404390⟩,⟨1685502770868,1743991054085⟩,⟨757329978250,778214661913⟩,⟨-7172748634079,-6631411349436⟩,⟨-5152564431399,-4891607784899⟩,⟨-1425614146671,-1341814980013⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨817846533346,827938392500⟩,⟨4063694978221,4136184908198⟩,⟨757329978250,778214661913⟩,⟨-19224080145527,-18475830408513⟩,⟨-5152564431399,-4891607784899⟩,⟨-1425614146671,-1341814980013⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95714352822,100601555848⟩,⟨-250826090088,-243095148952⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12016969413884,12630559409025⟩,⟨29037989969393,33099255637049⟩,⟨-115393980268205,-104352069961320⟩,⟨140335692373215,173477783247487⟩,⟨-342120023047361,-214130643138571⟩,⟨1812329569988119,2108500542362998⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8938547377028,9510881730861⟩,⟨66012869585792,72438045858502⟩,⟨-78615171644367,-68680212411961⟩,⟨98193814831315,177728644628842⟩,⟨-730900476313595,-574987063322169⟩,⟨1168335599903840,1429294660108277⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨87700918272,93260138240⟩,⟨-748408661690,-602775596874⟩,⟨627131592519,812228915090⟩,⟨6397706362167,11069425991053⟩,⟨-7736139892251,-1015201298120⟩,⟨-5854255169452,3425580356857⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1187212546048,1192771766016⟩,⟨-748408661690,-602775596874⟩,⟨627131592519,812228915090⟩,⟨6397706362167,11069425991053⟩,⟨-7736139892251,-1015201298120⟩,⟨-5854255169452,3425580356857⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨84378781440,89515317952⟩,⟨-693122750932,-555645930416⟩,⟨578097585612,752228520100⟩,⟨5460545439854,9970913673913⟩,⟨-6872515606129,-461626552572⟩,⟨-5936429335273,2868578092699⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨91109130103,97107971560⟩,⟨-812843870340,-646224443786⟩,⟨672336051191,882158810738⟩,⟨6996304669905,12661426480542⟩,⟨-9109311830525,-1210206862823⟩,⟨-6257109176602,4502148278298⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-93260138240,-87700918272⟩,⟨602775596874,748408661690⟩,⟨-812228915090,-627131592519⟩,⟨-11069425991053,-6397706362167⟩,⟨1015201298120,7736139892251⟩,⟨-3425580356857,5854255169452⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1006251489536,1011810709504⟩,⟨602775596874,748408661690⟩,⟨-812228915090,-627131592519⟩,⟨-11069425991053,-6397706362167⟩,⟨1015201298120,7736139892251⟩,⟨-3425580356857,5854255169452⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-97454197696,-91396463168⟩,⟨655022497268,817771734417⟩,⟨-887506896482,-681489602396⟩,⟨-12703573780741,-7342464398994⟩,⟨1509186371838,9113222399803⟩,⟨-4459446017797,5974437026626⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-89680907800,-83644251572⟩,⟨533129239448,702437902124⟩,⟨-764586159788,-551694766043⟩,⟨-10440290782687,-4625279699023⟩,⟨-512713058097,7554717386000⟩,⟨-3845225056137,7112752500186⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1428222303,13463719988⟩,⟨-279714630892,56213458338⟩,⟨-92250108597,330464044695⟩,⟨-3443986112782,8036146781519⟩,⟨-9622024888622,6344510523177⟩,⟨-10102334232739,11614900778484⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨714111151,6731859994⟩,⟨-139857315446,28106729169⟩,⟨-46125054299,165232022348⟩,⟨-1721993056391,4018073390760⟩,⟨-4811012444311,3172255261589⟩,⟨-5051167116370,5807450389242⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6731859994,-714111151⟩,⟨-28106729169,139857315446⟩,⟨-165232022348,46125054299⟩,⟨-4018073390760,1721993056391⟩,⟨-3172255261589,4811012444311⟩,⟨-5807450389242,5051167116370⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755391523622,761409291729⟩,⟨-28106729169,139857315446⟩,⟨-165232022348,46125054299⟩,⟨-4018073390760,1721993056391⟩,⟨-3172255261589,4811012444311⟩,⟨-5807450389242,5051167116370⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6995333993,7910287773⟩,⟨-126959449062,-96159007366⟩,⟨100044447282,137785865998⟩,⟨1681515901478,2896652809898⟩,⟨-2418078349592,-849565742236⟩,⟨-277713501529,1781128791011⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7910287773,-6995333993⟩,⟨96159007366,126959449062⟩,⟨-137785865998,-100044447282⟩,⟨-2896652809898,-1681515901478⟩,⟨849565742236,2418078349592⟩,⟨-1781128791011,277713501529⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091601340003,1092516293783⟩,⟨96159007366,126959449062⟩,⟨-137785865998,-100044447282⟩,⟨-2896652809898,-1681515901478⟩,⟨849565742236,2418078349592⟩,⟨-1781128791011,277713501529⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7938879744,-7017681728⟩,⟨96774709279,127879460555⟩,⟨-138784331108,-100685027497⟩,⟨-2932516510070,-1700800305241⟩,⟨863867376458,2451742359037⟩,⟨-1811553598430,270505972493⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3969439872,-3508840864⟩,⟨48387354639,63939730278⟩,⟨-69392165554,-50342513748⟩,⟨-1466258255035,-850400152620⟩,⟨431933688229,1225871179519⟩,⟨-905776799215,135252986247⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3508840864,3969439872⟩,⟨-63939730278,-48387354639⟩,⟨50342513748,69392165554⟩,⟨850400152620,1466258255035⟩,⟨-1225871179519,-431933688229⟩,⟨-135252986247,905776799215⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765632224480,766092842752⟩,⟨-63939730278,-48387354639⟩,⟨50342513748,69392165554⟩,⟨850400152620,1466258255035⟩,⟨-1225871179519,-431933688229⟩,⟨-135252986247,905776799215⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272900335000,273129073446⟩,⟨24039751841,31739862266⟩,⟨-34446466500,-25011111820⟩,⟨-724163202475,-420378975369⟩,⟨212391435559,604519587398⟩,⟨-445282197753,69428375383⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531264448960,1532185685504⟩,⟨-127879460556,-96774709278⟩,⟨100685027496,138784331108⟩,⟨1700800305240,2932516510070⟩,⟨-2451742359038,-863867376458⟩,⟨-270505972494,1811553598430⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1194814215998,1201415185157⟩,⟨-893563428436,-711798012648⟩,⟨740559212315,969761697311⟩,⟨8402934832855,14545546364967⟩,⟨-10679111694139,-2081178787454⟩,⟨-6071681290413,5655525781075⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1290116804220,1303318742538⟩,⟨-1787126856872,-1423596025296⟩,⟨1481118424630,1939523394622⟩,⟨16805869665715,29091092729919⟩,⟨-21358223388266,-4162357574908⟩,⟨-12138721028777,11311051562145⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨175775244608,186969515584⟩,⟨-1523092136320,-1200980490788⟩,⟨1249507796397,1652973217429⟩,⟨12067988870639,23481286383719⟩,⟨-16837885390087,-1221695235780⟩,⟨-12830346127746,8219961147795⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨60252687286,64582432792⟩,⟨-520655290956,-402259014619⟩,⟨416839909974,566378977876⟩,⟨3864175800264,7849874012488⟩,⟨-5678487694790,-73615899447⟩,⟨-4790763669732,2868791364058⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380061993468,380609396079⟩,⟨1713141301,20210347469⟩,⟨-23011493936,-357059065⟩,⟨-594374134984,138780939959⟩,⟨-308840552107,636006510010⟩,⟨-696399469836,542175830383⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176290002477,3180864807300⟩,⟨-169147097349,-14296634931⟩,⟨2979756017,192590820662⟩,⟨-1161374990305,4992503444630⟩,⟨-5343431899580,2584762131826⟩,⟨-4537643655606,5851719479062⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨174059103527,186835666353⟩,⟨-1516180439270,-1162836904053⟩,⟨1204338311245,1649835159745⟩,⟨11105148988002,23162966198114⟩,⟨-16919937741889,-67351048082⟩,⟨-14123851961909,8841484080861⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨349834348135,373805181937⟩,⟨-3039272575590,-2363817394841⟩,⟨2453846107642,3302808377174⟩,⟨23173137858641,46644252581833⟩,⟨-33757823131976,-1289046283862⟩,⟨-26954198089655,17061445228656⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518972550671,527274196003⟩,⟨-38927691548,193701743224⟩,⟨-228845596408,63882989572⟩,⟨-5572163620422,2420532077147⟩,⟨-4435593908024,6674964432010⟩,⟨-8057155398324,7045504749276⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356546903066,365136176812⟩,⟨-40436006271,201207022359⟩,⟨-237712579488,66358236623⟩,⟨-5795493250018,2551277548637⟩,⟨-4651121544166,6945785267707⟩,⟨-8383742852971,7370079495178⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713093806132,730272353624⟩,⟨-80872012542,402414044718⟩,⟨-475425158976,132716473246⟩,⟨-11590986500036,5102555097274⟩,⟨-9302243088332,13891570535414⟩,⟨-16767485705942,14740158990356⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523354161187,1525190351511⟩,⟨-31720453190,30184739784⟩,⟨-37100838502,38739883826⟩,⟨-1195852504658,1251000608592⟩,⟨-1602176616802,1554210973134⟩,⟨-2051634763505,2089267099959⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨987979016725,1012999153066⟩,⟨-133249871621,578257731179⟩,⟨-684128810454,209828204445⟩,⟨-16895945290573,7931005245782⟩,⟨-13994392409408,20329895804181⟩,⟨-24655214834800,21866580589951⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67734247607,67847841603⟩,⟨11933400548,15768963154⟩,⟨-17113655266,-12415586378⟩,⟨-358726747159,-206844823602⟩,⟨103442958446,299243063392⟩,⟨-220086728187,36651666767⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50382568219,51089803412⟩,⟨259216005472,267106723639⟩,⟨33767832097,38786439142⟩,⟨-1368178883520,-1173400140693⟩,⟨-297166144343,-110736500312⟩,⟨-277922744909,-72165582928⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132556630975,2135123372558⟩,⟨-356403832364,-269551804878⟩,⟨280443424612,386796028572⟩,⟨4754366066753,8202756317889⟩,⟨-6865361160560,-2423900089434⟩,⟨-735468173184,5083889086744⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2969962365028,2975325940696⟩,⟨-744981003037,-563097859361⟩,⟨585850620226,808508964185⟩,⟨9967531058798,17208170732062⟩,⟨-14417953066420,-5100589804441⟩,⟨-1498815002879,10699945933312⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136091631669,138251214046⟩,⟨665568993712,696999675224⟩,⟨118057732211,142525880224⟩,⟨-3607571834341,-2635461126175⟩,⟨-1362250103272,-353721102921⟩,⟨-785729849241,359293550335⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8744413768492,8883175289977⟩,⟨-45495598929487,-42097356704294⟩,⟨-9303161126524,-7467172466776⟩,⟨572023571604644,701494479570825⟩,⟨94269845669670,184211965983455⟩,⟨-10699363253568,70773333526110⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7857395136699,8184223629800⟩,⟨-42992437693809,-33155211253490⟩,⟨-14098377947624,-5014470835317⟩,⟨329638422481609,721402456240940⟩,⟨-41931249231583,363402331080281⟩,⟨-212602728691730,253446265928190⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15714790273398,16368447259600⟩,⟨-85984875387618,-66310422506980⟩,⟨-28196755895248,-10028941670634⟩,⟨659276844963218,1442804912481880⟩,⟨-83862498463166,726804662160562⟩,⟨-425205457383460,506892531856380⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10702470597344,10743319721800⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803854,2051378711294242⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9602958969568,9643808094024⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803861,2051378711294240⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2382867281216,2387534528576⟩,⟨-12019099426619,-11877349255562⟩,⟨0,0⟩,⟨99839973091184,106573343585493⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7424515323221,7517502724311⟩,⟨-45716231901356,-44416003041083⟩,⟨-20438789668671,-19916699776366⟩,⟨531423598783734,556028760056101⟩,⟨288431555444674,299987189900870⟩,⟨106855441119841,111139067969795⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6325003695445,6417991096535⟩,⟨-45716231901356,-44416003041082⟩,⟨-20438789668671,-19916699776366⟩,⟨531423598783736,556028760056094⟩,⟨288431555444674,299987189900867⟩,⟨106855441119841,111139067969795⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1923754483520,1939801384704⟩,⟨-7947114495738,-7609220871193⟩,⟨-3552991900158,-3412071263671⟩,⟨33601330968830,43997701229439⟩,⟨23732735058026,28535095457570⟩,⟨6824929326156,8731394109226⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100967634698,101397131429⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136999421924,139013526708⟩,⟨685013642768,692454936088⟩,⟨307361902754,309392455436⟩,⟨-1739706366693,-1725980926276⟩,⟨-1555669031326,-1547805550178⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4306621764736,4327335913280⟩,⟨-19966213922357,-19486570126755⟩,⟨-3552991900158,-3412071263671⟩,⟨133441304060014,150571044814932⟩,⟨23732735058026,28535095457570⟩,⟨6824929326156,8731394109226⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨699668696270,747610363874⟩,⟨-6078545151180,-4727634789682⟩,⟨4907692215284,6605616754348⟩,⟨46346275717282,93288505163666⟩,⟨-67515646263952,-2578092567724⟩,⟨-53908396179310,34122890457312⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5006290461006,5074946277154⟩,⟨-26044759073537,-24214204916437⟩,⟨1354700315126,3193545490677⟩,⟨179787579777296,243859549978598⟩,⟨-43782911205926,25957002889846⟩,⟨-47083466853154,42854284566538⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459725294112,468012326255⟩,⟨1575802530147,1812589183106⟩,⟨124401491614,294509256349⟩,⟨-35067528719125,-26001700715041⟩,⟨-2961315070894,4933625446996⟩,⟨-4342044555090,3952028714129⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34548680971,36567726503⟩,⟨-746929360823,-705929493984⟩,⟨315329944105,317856354168⟩,⟨8660736626323,9346943389182⟩,⟨-6499332721185,-6435979379349⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨494273975083,504580052758⟩,⟨828873169324,1106659689122⟩,⟨439731435719,612365610517⟩,⟨-26406792092802,-16654757325859⟩,⟨-9460647792079,-1502353932353⟩,⟨-4342044555090,3952028714129⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506349041299,507340811276⟩,⟨2518951804351,2559009350623⟩,⟨0,0⟩,⟨2371496934072,4641016220299⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227623926023,232825235180⟩,⟨1514082629022,1685001459584⟩,⟨202505899237,282560054655⟩,⟨-7320787495852,-388764611565⟩,⟨-3357954876807,733356364412⟩,⟨-2003522610882,1823560027345⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-747610363874,-699668696270⟩,⟨4727634789682,6078545151180⟩,⟨-6605616754348,-4907692215284⟩,⟨-93288505163666,-46346275717282⟩,⟨2578092567724,67515646263952⟩,⟨-34122890457312,53908396179310⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3559011400862,3627667217010⟩,⟨-15238579132675,-13408024975575⟩,⟨-10158608654506,-8319763478955⟩,⟨40152798896348,104224769097650⟩,⟨26310827625750,96050741721522⟩,⟨-27297961131156,62639790288536⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443453704555,458653461064⟩,⟨290676996069,614003875041⟩,⟨-289473518404,-15852419333⟩,⟨-19930870798838,-9116313898066⟩,⟨-12540077925409,-1797682494838⟩,⟨-10315705247739,2144831616146⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨321629632592,325657842158⟩,⟨1948197165464,1955928106600⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-325657842158,-321629632592⟩,⟨-1955928106600,-1948197165464⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨773853785618,777881995184⟩,⟨-1955928106600,-1948197165464⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1353969027760,1372369816995⟩,⟨-9073145819880,-8764143247952⟩,⟨-4056417410908,-3929953123090⟩,⟨50614328062991,59401817300596⟩,⟨32642513218384,36708478349737⟩,⟨10225488391168,11828760544614⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1372369816995,-1353969027760⟩,⟨8764143247952,9073145819880⟩,⟨3929953123090,4056417410908⟩,⟨-59401817300596,-50614328062991⟩,⟨-36708478349737,-32642513218384⟩,⟨-11828760544614,-10225488391168⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-272858189219,-254457399984⟩,⟨8764143247952,9073145819880⟩,⟨3929953123090,4056417410908⟩,⟨-59401817300596,-50614328062991⟩,⟨-36708478349737,-32642513218384⟩,⟨-11828760544614,-10225488391168⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12482795847,-11075474212⟩,⟨409596240645,446203802615⟩,⟨62550779499,84486986161⟩,⟨-4787343014977,-4140728865724⟩,⟨1594114983701,2025614213673⟩,⟨2581324987563,2781046414712⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430970908708,447577986852⟩,⟨700273236714,1060207677656⟩,⟨-226922738905,68634566828⟩,⟨-24718213813815,-13257042763790⟩,⟨-10945962941708,227931718835⟩,⟨-7734380260176,4925878030858⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101397131429,-100967634698⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4394701959,4638745477⟩,⟨26458411891,28843180952⟩,⟨40110970503,40321203045⟩,⟨-300086680622,-288861045387⟩,⟨245652667759,246764997182⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9524220794,10072803885⟩,⟨6633254910,15158257517⟩,⟨86928702539,87555476515⟩,⟨-883154375975,-748025300615⟩,⟨91616271808,102543659135⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1460163981482,1478181749660⟩,⟨-7475770569699,-7166790539823⟩,⟨-1406550818100,-1335637973011⟩,⟨102936455557289,110361809410558⟩,⟨21738091033550,23539789501285⟩,⟨4809907710285,5253447410031⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12648273837,13541862128⟩,⟨-59677705340,-41701637989⟩,⟨102556668806,106139847514⟩,⟨-501779560262,-68816949062⟩,⟨-304728341875,-221161446024⟩,⟨-182346258236,-163066585291⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13541862128,-12648273837⟩,⟨41701637989,59677705340⟩,⟨-106139847514,-102556668806⟩,⟨68816949062,501779560262⟩,⟨221161446024,304728341875⟩,⟨163066585291,182346258236⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114938993557,-113615908535⟩,⟨-832753703477,-813918642666⟩,⟨-106139847514,-102556668806⟩,⟨2267840204614,2700802815814⟩,⟨221161446024,304728341875⟩,⟨163066585291,182346258236⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨83733045984,88742598263⟩,⟨-584825502141,-543862840405⟩,⟨601698219811,622860847877⟩,⟨3144877614350,3825755134273⟩,⟨-3689839889970,-3235941378872⟩,⟨-2528678031490,-2311550887519⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨111198440031,119305413291⟩,⟨-1389614852428,-1268041280357⟩,⟨685538083509,735657979110⟩,⟨19105502455569,22003403218042⟩,⟨-6879434606369,-5571274674179⟩,⟨-4626843623300,-4107587988672⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-119305413291,-111198440031⟩,⟨1268041280357,1389614852428⟩,⟨-735657979110,-685538083509⟩,⟨-22003403218042,-19105502455569⟩,⟨5571274674179,6879434606369⟩,⟨4107587988672,4626843623300⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨980206214485,988313187745⟩,⟨1268041280357,1389614852428⟩,⟨-735657979110,-685538083509⟩,⟨-22003403218042,-19105502455569⟩,⟨5571274674179,6879434606369⟩,⟨4107587988672,4626843623300⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122133937794,124954478198⟩,⟨768682686640,798115803862⟩,⟨181000029486,192684022067⟩,⟨-2765677229628,-2168934492463⟩,⟨-812987516740,-546152242574⟩,⟨-214773192950,-107686991953⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11740280271,12015309258⟩,⟨168209419024,174106157936⟩,⟨21194990226,22190956316⟩,⟨640349752634,792744695712⟩,⟨88125699670,115070893084⟩,⟨-18991750193,-13208211400⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167798172887,178872101876⟩,⟨1464505542279,1883876865238⟩,⟨-5200414222,223270864867⟩,⟨-11039388108089,7279296982463⟩,⟨-5857211740402,6842950298794⟩,⟨-6067481523772,4963821645485⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178872101876,-167798172887⟩,⟨-1883876865238,-1464505542279⟩,⟨-223270864867,5200414222⟩,⟨-7279296982463,11039388108089⟩,⟨-6842950298794,5857211740402⟩,⟨-4963821645485,6067481523772⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48751824147,65027062293⟩,⟨-369794236216,220495917305⟩,⟨-20764965630,287760468877⟩,⟨-14600084478315,10650623496524⟩,⟨-10200905175601,6590568104814⟩,⟨-6967344256367,7891041551117⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27495296531947,28877854365080⟩,⟨-270006698729043,-224774596733067⟩,⟨-102639266207267,-66314174373765⟩,⟨2551556424165557,4443420328627440⟩,⟨466431340829808,2188715651217973⟩,⟨-590373815308361,1206495553364101⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13566658491,14200506141⟩,⟨170770805986,181404436832⟩,⟨40211027848,43795319352⟩,⟨446178669602,676824722164⟩,⟨68294244574,158398396058⟩,⟨10775945007,43610081747⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339259075333,372965722136⟩,⟨783222427499,1991002788314⟩,⟨-320065187726,332013857840⟩,⟨-46454185206596,5342540428036⟩,⟨-20225854918566,13908114200777⟩,⟨-15531948583520,11877173964654⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372965722136,-339259075333⟩,⟨-1991002788314,-783222427499⟩,⟨-332013857840,320065187726⟩,⟨-5342540428036,46454185206596⟩,⟨-13908114200777,20225854918566⟩,⟨-11877173964654,15531948583520⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58005186572,108318911519⟩,⟨-1290729551600,276985250157⟩,⟨-558936596745,388699754554⟩,⟨-30060754241851,33197142442806⟩,⟨-24854077142485,20453786637401⟩,⟨-19611554224830,20457826614378⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237967056622,240410658137⟩,⟨1558609990774,1566910277554⟩,⟨307361902754,309392455436⟩,⟨-3938729622245,-3925004181828⟩,⟨-1555669031326,-1547805550178⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1711098642872,-1623857473850⟩,⟨-5545158434989,-2644397437440⟩,⟨-543784314343,1481794427262⟩,⟨-20239288630996,102329120251617⟩,⟨-59207533930994,42959414188751⟩,⟨-48787197161716,52607912202569⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-194458551110,-180378363163⟩,⟨-1872237815054,-1428999710556⟩,⟨-361660253397,-98917918141⟩,⟨-7147088061062,12235817235916⟩,⟨-7288544468063,6787632225076⟩,⟨-5575991540369,6832241122160⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43508505512,60032294974⟩,⟨-313627824280,137910566998⟩,⟨-54298350643,210474537295⟩,⟨-11085817683307,8310813054088⟩,⟨-8844213499389,5239826674898⟩,⟨-5923724172249,6485191322972⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2571922464,6406172004⟩,⟨-112766483753,38103657856⟩,⟨-35102169359,51337250553⟩,⟨-3733865915258,3880800514810⟩,⟨-2943396282285,2119422568785⟩,⟨-2138819234983,2190760137134⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1721664422,3277706528⟩,⟨-34247565162,15059573050⟩,⟨-5929277182,22983421346⟩,⟨-1289226326236,1086445250439⟩,⟨-1085844096102,624978353404⟩,⟨-667647649756,788751002462⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3012300704,5782657956⟩,⟨-84111692001,14653829388⟩,⟨-21052332917,35205476572⟩,⟨-2439585932135,2542981925972⟩,⟨-2093311648072,1341200468475⟩,⟨-1315741808184,1455894181924⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5782657956,-3012300704⟩,⟨-14653829388,84111692001⟩,⟨-35205476572,21052332917⟩,⟨-2542981925972,2439585932135⟩,⟨-1341200468475,2093311648072⟩,⟨-1455894181924,1315741808184⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3210735492,3393871300⟩,⟨-127420313141,122215349857⟩,⟨-70307645931,72389583470⟩,⟨-6276847841230,6320386446945⟩,⟨-4284596750760,4212734216857⟩,⟨-3594713416907,3506501945318⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48751824147,65027062293⟩,⟨-369794236216,220495917305⟩,⟨-20764965630,287760468877⟩,⟨-14600084478315,10650623496524⟩,⟨-10200905175601,6590568104814⟩,⟨-6967344256367,7891041551117⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3210735492,3393871300⟩,⟨-127420313141,122215349857⟩,⟨-70307645931,72389583470⟩,⟨-6276847841230,6320386446945⟩,⟨-4284596750760,4212734216857⟩,⟨-3594713416907,3506501945318⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (105/1024) u, BivariateJet2.affineZ (115/1024) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000045

end


