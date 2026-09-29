-- Prove2me | Definitions.Def_GeneralCK_RB2Cell000000_data
-- name    : GeneralCK_RB2Cell000000_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T22:17:30.861793+00:00
-- url     : https://prove2.me/theorems/7779a53a-6945-4326-943d-b5eb448c8c2f
-- title:
--   Exact certificate data for the first RB2 cell
-- statement:
--   For the first RB2 cell, the entropy coordinates are $e=H(u)$ and $f=H(u+\rho(1/2-u))$, with $$\frac1{10}\le u\le\frac{257}{2560},\qquad \frac1{10}\le\rho\le\frac{53}{512}.$$ This bundle stores the source's exact dyadic endpoints, proposed logarithm enclosures, input and register jet records, center and whole-cell instruction lists, and their affine-coordinate real semantics. Endpoint intervals at precision $40$ are lifted exactly to precision $64$ for logarithm checks. All integer data and program definitions are preserved from the release source. Separate theorem proofs check these proposals and use them to establish positivity of the correction matrix's first diagonal entry and determinant. The data bundle itself introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000000Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2154885614464,-2154885574912⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2154885614400,-2154885574912⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-166955339520,-166955339456⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-166955339520,-166955339456⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨81268356672,81268356736⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-87758016768,-87758016704⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨81268480576,81268480640⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-87758161280,-87758161216⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6489680640,-6489680576⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6489660096,-6489660032⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨169026373440,169026373504⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨169026641792,169026641856⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1987930235456,1987930274048⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1987930235520,1987930274112⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2531719137984,-2531719080128⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-115845112128,-115845112064⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2162070810560,-2162070770880⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2147741743808,-2147741704512⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-168131232448,-168131232384⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-165781580672,-165781580608⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨78662794688,78662794752⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-84727255616,-84727255552⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨83897544128,83897544192⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-90832069824,-90832069760⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-6934525632,-6934525568⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6064460928,-6064460864⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨163390050304,163390050368⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨174729613952,174729614016⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2415873968064,2415874025920⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1979610472128,1979610510720⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1996289190272,1996289228864⟩



end LaneCBRB2Cell000000Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000000
open Set LaneCBRB2Cell000000Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110165911143,-110165911142⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439589902745,439589902746⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨44731706900,44731706901⟩,⟨-111883898061,-111883898060⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨154897618042,154897618044⟩,⟨987627729715,987627729716⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44731706899,44731706902⟩,⟨-111883898061,-111883898060⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2154885614464,-2154885574912⟩,⟨7010489808998,7010489809097⟩,⟨3120346301153,3120346301201⟩,⟨-44698906425268,-44698906424007⟩,⟨-27700015063075,-27700015062386⟩,⟨-8855350678840,-8855350678567⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-303577188641,-303577183064⟩,⟨-947981438448,-947981402891⟩,⟨-421943466951,-421943451122⟩,⟨6297117701302,6297117701753⟩,⟨3858200634342,3858200674137⟩,⟨1247529077784,1247529077884⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨303577183064,303577188641⟩,⟨947981402891,947981438448⟩,⟨421943451122,421943466951⟩,⟨-6297117701753,-6297117701302⟩,⟨-3858200674137,-3858200634342⟩,⟨-1247529077884,-1247529077784⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-154897618044,-154897618042⟩,⟨-987627729716,-987627729715⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨944614009732,944614009734⟩,⟨-987627729716,-987627729715⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-166955339520,-166955339456⟩,⟨-1149578729037,-1149578729031⟩,⟨-511673767849,-511673767846⟩,⟨-1201925673971,-1201925673959⟩,⟨744836103071,744836103081⟩,⟨-238114848530,-238114848527⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-143434911216,-143434911160⟩,⟨-837661400393,-837661400326⟩,⟨-372840375431,-372840375399⟩,⟨1032600112258,1032600112285⟩,⟨1392163252765,1392163252848⟩,⟨204569570852,204569570861⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨143434911160,143434911216⟩,⟨837661400326,837661400393⟩,⟨372840375399,372840375431⟩,⟨-1032600112285,-1032600112258⟩,⟨-1392163252848,-1392163252765⟩,⟨-204569570861,-204569570852⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨447012094224,447012099857⟩,⟨1785642803217,1785642838841⟩,⟨794783826521,794783842382⟩,⟨-7329717814038,-7329717813560⟩,⟨-5250363926985,-5250363887107⟩,⟨-1452098648745,-1452098648636⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨804916220551,804916232043⟩,⟨4199132746884,4199132840454⟩,⟨794783826521,794783842382⟩,⟨-19525345882251,-19525345881253⟩,⟨-5250363926985,-5250363887107⟩,⟨-1452098648745,-1452098648636⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89463413798,89463413804⟩,⟨-223767796122,-223767796120⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13513074990221,13513074991128⟩,⟨33799190985386,33799190990226⟩,⟨-132796437537296,-132796437519166⟩,⟨169078512787550,169078512824621⟩,⟨-332153278129136,-332153277943327⟩,⟨2610048983009966,2610048983547418⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9892476781852,9892476923754⟩,⟨76350909483312,76350910993568⟩,⟨-87447947118982,-87447945522143⟩,⟨141973172253173,141973179865568⟩,⟨-790415431931230,-790415415967656⟩,⟨1700900174147398,1700900205680914⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨84347141120,84347274496⟩,⟨-645484893542,-645482814286⟩,⟨739298933846,739301314182⟩,⟨8637087924716,8637140253067⟩,⟨-4584899107371,-4584822137342⟩,⟨-1474991376412,-1474881593523⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1183858768896,1183858902272⟩,⟨-645484893542,-645482814286⟩,⟨739298933846,739301314182⟩,⟨8637087924716,8637140253067⟩,⟨-4584899107371,-4584822137342⟩,⟨-1474991376412,-1474881593523⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨81268356672,81268480640⟩,⟨-599495619453,-599493620797⟩,⟨686625553607,686627841708⟩,⟨7694847060038,7694898743349⟩,⟨-3883862718063,-3883788256544⟩,⟨-1798690089486,-1798585116281⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨87502718706,87502862043⟩,⟨-693194854228,-693192403063⟩,⟨793942756016,793945562231⟩,⟨9627419575197,9627485612364⟩,⟨-5326882307547,-5326790173225⟩,⟨-1122336928820,-1122209353932⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-84347274496,-84347141120⟩,⟨645482814286,645484893542⟩,⟨-739301314182,-739298933846⟩,⟨-8637140253067,-8637087924716⟩,⟨4584822137342,4584899107371⟩,⟨1474881593523,1474991376412⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1015164353280,1015164486656⟩,⟨645482814286,645484893542⟩,⟨-739301314182,-739298933846⟩,⟨-8637140253067,-8637087924716⟩,⟨4584822137342,4584899107371⟩,⟨1474881593523,1474991376412⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-87758161280,-87758016704⟩,⟨699114152598,699116496468⟩,⟨-800727871056,-800725187741⟩,⟨-9799305151075,-9799244265170⟩,⟨5474895617407,5474983048200⟩,⟨1014289043847,1014412066465⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-81025945061,-81025800930⟩,⟨593962976563,593965476267⟩,⟨-680293933316,-680291071514⟩,⟨-7537346878467,-7537278766144⟩,⟨3748792609432,3748886922548⟩,⟨1895548944356,1895678684321⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6476773645,6477061113⟩,⟨-99231877665,-99226926796⟩,⟨113648822700,113654490717⟩,⟨2090072696730,2090206846220⟩,⟨-1578089698115,-1577903250677⟩,⟨773212015536,773469330389⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3238386822,3238530557⟩,⟨-49615938833,-49613463398⟩,⟨56824411350,56827245359⟩,⟨1045036348365,1045103423110⟩,⟨-789044849058,-788951625338⟩,⟨386606007768,386734665195⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3238530557,-3238386822⟩,⟨49613463398,49615938833⟩,⟨-56827245359,-56824411350⟩,⟨-1045103423110,-1045036348365⟩,⟨788951625338,789044849058⟩,⟨-386734665195,-386606007768⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758884853059,758885016058⟩,⟨49613463398,49615938833⟩,⟨-56827245359,-56824411350⟩,⟨-1045103423110,-1045036348365⟩,⟨788951625338,789044849058⟩,⟨-386734665195,-386606007768⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6470545681,6470566146⟩,⟨-99034680714,-99034205098⟩,⟨113428089212,113428633782⟩,⟨2083037066022,2083052072662⟩,⟨-1571482377816,-1571463865266⟩,⟨767888943445,767912546958⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6470566146,-6470545681⟩,⟨99034205098,99034680714⟩,⟨-113428633782,-113428089212⟩,⟨-2083052072662,-2083037066022⟩,⟨1571463865266,1571482377816⟩,⟨-767912546958,-767888943445⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1093041061630,1093041082095⟩,⟨99034205098,99034680714⟩,⟨-113428633782,-113428089212⟩,⟨-2083052072662,-2083037066022⟩,⟨1571463865266,1571482377816⟩,⟨-767912546958,-767888943445⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6489680640,-6489660032⟩,⟨99620464259,99620944557⟩,⟨-114100106707,-114099556775⟩,⟨-2104409417303,-2104394195556⟩,⟨1591104469798,1591123221207⟩,⟨-784298983641,-784275111799⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3244840320,-3244830016⟩,⟨49810232129,49810472279⟩,⟨-57050053354,-57049778387⟩,⟨-1052204708652,-1052197097778⟩,⟨795552234899,795561610604⟩,⟨-392149491821,-392137555899⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3244830016,3244840320⟩,⟨-49810472279,-49810232129⟩,⟨57049778387,57050053354⟩,⟨1052197097778,1052204708652⟩,⟨-795561610604,-795552234899⟩,⟨392137555899,392149491821⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765368213632,765368243200⟩,⟨-49810472279,-49810232129⟩,⟨57049778387,57050053354⟩,⟨1052197097778,1052204708652⟩,⟨-795561610604,-795552234899⟩,⟨392137555899,392149491821⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273260265407,273260270524⟩,⟨24758551274,24758670179⟩,⟨-28357158446,-28357022303⟩,⟨-520763018166,-520759266505⟩,⟨392865966316,392870594454⟩,⟨-191978136740,-191972235861⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530736427264,1530736486400⟩,⟨-99620944558,-99620464258⟩,⟨114099556774,114100106708⟩,⟨2104394195556,2104409417304⟩,⟨-1591123221208,-1591104469798⟩,⟨784275111798,784298983642⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1190866933886,1190867090348⟩,⟨-757204204968,-757201566867⟩,⟨867255175044,867258195254⟩,⟨11094895220798,11094965851573⟩,⟨-6481324492883,-6481225249474⟩,⟨-467113727052,-466975856525⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1282222239996,1282222552920⟩,⟨-1514408409936,-1514403133734⟩,⟨1734510350088,1734516390507⟩,⟨22189790441606,22189931703138⟩,⟨-12962648985762,-12962450498953⟩,⟨-934227300874,-933951866281⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨169026373440,169026641856⟩,⟨-1298612365305,-1298607524011⟩,⟨1487350455718,1487355998394⟩,⟨17494079003781,17494216215859⟩,⟨-9358857825834,-9358671814403⟩,⟨-2813113846823,-2812862469302⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨58216544671,58216649232⟩,⟨-441708889414,-441707162698⟩,⟨505906009051,505907985865⟩,⟨5822904219992,5822949983970⟩,⟨-3037263974958,-3037199380123⟩,⟨-1124129797688,-1124039832874⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380432031654,380432053476⟩,⟨9710102004,9710388709⟩,⟨-11121721325,-11121393055⟩,⟨-206488585259,-206479498185⟩,⟨156645331353,156656512879⟩,⟨-78241849140,-78227630515⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177770665139,3177770847420⟩,⟨-81111440650,-81109036480⟩,⟨92897631213,92900383930⟩,⟨1728875472796,1728951820742⟩,⟨-1313303443961,-1313209613095⟩,⟨658871326178,658990491726⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨168255453792,168255765643⟩,⟨-1280906570279,-1280901371545⟩,⟨1467070846026,1467076797803⟩,⟨16985865165353,16986004789459⟩,⟨-8922374847731,-8922180057637⟩,⟨-3128547858163,-3128278419179⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨337281827232,337282407499⟩,⟨-2579518935584,-2579508895556⟩,⟨2954421301744,2954432796197⟩,⟨34479944169134,34480221005318⟩,⟨-18281232673565,-18280851872040⟩,⟨-5941661704986,-5941140888481⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523783655992,523783880997⟩,⟨68486598830,68490030642⟩,⟨-78444545592,-78440616666⟩,⟨-1438187304810,-1438093957920⟩,⟨1083942881696,1084072313636⟩,⟨-527976460730,-527798161021⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361516397617,361516630566⟩,⟨70904355865,70907924061⟩,⟨-81213861779,-81209776707⟩,⟨-1484323918865,-1484226492529⟩,⟨1116899149262,1117033923161⟩,⟨-540534642820,-540349322517⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨723032795234,723033261132⟩,⟨141808711730,141815848122⟩,⟨-162427723558,-162419553414⟩,⟨-2968647837730,-2968452985058⟩,⟨2233798298524,2234067846322⟩,⟨-1081069285640,-1080698645034⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524265861118,1524265940719⟩,⟨-586739460,-585783544⟩,⟨670922992,672017496⟩,⟨21342122894,21372351282⟩,⟨-19659355942,-19622091982⟩,⟨16362564840,16410040197⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002348841433,1002349539659⟩,⟨196205242858,196215775245⟩,⟨-224734274091,-224722215939⟩,⟨-4101588412757,-4101297930020⟩,⟨3083985943022,3084384586035⟩,⟨-1488137722128,-1487592260607⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67913035900,67913038445⟩,⟨12306424272,12306483608⟩,⟨-14095139320,-14095071384⟩,⟨-257734168122,-257732287770⟩,⟨193999899586,194002215960⟩,⟨-93961492653,-93958543741⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49716895030,49716897604⟩,⟨268375054930,268375113998⟩,⟨38772465006,38772517708⟩,⟨-1300693259248,-1300691379438⟩,⟨-227210800131,-227208784020⟩,⟨-178854625081,-178852363305⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131086157308,2131086321967⟩,⟨-277383905350,-277382557288⟩,⟨317698046070,317699589578⟩,⟨5877513266311,5877556050083⟩,⟨-4450989089432,-4450936507636⟩,⟨2207411292112,2207478073357⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966891052555,2966891396412⟩,⟨-579259446558,-579256609028⟩,⟨663447242900,663450491832⟩,⟨12311679671625,12311769855908⟩,⟨-9338156268717,-9338045685381⟩,⟨4659178668181,4659318783827⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134154662214,134154684709⟩,⟨697983129257,697983502238⟩,⟨134621783622,134622086420⟩,⟨-3235831895260,-3235820861910⟩,⟨-893833734151,-893822244251⟩,⟨-225150307936,-225137509597⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨9011432006544,9011433517579⟩,⟨-46884929848744,-46884889071574⟩,⟨-9042831324316,-9042807952183⟩,⟨705223996208247,705225577053038⟩,⟨154136049801955,154137150998704⟩,⟨33271512213574,33272467745884⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8215100416611,8215107516674⟩,⟨-41133714735671,-41133561196952⟩,⟨-10085619383277,-10085493198371⟩,⟨592554114097671,592559302264449⟩,⟨173759827325043,173764813855624⟩,⟨21831190001368,21836762685126⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16430200833222,16430215033348⟩,⟨-82267429471342,-82267122393904⟩,⟨-20171238766554,-20170986396742⟩,⟨1185108228195342,1185118604528898⟩,⟨347519654650086,347529627711248⟩,⟨43662380002736,43673525370252⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10973683302499,10973683302600⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨2186188521914400,2186188521974786⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9874171674723,9874171674824⟩,⟨-109522921071186,-109522921069170⟩,⟨0,0⟩,⟨2186188521914418,2186188521974777⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2413489943680,2413490001536⟩,⟨-12195628068220,-12195628067696⟩,⟨0,0⟩,⟨108164909937337,108164909975027⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7804676630154,7804676630256⟩,⟨-49762644248138,-49762644246785⟩,⟨-22149191732105,-22149191731474⟩,⟨634573571662061,634573571688241⟩,⟨337846670957669,337846670971128⟩,⟨125716084754158,125716084759663⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6705165002378,6705165002480⟩,⟨-49762644248138,-49762644246785⟩,⟨-22149191732105,-22149191731474⟩,⟨634573571662067,634573571688236⟩,⟨337846670957672,337846670971127⟩,⟨125716084754158,125716084759663⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1987930235456,1987930274112⟩,⟨-8160068538297,-8160068537893⟩,⟨-3632020069123,-3632020068938⟩,⟨43496980743533,43496980757575⟩,⟨28444851162376,28444851169161⟩,⟨8617235828712,8617235831585⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99127803248,99127803250⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133075864211,133075864214⟩,⟨709356579173,709356579180⟩,⟨315732315191,315732315196⟩,⟨-1774257784753,-1774257784749⟩,⟨-1579432783384,-1579432783376⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4401420179136,4401420275648⟩,⟨-20355696606517,-20355696605589⟩,⟨-3632020069123,-3632020068938⟩,⟨151661890680870,151661890732602⟩,⟨28444851162376,28444851169161⟩,⟨8617235828712,8617235831585⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨674563654464,674564814998⟩,⟨-5159037871168,-5159017791112⟩,⟨5908842603488,5908865592394⟩,⟨68959888338268,68960442010636⟩,⟨-36562465347130,-36561703744080⟩,⟨-11883323409972,-11882281776962⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5075983833600,5075985090646⟩,⟨-25514734477685,-25514714396701⟩,⟨2276822534365,2276845523456⟩,⟨220621779019138,220622332743238⟩,⟨-8117614184754,-8116852574919⟩,⟨-3266087581260,-3265045945377⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457631473861,457631587202⟩,⟨1758492453713,1758495269342⟩,⟨205269694758,205271767373⟩,⟨-31065188110803,-31065103560661⟩,⟨1088715299495,1088802345665⟩,⟨-294458083911,-294364173959⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33780830796,33780832681⟩,⟨-677602995522,-677602986047⟩,⟨331972847757,331972866257⟩,⟨8470309304169,8470309329526⟩,⟨-6658977614141,-6658977521421⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨491412304657,491412419883⟩,⟨1080889458191,1080892283295⟩,⟨537242542515,537244633630⟩,⟨-22594878806634,-22594794231135⟩,⟨-5570262314646,-5570175175756⟩,⟨-294458083911,-294364173959⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500903595558,500903607567⟩,⟨2531120470889,2531120592376⟩,⟨0,0⟩,⟨3131155626176,3131158552760⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨223872293922,223872351783⟩,⟨1623671014360,1623672632750⟩,⟨244751137172,244752095688⟩,⟨-3917598437960,-3917544779181⟩,⟨-1300885643386,-1300841011560⟩,⟨-134146027002,-134103241307⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-674564814998,-674563654464⟩,⟨5159017791112,5159037871168⟩,⟨-5908865592394,-5908842603488⟩,⟨-68960442010636,-68959888338268⟩,⟨36561703744080,36562465347130⟩,⟨11882281776962,11883323409972⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3726855364138,3726856621184⟩,⟨-15196678815405,-15196658734421⟩,⟨-9540885661517,-9540862672426⟩,⟨82701448670234,82702002394334⟩,⟨65006554906456,65007316516291⟩,⟨20499517605674,20500559241557⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451067988589,451068140743⟩,⟨565121995927,565125237423⟩,⟨-84558389310,-84555245885⟩,⟨-15612900659370,-15612805701509⟩,⟨-8004907298340,-8004792715325⟩,⟨-4189798066224,-4189658390196⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨309795236084,309795236088⟩,⟨1975255459430,1975255459432⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-309795236088,-309795236084⟩,⟨-1975255459432,-1975255459430⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨789716391688,789716391692⟩,⟨-1975255459432,-1975255459430⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1427816725910,1427816753683⟩,⟨-9432196756219,-9432196686449⟩,⟨-4198240217435,-4198240186374⟩,⟨60560267720299,60560267732027⟩,⟨37455906731424,37455906814392⟩,⟨11997662823400,11997662825806⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1427816753683,-1427816725910⟩,⟨9432196686449,9432196756219⟩,⟨4198240186374,4198240217435⟩,⟨-60560267732027,-60560267720299⟩,⟨-37455906814392,-37455906731424⟩,⟨-11997662825806,-11997662823400⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-328305125907,-328305098134⟩,⟨9432196686449,9432196756219⟩,⟨4198240186374,4198240217435⟩,⟨-60560267732027,-60560267720299⟩,⟨-37455906814392,-37455906731424⟩,⟨-11997662825806,-11997662823400⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13356519655,-13356518523⟩,⟨417140028479,417140034171⟩,⟨39540128581,39540140963⟩,⟨-4383387956136,-4383387941275⟩,⟨2148309768954,2148309831276⟩,⟨2868848290220,2868848315198⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437711468934,437711622220⟩,⟨982262024406,982265271594⟩,⟨-45018260729,-45015104922⟩,⟨-19996288615506,-19996193642784⟩,⟨-5856597529386,-5856482884049⟩,⟨-1320949776004,-1320810074998⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99127803250,-99127803248⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4032841243,4032841245⟩,⟨25680863779,25680863783⟩,⟨39631760400,39631760401⟩,⟨-268390241407,-268390241398⟩,⟨252372404139,252372404144⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8852313644,8852313861⟩,⟨11639235338,11639236724⟩,⟨86993946002,86993948090⟩,⟨-762096333931,-762096319337⟩,⟨114381737068,114381750391⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1501927494425,1501927515869⟩,⟨-7835341113578,-7835340715239⟩,⟨-1483021079169,-1483021007224⟩,⟨118184876377041,118184884564378⟩,⟨25270294248698,25270295919239⟩,⟨5638237777051,5638238096969⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12092217049,12092217519⟩,⟨-47184231497,-47184224621⟩,⟨106893304557,106893309980⟩,⟨-255384875415,-255384723183⟩,⟨-275936004238,-275935916340⟩,⟨-189280643422,-189280622713⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12092217519,-12092217049⟩,⟨47184224621,47184231497⟩,⟨-106893309980,-106893304557⟩,⟨255384723183,255384875415⟩,⟨275935916340,275936004238⟩,⟨189280622713,189280643422⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-111220020769,-111220020297⟩,⟨-831995580871,-831995573993⟩,⟨-106893309980,-106893304557⟩,⟨2454407978735,2454408130967⟩,⟨275935916340,275936004238⟩,⟨189280622713,189280643422⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨80875463598,80875465177⟩,⟨-534265547956,-534265543980⟩,⟨647021444523,647021459998⟩,⟨3430300008879,3430300009668⟩,⟨-3723548505714,-3723548466510⟩,⟨-2553620134264,-2553620133968⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨110475486874,110475490609⟩,⟨-1306138969665,-1306138913259⟩,⟨774743309526,774743350707⟩,⟨20993523961549,20993525245265⟩,⟨-7117760120779,-7117759450426⟩,⟨-4818912364807,-4818912156547⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-110475490609,-110475486874⟩,⟨1306138913259,1306138969665⟩,⟨-774743350707,-774743309526⟩,⟨-20993525245265,-20993523961549⟩,⟨7117759450426,7117760120779⟩,⟨4818912156547,4818912364807⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨989036137167,989036140902⟩,⟨1306138913259,1306138969665⟩,⟨-774743350707,-774743309526⟩,⟨-20993525245265,-20993523961549⟩,⟨7117759450426,7117760120779⟩,⟨4818912156547,4818912364807⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119704817452,119704817907⟩,⟨796166983127,796166992375⟩,⟨190239942144,190239948210⟩,⟨-2451543081809,-2451542847550⟩,⟨-684024730379,-684024601074⟩,⟨-177886734001,-177886683924⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11250352067,11250352164⟩,⟨168319392516,168319394624⟩,⟨21625374760,21625375952⟩,⟨762588227810,762588281538⟩,⟨105947307306,105947334876⟩,⟨-17508898116,-17508891653⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨168116042828,168116189576⟩,⟨1673455581098,1673460935750⟩,⟨116757028711,116759909876⟩,⟨-1666235503867,-1666024241896⟩,⟨433082471195,433231129553⟩,⟨-608341958850,-608217620341⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-168116189576,-168116042828⟩,⟨-1673460935750,-1673455581098⟩,⟨-116759909876,-116757028711⟩,⟨1666024241896,1666235503867⟩,⟨-433231129553,-433082471195⟩,⟨608217620341,608341958850⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨55756104346,55756308955⟩,⟨-49789921390,-49782948348⟩,⟨127991227296,127995066977⟩,⟨-2251574196064,-2251309275314⟩,⟨-1734116772939,-1733923482755⟩,⟨474071593339,474238717543⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29706000542297,29706026793941⟩,⟨-270677987273787,-270677323788948⟩,⟨-90743821557682,-90743317650775⟩,⟨4013770487900931,4013794410107997⟩,⟨1474829257118324,1474850555579423⟩,⟨340972779175777,340994710318345⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13032370881,13032370981⟩,⟨173358827626,173358830300⟩,⟨41423186386,41423187868⟩,⟨619221003620,619221083447⟩,⟨126568384096,126568424808⟩,⟨27098097205,27098112459⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352101430015,352101743875⟩,⟨1475401842005,1475413942140⟩,⟨43573937065,43580947114⟩,⟨-21050539930557,-21050028539091⟩,⟨-3604532620792,-3604170884632⟩,⟨-2063768013321,-2063468762992⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352101743875,-352101430015⟩,⟨-1475413942140,-1475401842005⟩,⟨-43580947114,-43573937065⟩,⟨21050028539091,21050539930557⟩,⟨3604170884632,3604532620792⟩,⟨2063468762992,2063768013321⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨85609725059,85610192205⟩,⟨-493151917734,-493136570411⟩,⟨-88599207843,-88589041987⟩,⟨1053739923585,1054346287773⟩,⟨-2252426644754,-2251950263257⟩,⟨742518986988,742957938323⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨232203667459,232203667464⟩,⟨1588536384663,1588536384672⟩,⟨315732315191,315732315196⟩,⟨-3973281040305,-3973281040301⟩,⟨-1579432783384,-1579432783376⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1661982293852,-1661980850398⟩,⟨-4111020896818,-4110978951431⟩,⟨443048927861,443075926301⟩,⟨41299484693428,41301034540908⟩,⟨-7769443905165,-7768208710794⟩,⟨2332703871179,2333883311861⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-180941504232,-180941346393⟩,⟨-1651027971223,-1651022343690⟩,⟨-239324740030,-239321541581⟩,⟨2248312972937,2248546111109⟩,⟨-202402183231,-202239776121⟩,⟨676165071214,676303135724⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51262163227,51262321071⟩,⟨-62491586560,-62485959018⟩,⟨76407575161,76410773615⟩,⟨-1724968067368,-1724734929192⟩,⟨-1781834966615,-1781672559497⟩,⟨324664863822,324802928335⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4341259012,4341298633⟩,⟨-28884510746,-28883076626⟩,⟨5472728819,5473614163⟩,⟨-77221267684,-77161094196⟩,⟨-302639687271,-302594793327⟩,⟨53937202934,53975799978⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2389978707,2389993426⟩,⟨-5827066662,-5826523976⟩,⟨7124649690,7124969872⟩,⟨-153743479738,-153719966096⟩,⟨-174834033948,-174817232930⟩,⟨40892956867,40906813088⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4321110221,4321136918⟩,⟨-28272836416,-28271745788⟩,⟨4986579775,4987207543⟩,⟨-96938301849,-96887146041⟩,⟨-287903704617,-287868772320⟩,⟨45594141176,45621425513⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4321136918,-4321110221⟩,⟨28271745788,28272836416⟩,⟨-4987207543,-4986579775⟩,⟨96887146041,96938301849⟩,⟨287868772320,287903704617⟩,⟨-45621425513,-45594141176⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨20122094,20188412⟩,⟨-612764958,-610240210⟩,⟨485521276,487034388⟩,⟨19665878357,19777207653⟩,⟨-14770914951,-14691088710⟩,⟨8315777421,8381658802⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨55756104346,55756308955⟩,⟨-49789921390,-49782948348⟩,⟨127991227296,127995066977⟩,⟨-2251574196064,-2251309275314⟩,⟨-1734116772939,-1733923482755⟩,⟨474071593339,474238717543⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨20122094,20188412⟩,⟨-612764958,-610240210⟩,⟨485521276,487034388⟩,⟨19665878357,19777207653⟩,⟨-14770914951,-14691088710⟩,⟨8315777421,8381658802⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110380659508,-109951162777⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439375154380,439804651111⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨43937515437,45526653338⟩,⟨-113816633344,-109951162777⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨153888678214,155907312846⟩,⟨985694994432,989560464999⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨43508018706,45956150069⟩,⟨-113816633344,-109951162777⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2162070810560,-2147741704512⟩,⟨6951457811918,7070261765073⟩,⟨3098623678248,3142338562257⟩,⟨-45464368146570,-43949299389058⟩,⟨-28062232248567,-27344603604983⟩,⟨-8980615930201,-8732484911342⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-306574884469,-300599942468⟩,⟨-972931177169,-922875855902⟩,⟨-431142049264,-412683931875⟩,⟨6017041296629,6575286032247⟩,⟨3724340289218,3991103866551⟩,⟨1203054868357,1291664074928⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨300599942468,306574884469⟩,⟨922875855902,972931177169⟩,⟨412683931875,431142049264⟩,⟨-6575286032247,-6017041296629⟩,⟨-3991103866551,-3724340289218⟩,⟨-1291664074928,-1203054868357⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-155907312846,-153888678214⟩,⟨-989560464999,-985694994432⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨943604314930,945622949562⟩,⟨-989560464999,-985694994432⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-168131232448,-165781580608⟩,⟨-1153060896860,-1146104912449⟩,⟨-512471509716,-510878137443⟩,⟨-1209218164030,-1194672650254⟩,⟨741013528784,748651488359⟩,⟨-238857908945,-237374907844⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-144599427532,-142274270545⟩,⟨-843056816066,-832272708236⟩,⟨-374497642962,-371184721067⟩,⟨1014955436089,1050237812552⟩,⟨1383797429113,1400536661071⟩,⟨202876254327,206261320066⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨142274270545,144599427532⟩,⟨832272708236,843056816066⟩,⟨371184721067,374497642962⟩,⟨-1050237812552,-1014955436089⟩,⟨-1400536661071,-1383797429113⟩,⟨-206261320066,-202876254327⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨442874213013,451174312001⟩,⟨1755148564138,1815987993235⟩,⟨783868652942,805639692226⟩,⟨-7625523844799,-7031996732718⟩,⟨-5391640527622,-5108137718331⟩,⟨-1497925394994,-1405931122684⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨799832809839,810025369464⟩,⟨4161486423612,4236617700337⟩,⟨783868652942,805639692226⟩,⟨-19929309536572,-19119216639775⟩,⟨-5391640527622,-5108137718331⟩,⟨-1497925394994,-1405931122684⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨87016037412,91912300138⟩,⟨-227633266688,-219902325554⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13153036294375,13893138041792⟩,⟨31468946646819,36344339400640⟩,⟨-140440013382287,-125752861014895⟩,⟨150580380209832,190153009708169⟩,⟨-420090465384546,-250633282776086⟩,⟨2404582744167513,2839300566867880⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9568093425736,10235266268244⟩,⟨72674154569099,80308156149850⟩,⟨-94086973045113,-81298276850060⟩,⟨95927742779961,191455141961513⟩,⟨-896319639893420,-692753587866541⟩,⟨1524463359741161,1895628680429354⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨81545019392,87181409536⟩,⟨-725534104695,-574087925350⟩,⟨642213994344,850017121852⟩,⟨6308680755337,11278981482093⟩,⟨-8629567481109,-894568398912⟩,⟨-7066469165091,4479028035702⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1181056647168,1186693037312⟩,⟨-725534104695,-574087925350⟩,⟨642213994344,850017121852⟩,⟨6308680755337,11278981482093⟩,⟨-8629567481109,-894568398912⟩,⟨-7066469165091,4479028035702⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨78662794688,83897544192⟩,⟨-675440239360,-531912069458⟩,⟨595033199066,791328435878⟩,⟨5430278944446,10242910362215⟩,⟨-7745886639908,-342727740870⟩,⟨-7148097217940,3847757682873⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨84496802220,90549866891⟩,⟨-784358015863,-612433401280⟩,⟨685109864775,918933705297⟩,⟨6839813154483,12807121597385⟩,⟨-10062886575708,-1053515803826⟩,⟨-7558973550240,5718149753286⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-87181409536,-81545019392⟩,⟨574087925350,725534104695⟩,⟨-850017121852,-642213994344⟩,⟨-11278981482093,-6308680755337⟩,⟨894568398912,8629567481109⟩,⟨-4479028035702,7066469165091⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1012330218240,1017966608384⟩,⟨574087925350,725534104695⟩,⟨-850017121852,-642213994344⟩,⟨-11278981482093,-6308680755337⟩,⟨894568398912,8629567481109⟩,⟨-4479028035702,7066469165091⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-90832069824,-84727255552⟩,⟨620075692158,788016765763⟩,⟨-923220202703,-693659053730⟩,⟨-12815091453287,-7163737743482⟩,⟨1357421385062,10034411053173⟩,⟨-5639954515886,7237415124155⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-84095530885,-78009144184⟩,⟨510971946195,685335053307⟩,⟨-805261433306,-568437105069⟩,⟨-10731002513184,-4623970091854⟩,⟨-681519191333,8496916495892⟩,⟨-4995119786484,8498129567454⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨401271335,12540722707⟩,⟨-273386069668,72901652027⟩,⟨-120151568531,350496600228⟩,⟨-3891189358701,8183151505531⟩,⟨-10744405767041,7443400692066⟩,⟨-12554093336724,14216279320740⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨200635667,6270361354⟩,⟨-136693034834,36450826014⟩,⟨-60075784266,175248300114⟩,⟨-1945594679351,4091575752766⟩,⟨-5372202883521,3721700346033⟩,⟨-6277046668362,7108139660370⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6270361354,-200635667⟩,⟨-36450826014,136693034834⟩,⟨-175248300114,60075784266⟩,⟨-4091575752766,1945594679351⟩,⟨-3721700346033,5372202883521⟩,⟨-7108139660370,6277046668362⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755853022262,761922767213⟩,⟨-36450826014,136693034834⟩,⟨-175248300114,60075784266⟩,⟨-4091575752766,1945594679351⟩,⟨-3721700346033,5372202883521⟩,⟨-7108139660370,6277046668362⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6047767044,6912703765⟩,⟨-115056693020,-85154189956⟩,⟨95259297490,134797466332⟩,⟨1535260599782,2746159663394⟩,⟨-2490295206676,-803329198022⟩,⟨-370393404819,2024566283482⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6912703765,-6047767044⟩,⟨85154189956,115056693020⟩,⟨-134797466332,-95259297490⟩,⟨-2746159663394,-1535260599782⟩,⟨803329198022,2490295206676⟩,⟨-2024566283482,370393404819⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092598924011,1093463860732⟩,⟨85154189956,115056693020⟩,⟨-134797466332,-95259297490⟩,⟨-2746159663394,-1535260599782⟩,⟨803329198022,2490295206676⟩,⟨-2024566283482,370393404819⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6934525632,-6064460864⟩,⟨85625163640,115784638855⟩,⟨-135650308975,-95786160846⟩,⟨-2775726950334,-1550419985018⟩,⟨815231686299,2520335643555⟩,⟨-2054111017803,364392222859⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3467262816,-3032230432⟩,⟨42812581820,57892319428⟩,⟨-67825154488,-47893080423⟩,⟨-1387863475167,-775209992509⟩,⟨407615843149,1260167821778⟩,⟨-1027055508902,182196111430⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3032230432,3467262816⟩,⟨-57892319428,-42812581820⟩,⟨47893080423,67825154488⟩,⟨775209992509,1387863475167⟩,⟨-1260167821778,-407615843149⟩,⟨-182196111430,1027055508902⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765155614048,765590665696⟩,⟨-57892319428,-42812581820⟩,⟨47893080423,67825154488⟩,⟨775209992509,1387863475167⟩,⟨-1260167821778,-407615843149⟩,⟨-182196111430,1027055508902⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273149731002,273365965183⟩,⟨21288547489,28764173255⟩,⟨-33699366583,-23814824372⟩,⟨-686539915849,-383815149945⟩,⟨200832299505,622573801669⟩,⟨-506141570871,92598351205⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530311228096,1531181331392⟩,⟨-115784638856,-85625163640⟩,⟨95786160846,135650308976⟩,⟨1550419985018,2775726950334⟩,⟨-2520335643556,-815231686298⟩,⟨-364392222860,2054111017804⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1187588875369,1194201059924⟩,⟨-855880404662,-669747345358⟩,⟨749225160243,1002727498973⟩,⟨8115302352020,14532128175148⟩,⟨-11617221749565,-1888688389870⟩,⟨-7390659073691,6967618851972⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1275666122962,1288890492072⟩,⟨-1711760809325,-1339494690716⟩,⟨1498450320485,2005454997946⟩,⟨16230604704044,29064256350283⟩,⟨-23234443499121,-3777376779740⟩,⟨-14776472076050,13935237703938⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨163390050304,174729614016⟩,⟨-1475386764568,-1142680465753⟩,⟨1278280475456,1728525238332⟩,⟨11866057209149,23863280028790⟩,⟨-18697571884471,-902927675768⟩,⟨-15453402805473,10524829967535⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨56057660329,60413641044⟩,⟨-505659761210,-383814951391⟩,⟨427590743802,593795347606⟩,⟨3832042381658,8018310021315⟩,⟨-6342905065746,32318012320⟩,⟨-5731389580258,3694409408244⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380172514545,380689800774⟩,⟨842668393,18785317194⟩,⟨-23133795298,580334481⟩,⟨-576966339743,152601362666⟩,⟨-343388607165,671567981674⟩,⟨-803765592579,635506372840⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175619144922,3179940088677⟩,⟨-157129147791,-7029329065⟩,⟨-4854188061,193501845234⟩,⟨-1276397796985,4841543680592⟩,⟨-5636430442224,2872742060671⟩,⟨-5316262238497,6746619483963⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨161906227149,174724627013⟩,⟨-1471071745833,-1108896099581⟩,⟨1234704625889,1727970612903⟩,⟨11002513234593,23600613109868⟩,⟨-18828108328792,250812301750⟩,⟨-16873323181458,11264446056823⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨325296277453,349454241029⟩,⟨-2946458510401,-2251576565334⟩,⟨2512985101345,3456495851235⟩,⟨22868570443742,47463893138658⟩,⟨-37525680213263,-652115374018⟩,⟨-32326725986931,21789276024358⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519606866203,527985596998⟩,⟨-50518272882,189446901204⟩,⟨-242881778418,83260798040⟩,⟨-5679698540626,2730444735313⟩,⟨-5201588370946,7460431567442⟩,⟨-9870530664261,8755408515167⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357200788319,365875391357⟩,⟨-52511071230,196920028255⟩,⟨-252462755341,86545193394⟩,⟨-5913166830912,2873481317217⟩,⟨-5452069016736,7770250479965⟩,⟨-10279800359373,9158852257433⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714401576638,731750782714⟩,⟨-105022142460,393840056510⟩,⟨-504925510682,173090386788⟩,⟨-11826333661824,5746962634434⟩,⟨-10904138033472,15540500959930⟩,⟨-20559600718746,18317704514866⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523398524331,1525133564348⟩,⟨-30630448900,29431529380⟩,⟨-39011305486,40391011486⟩,⟨-1195739678376,1240466350552⟩,⟨-1717006445534,1675063520378⟩,⟨-2388958506342,2424504422623⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989819734632,1015012166550⟩,⟨-166061590266,565883268637⟩,⟨-726345567420,266974996363⟩,⟨-17222054204333,8818260958074⟩,⟨-16295337136705,22699571087474⟩,⟨-30145245806893,27057899017628⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67858105054,67965584932⟩,⟨10577352476,14302979226⟩,⟨-16757003090,-11832549482⟩,⟨-340557461602,-189196047902⟩,⟨98021617606,308652497864⟩,⟨-250647159521,48110241478⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49362951209,50071183110⟩,⟨264527167442,272420926349⟩,⟨36032582811,41192571760⟩,⟨-1402743097196,-1207378325472⟩,⟨-319002408314,-122172549295⟩,⟨-301805036794,-68197218696⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2129902400007,2132325125425⟩,⟨-322483679118,-238347910136⟩,⟨266632264244,377813595518⟩,⟨4329116163689,7755347487526⟩,⟨-7048214880872,-2284213967390⟩,⟨-998216965562,5754586617321⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2964419361414,2969478759505⟩,⟨-673636790194,-497602490769⟩,⟨556652159155,789215561149⟩,⟨9065802694521,16251099551958⟩,⟨-14782708680210,-4799933839777⟩,⟨-2050341675170,12090685408050⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨133088622806,135228505959⟩,⟨682520899966,713394026176⟩,⟨122139389985,147190279465⟩,⟨-3715219075186,-2754607210559⟩,⟨-1426049313357,-365653831248⟩,⟨-871979363806,425870352747⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8939874111906,9083615068862⟩,⟨-48690839153508,-45121040724139⟩,⟨-10046086677802,-8074560632222⟩,⟨637572290868670,775566876885967⟩,⟨105680469495795,205031195764249⟩,⟨-14480658389619,81735743226773⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8047994761991,8385522788696⟩,⟨-46320777713882,-35944531891508⟩,⟨-15274730454260,-5063394712381⟩,⟨381566189610907,803522980727210⟩,⟨-56479716174376,410489491089419⟩,⟨-267291362815466,312266069269874⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16095989523982,16771045577392⟩,⟨-92641555427764,-71889063783016⟩,⟨-30549460908520,-10126789424762⟩,⟨763132379221814,1607045961454420⟩,⟨-112959432348752,820978982178838⟩,⟨-534582725630932,624532138539748⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10952333724070,10995116277821⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨2173453475238562,2199023255588622⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9852822096294,9895604650045⟩,⟨-109951162778820,-109097176394608⟩,⟨0,0⟩,⟨2173453475238575,2199023255588602⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2411110045440,2415874025920⟩,⟨-12269843176037,-12121908488212⟩,⟨0,0⟩,⟨104571265817406,111755106875729⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7754131589765,7855846405631⟩,⟨-50515964607269,-49024055091935⟩,⟨-22451539825470,-21852552661855⟩,⟨619890944546097,649672243686862⟩,⟨331002186189480,344872068980200⟩,⟨123168933183822,128330319740810⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6654619961989,6756334777855⟩,⟨-50515964607269,-49024055091935⟩,⟨-22451539825470,-21852552661855⟩,⟨619890944546102,649672243686854⟩,⟨331002186189482,344872068980197⟩,⟨123168933183822,128330319740809⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1979610472128,1996289228864⟩,⟨-8346515772704,-7978071008387⟩,⟨-3709562565650,-3556238188046⟩,⟨37520405863500,49453306623816⟩,⟨25706891060807,31177481920930⟩,⟨7528827410441,9701191582639⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨98913096826,99342593558⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨132067744545,134086379178⟩,⟨705609942955,713101859099⟩,⟨314710205396,316753821306⟩,⟨-1781208837000,-1767320322048⟩,⟨-1583382643350,-1575482923412⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4390720517568,4412163254784⟩,⟨-20616358948741,-20099979496599⟩,⟨-3709562565650,-3556238188046⟩,⟨142091671680906,161208413499545⟩,⟨25706891060807,31177481920930⟩,⟨7528827410441,9701191582639⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨650592554906,698908482058⟩,⟨-5892917020802,-4503153130668⟩,⟨5025970202690,6912991702470⟩,⟨45737140887484,94927786277316⟩,⟨-75051360426526,-1304230748036⟩,⟨-64653451973862,43578552048716⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5041313072474,5111071736842⟩,⟨-26509275969543,-24603132627267⟩,⟨1316407637040,3356753514424⟩,⟨187828812568390,256136199776861⟩,⟨-49344469365719,29873251172894⟩,⟨-57124624563421,53279743631355⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨453521250226,461793317481⟩,⟨1633957427504,1875536512914⟩,⟨118425265159,303287924961⟩,⟨-35739728956998,-26266890090767⟩,⟨-3406252241832,5384497732011⟩,⟨-5161299086610,4813908086767⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32744145870,34824637676⟩,⟨-698472785006,-656925453974⟩,⟨330673852191,333275037186⟩,⟨8127827541019,8820691407275⟩,⟨-6692236630045,-6625935308195⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨486265396096,496617955157⟩,⟨935484642498,1218611058940⟩,⟨449099117350,636562962147⟩,⟨-27611901415979,-17446198683492⟩,⟨-10098488871877,-1241437576184⟩,⟨-5161299086610,4813908086767⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500409295618,501398026980⟩,⟨2510857612204,2551553037358⟩,⟨0,0⟩,⟨1957166706152,4308831445771⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨221308914063,226467148313⟩,⟨1536198744681,1708173142558⟩,⟨204393812033,290284709326⟩,⟨-7453411832207,-338055028904⟩,⟨-3579533275485,912220690666⟩,⟨-2353649668913,2195232825005⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-698908482058,-650592554906⟩,⟨4503153130668,5892917020802⟩,⟨-6912991702470,-5025970202690⟩,⟨-94927786277316,-45737140887484⟩,⟨1304230748036,75051360426526⟩,⟨-43578552048716,64653451973862⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3691812035510,3761570699878⟩,⟨-16113205818073,-14207062475797⟩,⟨-10622554268120,-8582208390736⟩,⟨47163885403590,115471272612061⟩,⟨27011121808843,106228842347456⟩,⟨-36049724638275,74354643556501⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443441684923,458726749611⟩,⟨404195684205,733133093879⟩,⟨-238732277882,52804341904⟩,⟨-21329496168818,-10087004446287⟩,⟨-13703893761284,-1909343251644⟩,⟨-11720413923706,2975614434509⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨307777356428,311814625692⟩,⟨1971389988864,1979120929998⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-311814625692,-307777356428⟩,⟨-1979120929998,-1971389988864⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨787697002084,791734271348⟩,⟨-1979120929998,-1971389988864⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1418205314793,1437484204885⟩,⟨-9603464039876,-9264919647032⟩,⟨-4268206239949,-4129853071415⟩,⟨55488717269703,65657701090632⟩,⟨35128246245676,39797226418016⟩,⟨11078123490688,12920915950172⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1437484204885,-1418205314793⟩,⟨9264919647032,9603464039876⟩,⟨4129853071415,4268206239949⟩,⟨-65657701090632,-55488717269703⟩,⟨-39797226418016,-35128246245676⟩,⟨-12920915950172,-11078123490688⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-337972577109,-318693687017⟩,⟨9264919647032,9603464039876⟩,⟨4129853071415,4268206239949⟩,⟨-65657701090632,-55488717269703⟩,⟨-39797226418016,-35128246245676⟩,⟨-12920915950172,-11078123490688⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-14126197560,-12610808786⟩,⟨398485134400,436380228611⟩,⟨28230545761,51044697608⟩,⟨-4732503889886,-4048689811857⟩,⟨1915816702021,2376337204487⟩,⟨2760602100537,2976200183549⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429315487363,446115940825⟩,⟨802680818605,1169513322490⟩,⟨-210501732121,103849039512⟩,⟨-26062000058704,-14135694258144⟩,⟨-11788077059263,466993952843⟩,⟨-8959811823169,5951814618058⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99342593558,-98913096826⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨3914022151,4152209966⟩,⟨24488913663,26873610374⟩,⟨39526600801,39737037424⟩,⟨-274018913489,-262766099163⟩,⟨251814268106,252930624064⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8583027125,9123337993⟩,⟨7365543403,15896001924⟩,⟨86677559241,87311197222⟩,⟨-829614595812,-694155508943⟩,⟨108761645553,119972071186⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1492454267715,1511473153819⟩,⟨-8006090570789,-7667448955409⟩,⟨-1522446630687,-1444261081828⟩,⟨114009424166293,122475728901235⟩,⟨24251348719040,26317210722530⟩,⟨5385645988426,5897683656993⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11650422914,12541641309⟩,⟨-56433722053,-38001910253⟩,⟨105021625145,108750462995⟩,⟨-481962953651,-28701594798⟩,⟨-320824621152,-230828077729⟩,⟨-199750621014,-178773452335⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12541641309,-11650422914⟩,⟨38001910253,56433722053⟩,⟨-108750462995,-105021625145⟩,⟨28701594798,481962953651⟩,⟨230828077729,320824621152⟩,⟨178773452335,199750621014⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-111884234867,-110563519740⟩,⟨-841607391969,-822316586707⟩,⟨-108750462995,-105021625145⟩,⟨2227724850350,2680986209203⟩,⟨230828077729,320824621152⟩,⟨178773452335,199750621014⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨78333805005,83438651366⟩,⟨-555505403658,-513655810142⟩,⟨636022780641,657794235130⟩,⟨3080308386728,3794983268942⟩,⟨-3962042006528,-3480603439314⟩,⟨-2669731999153,-2436732747400⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨106328681418,114701180365⟩,⟨-1371198690661,-1243486856166⟩,⟨747790199683,801359293452⟩,⟨19467616592783,22601014391770⟩,⟨-7833775119123,-6393487421281⟩,⟨-5107961747715,-4530905531360⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-114701180365,-106328681418⟩,⟨1243486856166,1371198690661⟩,⟨-801359293452,-747790199683⟩,⟨-22601014391770,-19467616592783⟩,⟨6393487421281,7833775119123⟩,⟨4530905531360,5107961747715⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨984810447411,993182946358⟩,⟨1243486856166,1371198690661⟩,⟨-801359293452,-747790199683⟩,⟨-22601014391770,-19467616592783⟩,⟨6393487421281,7833775119123⟩,⟨4530905531360,5107961747715⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨118290422136,121119505947⟩,⟨781361948687,811359926082⟩,⟨184153152168,196301269580⟩,⟨-2769157660683,-2142688627955⟩,⟨-826119479359,-540663019616⟩,⟨-235309877080,-119679739315⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11117928713,11385129267⟩,⟨165379271796,171280769990⟩,⟨21121305552,22132485072⟩,⟨684384718746,840369287745⟩,⟨91796768274,120060628996⟩,⟨-20589875293,-14441245954⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨162757773153,173659392969⟩,⟨1461746198647,1885655468550⟩,⟨-7131574042,235191685505⟩,⟨-11127788856720,7832909976714⟩,⟨-6449609780692,7428154436488⟩,⟨-7079395934140,5866378121647⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-173659392969,-162757773153⟩,⟨-1885655468550,-1461746198647⟩,⟨-235191685505,7131574042⟩,⟨-7832909976714,11127788856720⟩,⟨-7428154436488,6449609780692⟩,⟨-5866378121647,7079395934140⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47649521094,63709375160⟩,⟨-349456723869,246426943911⟩,⟨-30797873472,297416283368⟩,⟨-15286321808921,10789733827816⟩,⟨-11007687711973,7361830471358⟩,⟨-8220027790560,9274628759145⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28979947656750,30449753142362⟩,⟨-295512232407504,-246225036670618⟩,⟨-112048658247645,-70293272996301⟩,⟨2966503434815089,5078600779282114⟩,⟨477234634816576,2510597981100152⟩,⟨-794872229960843,1488020807853735⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨12726217363,13342227904⟩,⟨168124888206,178754841532⟩,⟨39624054092,43248133422⟩,⟨500453983666,736409469657⟩,⟨79728274870,173378296956⟩,⟨9843947548,44341907697⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨335426296304,369498180632⟩,⟨845337951254,2100502989169⟩,⟨-315299731614,384104637543⟩,⟨-48560638587103,6721367813804⟩,⟨-22215026252164,15644958644532⟩,⟨-18200698837358,14218225246165⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-369498180632,-335426296304⟩,⟨-2100502989169,-845337951254⟩,⟨-384104637543,315299731614⟩,⟨-6721367813804,48560638587103⟩,⟨-15644958644532,22215026252164⟩,⟨-14218225246165,18200698837358⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59817306731,110689644521⟩,⟨-1297822170564,324175371236⟩,⟨-594606369664,419148771126⟩,⟨-32783367872508,34424944328959⟩,⟨-27433035703795,22682020205007⟩,⟨-23178037069334,24152513455416⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨230980841371,233428972736⟩,⟨1584360251715,1592711161321⟩,⟨314710205396,316753821306⟩,⟨-3980232092552,-3966343577600⟩,⟨-1583382643350,-1575482923412⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1706590048658,-1618563378969⟩,⟨-5608242651142,-2611040708058⟩,⟨-640471161192,1571221292783⟩,⟨-23387231373509,105977938561049⟩,⟨-65721784011918,48934824162341⟩,⟨-58999558940416,63488134433619⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187993776806,-174132351596⟩,⟨-1877130084604,-1431130789055⟩,⟨-375238727267,-98005331442⟩,⟨-7699035676931,12261331680917⟩,⟨-7917742943484,7394922816972⟩,⟨-6551762263224,7919965755539⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨42987064565,59296621140⟩,⟨-292769832889,161580372266⟩,⟨-60528521871,218748489864⟩,⟨-11679267769483,8294988103317⟩,⟨-9501125586834,5819439893560⟩,⟨-6903605984114,7568808893875⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2592301842,6413727615⟩,⟨-110380533531,43592009358⟩,⟨-37553951138,54228265971⟩,⟨-4020223161502,3905887627093⟩,⟨-3182048276556,2332071708711⟩,⟨-2492216887075,2559927671043⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1680644090,3197864570⟩,⟨-31578132370,17428046920⟩,⟨-6528601862,23594195826⟩,⟨-1345773807237,1050609975162⟩,⟨-1141284161620,691977375102⟩,⟨-768706797852,903411446925⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3025907645,5806089209⟩,⟨-81609061992,19447838402⟩,⟨-22642467481,37402122233⟩,⟨-2650651590118,2530760970398⟩,⟨-2270743518635,1503140521437⟩,⟨-1543372593570,1712514996803⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5806089209,-3025907645⟩,⟨-19447838402,81609061992⟩,⟨-37402122233,22642467481⟩,⟨-2530760970398,2650651590118⟩,⟨-1503140521437,2270743518635⟩,⟨-1712514996803,1543372593570⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3213787367,3387819970⟩,⟨-129828371933,125201071350⟩,⟨-74956073371,76870733452⟩,⟨-6550984131900,6556539217211⟩,⟨-4685188797993,4602815227346⟩,⟨-4204731883878,4103300264613⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47649521094,63709375160⟩,⟨-349456723869,246426943911⟩,⟨-30797873472,297416283368⟩,⟨-15286321808921,10789733827816⟩,⟨-11007687711973,7361830471358⟩,⟨-8220027790560,9274628759145⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3213787367,3387819970⟩,⟨-129828371933,125201071350⟩,⟨-74956073371,76870733452⟩,⟨-6550984131900,6556539217211⟩,⟨-4685188797993,4602815227346⟩,⟨-4204731883878,4103300264613⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (513/5120) u, BivariateJet2.affineZ (521/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000000


