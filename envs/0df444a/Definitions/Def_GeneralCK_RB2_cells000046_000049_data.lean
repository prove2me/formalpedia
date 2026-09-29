-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000046_000049_data
-- name    : GeneralCK_RB2_cells000046_000049_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T03:53:48.94682+00:00
-- url     : https://prove2.me/theorems/6f418326-43e1-4857-b962-32084493a59b
-- title:
--   Exact certificate data for RB2 cells 000046–000049
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000046 through 000049. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000046Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2114670900800,-2114670861888⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2114670900800,-2114670861888⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-173692417408,-173692417344⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-173692417408,-173692417344⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨84369191616,84369191680⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-91385211072,-91385211008⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨84369315136,84369315200⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-91385356032,-91385355968⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7016040896,-7016040832⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7016019456,-7016019392⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨175754402688,175754402752⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨175754671104,175754671168⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1940978444544,1940978483136⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1940978444544,1940978483136⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2497885341504,-2497885283648⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-119669504256,-119669504192⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2121571235264,-2121571196288⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2107808467200,-2107808428352⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-174871115840,-174871115776⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-172515864512,-172515864448⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨81818723648,81818723712⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-88400188800,-88400188736⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨86941880512,86941880576⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-94411525056,-94411524992⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7469644480,-7469644416⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6581465088,-6581465024⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨170218912384,170218912448⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨181353405504,181353405568⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2378215779456,2378215837312⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1932937312576,1932937351168⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1949055331840,1949055370496⟩



end LaneCBRB2Cell000046Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000046
open Set LaneCBRB2Cell000046Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨113172388249,113172388250⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨119614839193,119614839194⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113172388250,-113172388249⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436583425638,436583425639⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨47495501577,47495501579⟩,⟨-119614839194,-119614839193⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨160667889826,160667889829⟩,⟨979896788582,979896788583⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47495501576,47495501580⟩,⟨-119614839194,-119614839193⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2114670900800,-2114670861888⟩,⟨6705807328476,6705807328610⟩,⟨2987706837340,2987706837404⟩,⟨-40898023079026,-40898023077395⟩,⟨-25746091264998,-25746091264106⟩,⟨-8118506362981,-8118506362636⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309009657317,-309009651624⟩,⟨-904721047445,-904721012724⟩,⟨-403089609788,-403089594315⟩,⟨5976288835665,5976288836267⟩,⟨3677836245460,3677836284695⟩,⟨1186329687508,1186329687640⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309009651624,309009657317⟩,⟨904721012724,904721047445⟩,⟨403089594315,403089609788⟩,⟨-5976288836267,-5976288835665⟩,⟨-3677836284695,-3677836245460⟩,⟨-1186329687640,-1186329687508⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160667889829,-160667889826⟩,⟨-979896788583,-979896788582⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938843737947,938843737950⟩,⟨-979896788583,-979896788582⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173692417408,-173692417344⟩,⟨-1147590242679,-1147590242672⟩,⟨-511297603193,-511297603189⟩,⟨-1197771202981,-1197771202965⟩,⟨754019983963,754019983977⟩,⟨-237764869809,-237764869804⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148311335955,-148311335899⟩,⟨-825100206490,-825100206422⟩,⟨-367615323209,-367615323176⟩,⟨1022744976024,1022744976057⟩,⟨1381493226637,1381493226726⟩,⟨203021099074,203021099085⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148311335899,148311335955⟩,⟨825100206422,825100206490⟩,⟨367615323176,367615323209⟩,⟨-1022744976057,-1022744976024⟩,⟨-1381493226726,-1381493226637⟩,⟨-203021099085,-203021099074⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨457320987523,457320993272⟩,⟨1729821219146,1729821253935⟩,⟨770704917491,770704932997⟩,⟨-6999033812324,-6999033811689⟩,⟨-5059329511421,-5059329472097⟩,⟨-1389350786725,-1389350786582⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨821779271794,821779283560⟩,⟨4110360796030,4110360888763⟩,⟨770704917491,770704932997⟩,⟨-18906865512236,-18906865511111⟩,⟨-5059329511421,-5059329472097⟩,⟨-1389350786725,-1389350786582⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨94991003152,94991003160⟩,⟨-239229678388,-239229678386⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12726740211158,12726740212231⟩,⟨32051603481744,32051603487418⟩,⟨-116985475565154,-116985475545158⟩,⟨161440442518075,161440442561611⟩,⟨-294621561758982,-294621561553978⟩,⟨2150684505452271,2150684506006122⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9512015188226,9512015325219⟩,⟨71532519900082,71532521324700⟩,⟨-78514566696403,-78514565249348⟩,⟨141456396241941,141456403482448⟩,⟨-693628738356940,-693628724193511⟩,⟨1427345954660967,1427345981420290⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨87690563584,87690696960⟩,⟨-653417884997,-653415858619⟩,⟨717193552501,717195775601⟩,⟨8400800624242,8400850643122⟩,⟨-4303116152374,-4303046057441⟩,⟨-1360695689682,-1360599922190⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1187202191360,1187202324736⟩,⟨-653417884997,-653415858619⟩,⟨717193552501,717195775601⟩,⟨8400800624242,8400850643122⟩,⟨-4303116152374,-4303046057441⟩,⟨-1360695689682,-1360599922190⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨84369191616,84369315200⟩,⟨-605154343195,-605152398504⟩,⟨664219260618,664221394136⟩,⟨7447221985089,7447271324156⟩,⟨-3619699261640,-3619631547367⟩,⟨-1661450362007,-1661358948903⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨91097980812,91098124487⟩,⟨-703556963857,-703554561724⟩,⟨772226123449,772228758897⟩,⟨9405047754592,9405111256356⟩,⟨-5028045614672,-5027961214433⟩,⟨-1031850073031,-1031738197019⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-87690696960,-87690563584⟩,⟨653415858619,653417884997⟩,⟨-717195775601,-717193552501⟩,⟨-8400850643122,-8400800624242⟩,⟨4303046057441,4303116152374⟩,⟨1360599922190,1360695689682⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1011820930816,1011821064192⟩,⟨653415858619,653417884997⟩,⟨-717195775601,-717193552501⟩,⟨-8400850643122,-8400800624242⟩,⟨4303046057441,4303116152374⟩,⟨1360599922190,1360695689682⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-91385356032,-91385211008⟩,⟨710044848590,710047144184⟩,⟨-779352423585,-779349905084⟩,⟨-9587457793251,-9587399271157⟩,⟨5179264346101,5179344385838⟩,⟨926099612649,926207445151⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-84096998937,-84096854393⟩,⟨599107273558,599109726809⟩,⟨-657586783277,-657584091727⟩,⟨-7280663049445,-7280597420732⟩,⟨3482237521355,3482324065381⟩,⟨1755860254145,1755974175130⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7000981875,7001270094⟩,⟨-104449690299,-104444834915⟩,⟨114639340172,114644667170⟩,⟨2124384705147,2124513835624⟩,⟨-1545808093317,-1545637149052⟩,⟨724010181114,724235978111⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3500490937,3500635047⟩,⟨-52224845150,-52222417457⟩,⟨57319670086,57322333585⟩,⟨1062192352573,1062256917812⟩,⟨-772904046659,-772818574526⟩,⟨362005090557,362117989056⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3500635047,-3500490937⟩,⟨52222417457,52224845150⟩,⟨-57322333585,-57319670086⟩,⟨-1062256917812,-1062192352573⟩,⟨772818574526,772904046659⟩,⟨-362117989056,-362005090557⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758622748569,758622911943⟩,⟨52222417457,52224845150⟩,⟨-57322333585,-57319670086⟩,⟨-1062256917812,-1062192352573⟩,⟨772818574526,772904046659⟩,⟨-362117989056,-362005090557⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6993682238,6993703513⟩,⟨-104225673098,-104225191346⟩,⟨114398256878,114398785480⟩,⟨2116618317069,2116633150557⟩,⟨-1538813742308,-1538796231774⟩,⟨718584921505,718606327703⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6993703513,-6993682238⟩,⟨104225191346,104225673098⟩,⟨-114398785480,-114398256878⟩,⟨-2116633150557,-2116618317069⟩,⟨1538796231774,1538813742308⟩,⟨-718606327703,-718584921505⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092517924263,1092517945538⟩,⟨104225191346,104225673098⟩,⟨-114398785480,-114398256878⟩,⟨-2116633150557,-2116618317069⟩,⟨1538796231774,1538813742308⟩,⟨-718606327703,-718584921505⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7016040896,-7016019392⟩,⟨104892382097,104892868977⟩,⟨-115131104072,-115130569843⟩,⟨-2140189408998,-2140174346172⟩,⟨1559630084103,1559647838837⟩,⟨-735261961147,-735240291953⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3508020448,-3508009696⟩,⟨52446191048,52446434489⟩,⟨-57565552036,-57565284921⟩,⟨-1070094704499,-1070087173086⟩,⟨779815042051,779823919419⟩,⟨-367630980574,-367620145976⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3508009696,3508020448⟩,⟨-52446434489,-52446191048⟩,⟨57565284921,57565552036⟩,⟨1070087173086,1070094704499⟩,⟨-779823919419,-779815042051⟩,⟨367620145976,367630980574⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765631393312,765631423328⟩,⟨-52446434489,-52446191048⟩,⟨57565284921,57565552036⟩,⟨1070087173086,1070094704499⟩,⟨-779823919419,-779815042051⟩,⟨367620145976,367630980574⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273129481065,273129486385⟩,⟨26056297836,26056418275⟩,⟨-28599696370,-28599564219⟩,⟨-529158287640,-529154579267⟩,⟨384699057943,384703435577⟩,⟨-179651581926,-179646230376⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531262786624,1531262846656⟩,⟨-104892868978,-104892382096⟩,⟨115130569842,115131104072⟩,⟨2140174346172,2140189408998⟩,⟨-1559647838838,-1559630084102⟩,⟨735240291952,735261961148⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1194801988610,1194802146107⟩,⟨-771584247294,-771581651040⟩,⟨846893104988,846895953395⟩,⟨10916575130399,10916643385263⟩,⟨-6175130548178,-6175039222181⟩,⟨-406188218424,-406066790709⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1290092349444,1290092664438⟩,⟨-1543168494588,-1543163302080⟩,⟨1693786209976,1693791906789⟩,⟨21833150260802,21833286770519⟩,⟨-12350261096355,-12350078444364⟩,⟨-812376291211,-812133727054⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨175754402688,175754671168⟩,⟨-1315201740519,-1315196993955⟩,⟨1443568887855,1443574095569⟩,⟨17034609065643,17034741308032⟩,⟨-8799055120802,-8798884420170⟩,⟨-2587668471708,-2587447897047⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨60503276808,60503381863⟩,⟨-446669551288,-446667856115⟩,⟨490265582512,490267442316⟩,⟨5649452864002,5649496979612⟩,⟨-2839230043770,-2839170753286⟩,⟨-1042491909363,-1042412876557⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380380706960,380380729283⟩,⟨10231546005,10231836616⟩,⟨-11230531239,-11230212366⟩,⟨-210276977889,-210267986270⟩,⟨153785814424,153796400597⟩,⟨-73544854411,-73531949760⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178199436899,3178199623416⟩,⟨-85490190972,-85487752791⟩,⟨93831921204,93834596502⟩,⟨1761453427398,1761529023457⟩,⟨-1290065069028,-1289976179831⟩,⟨619922850900,620031061021⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨174888082512,174888396444⟩,⟨-1295827537766,-1295822419665⟩,⟨1422303227602,1422308842818⟩,⟨16496442984122,16496578033862⟩,⟨-8354181108907,-8354001766960⟩,⟨-2895590029668,-2895352687101⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨350642485200,350643067612⟩,⟨-2611029278285,-2611019413620⟩,⟨2865872115457,2865882938387⟩,⟨33531052049765,33531319341894⟩,⟨-17153236229709,-17152886187130⟩,⟨-5483258501376,-5482800584148⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523421908516,523422133961⟩,⟨72063110324,72066475884⟩,⟨-79100638002,-79096945532⟩,⟨-1460876329179,-1460786456966⟩,⟨1060987599260,1061106280378⟩,⟨-493720033313,-493563578613⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361141944176,361142177500⟩,⟨74581359728,74584858961⟩,⟨-81864831834,-81860992698⟩,⟨-1506792994320,-1506699176718⟩,⟨1092428160354,1092551751148⟩,⟨-504788002481,-504625393364⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722283888352,722284355000⟩,⟨149162719456,149169717922⟩,⟨-163729663668,-163721985396⟩,⟨-3013585988640,-3013398353436⟩,⟨2184856320708,2185103502296⟩,⟨-1009576004962,-1009250786728⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524269083111,1524269164418⟩,⟨-667677632,-666708998⟩,⟨731784362,732847194⟩,⟨23541195615,23571091929⟩,⟨-20851607064,-20816341794⟩,⟨16633964249,16677039643⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001312739612,1001313439946⟩,⟨206347857339,206358207040⟩,⟨-226500125405,-226488770296⟩,⟨-4162495283773,-4162215018880⟩,⟨3015399180185,3015765486056⟩,⟨-1388881270735,-1388401710636⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67848044115,67848046759⟩,⟨12945280298,12945340388⟩,⟨-14208890900,-14208824966⟩,⟨-261661263110,-261659404176⟩,⟨189770523156,189772714308⟩,⟨-87766619303,-87763945056⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50709892353,50709895056⟩,⟨263315181322,263315241980⟩,⟨36938444333,36938496577⟩,⟨-1265472888386,-1265470999214⟩,⟨-214406846843,-214404902555⟩,⟨-171249895442,-171247799573⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132552000784,2132552167995⟩,⟨-292163446184,-292162078592⟩,⟨320679022846,320680523438⟩,⟨5981149561197,5981191935951⟩,⟨-4366133400790,-4366083573416⟩,⟨2072012914875,2072073575239⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2969952692493,2969953041799⟩,⟨-610333286604,-610330405757⟩,⟨669902675510,669905836531⟩,⟨12536507693777,12536597094806⟩,⟨-9166799318752,-9166694443397⟩,⟨4378829856144,4378957215548⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136975342074,136975365487⟩,⟨683106641034,683107022902⟩,⟨130672674244,130672974535⟩,⟨-3132381800829,-3132370694644⟩,⟨-861996293649,-861985194524⟩,⟨-215608299062,-215596422703⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8825863069001,8825864577594⟩,⟨-44015294905268,-44015255253058⟩,⟨-8419778039864,-8419755812567⟩,⟨640845898534587,640847399101983⟩,⟨139521040512114,139522057659287⟩,⟨29956397687814,29957249750083⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8037613160069,8037620155563⟩,⟨-38427886846309,-38427739338976⟩,⟨-9485935467012,-9485818402794⟩,⟨533676673488434,533681547159618⟩,⟨158751541955952,158756047790502⟩,⟨19601070478700,19605899960480⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16075226320138,16075240311126⟩,⟨-76855773692618,-76855478677952⟩,⟨-18971870934024,-18971636805588⟩,⟨1067353346976868,1067363094319236⟩,⟨317503083911904,317512095581004⟩,⟨39202140957400,39211799920960⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10682162303971,10682162304067⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848532,2016544728902914⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9582650676195,9582650676291⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848550,2016544728902902⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2380539576896,2380539634752⟩,⟨-11907831699843,-11907831699439⟩,⟨0,0⟩,⟨102414856889766,102414856913318⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7524377278504,7524377278646⟩,⟨-45890396266597,-45890396264815⟩,⟨-20446017008561,-20446017007741⟩,⟨559761530129057,559761530161911⟩,⟨300888454882259,300888454899159⟩,⟨111116068747675,111116068754480⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6424865650728,6424865650870⟩,⟨-45890396266597,-45890396264815⟩,⟨-20446017008561,-20446017007740⟩,⟨559761530129063,559761530161905⟩,⟨300888454882262,300888454899156⟩,⟨111116068747676,111116068754480⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1940978444544,1940978483136⟩,⟨-7853397571498,-7853397570942⟩,⟨-3499004440690,-3499004440437⟩,⟨39700251866795,39700251885080⟩,⟨26500111244412,26500111253260⟩,⟨7880741491284,7880741495010⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101523589692,101523589694⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137190038233,137190038237⟩,⟨693518827140,693518827148⟩,⟨308990527190,308990527196⟩,⟨-1746589471214,-1746589471210⟩,⟨-1556351696246,-1556351696236⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4321518021440,4321518117888⟩,⟨-19761229271341,-19761229270381⟩,⟨-3499004440690,-3499004440437⟩,⟨142115108756561,142115108798398⟩,⟨26500111244412,26500111253260⟩,⟨7880741491284,7880741495010⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨701284970400,701286135224⟩,⟨-5222058556570,-5222038827240⟩,⟨5731744230914,5731765876774⟩,⟨67062104099530,67062638683788⟩,⟨-34306472459418,-34305772374260⟩,⟨-10966517002752,-10965601168296⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5022802991840,5022804253112⟩,⟨-24983287827911,-24983268097621⟩,⟨2232739790224,2232761436337⟩,⟨209177212856091,209177747482186⟩,⟨-7806361215006,-7805661121000⟩,⟨-3085775511468,-3084859673286⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463781352707,463781469177⟩,⟨1681975855096,1681978678579⟩,⟨206160401241,206162399943⟩,⟨-30411683259717,-30411600034661⟩,⟨1052307706552,1052389539926⟩,⟨-284925596966,-284841032888⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34167524934,34167526923⟩,⟨-700204203220,-700204193153⟩,⟨314071324370,314071342618⟩,⟨8664240804795,8664240831429⟩,⟨-6436347433334,-6436347341287⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497948877641,497948996100⟩,⟨981771651876,981774485426⟩,⟨520231725611,520233742561⟩,⟨-21747442454922,-21747359203232⟩,⟨-5384039726782,-5383957801361⟩,⟨-284925596966,-284841032888⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507836879489,507836891833⟩,⟨2540279524621,2540279648204⟩,⟨0,0⟩,⟨3565745386739,3565748309078⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229990113590,229990173895⟩,⟨1603902265049,1603903914472⟩,⟨240282002910,240282940330⟩,⟨-3893224691745,-3893170974276⟩,⟨-1284824975053,-1284782356930⟩,⟨-131599999411,-131560938182⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-701286135224,-701284970400⟩,⟨5222038827240,5222058556570⟩,⟨-5731765876774,-5731744230914⟩,⟨-67062638683788,-67062104099530⟩,⟨34305772374260,34306472459418⟩,⟨10965601168296,10966517002752⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3620231886216,3620233147488⟩,⟨-14539190444101,-14539170713811⟩,⟨-9230770317464,-9230748671351⟩,⟨75052470072773,75053004698868⟩,⟨60805883618672,60806583712678⟩,⟨18846342659580,18847258497762⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451709412011,451709569398⟩,⟨469360091975,469363349425⟩,⟨-134380001090,-134376945721⟩,⟨-14727460865222,-14727367264116⟩,⟨-7445650795516,-7445542458499⟩,⟨-3978199669988,-3978072833441⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨321335779652,321335779658⟩,⟨1959793577164,1959793577166⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-321335779658,-321335779652⟩,⟨-1959793577166,-1959793577164⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨778175848118,778175848124⟩,⟨-1959793577166,-1959793577164⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1373721304172,1373721331497⟩,⟨-9017859593336,-9017859524107⟩,⟨-4017819099993,-4017819069142⟩,⟨56093861898112,56093861913282⟩,⟨35110730221815,35110730306322⟩,⟨11134972804477,11134972807574⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1373721331497,-1373721304172⟩,⟨9017859524107,9017859593336⟩,⟨4017819069142,4017819099993⟩,⟨-56093861913282,-56093861898112⟩,⟨-35110730306322,-35110730221815⟩,⟨-11134972807574,-11134972804477⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-274209703721,-274209676396⟩,⟨9017859524107,9017859593336⟩,⟨4017819069142,4017819099993⟩,⟨-56093861913282,-56093861898112⟩,⟨-35110730306322,-35110730221815⟩,⟨-11134972807574,-11134972804477⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11845011083,-11845009901⟩,⟨419374653198,419374659196⟩,⟨64676824090,64676836291⟩,⟨-4385170320705,-4385170304764⟩,⟨1901164249198,1901164311161⟩,⟨2709716961383,2709716986067⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439864400928,439864559497⟩,⟨888734745173,888738008621⟩,⟨-69703177000,-69700109430⟩,⟨-19112631185927,-19112537568880⟩,⟨-5544486546318,-5544378147338⟩,⟨-1268482708605,-1268355847374⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101523589694,-101523589692⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4385505066,4385505067⟩,⟨26673451161,26673451166⟩,⟨40312003485,40312003486⟩,⟨-284973009474,-284973009463⟩,⟨245185044806,245185044811⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9495004973,9495005207⟩,⟨10254870979,10254872409⟩,⟨87279040344,87279042468⟩,⟨-786253262815,-786253247479⟩,⟨94263805138,94263818079⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1471107685238,1471107706302⟩,⟨-7358160258710,-7358159881984⟩,⟨-1379677007115,-1379676939846⟩,⟨107453936529335,107453943983860⟩,⟨22858642039049,22858643550746⟩,⟨5075002871500,5075003158281⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12703980962,12703981458⟩,⟨-49821892811,-49821885880⟩,⟨104861852963,104861858353⟩,⟨-261299248045,-261299099051⟩,⟨-273436367358,-273436283773⟩,⟨-175211060823,-175211041255⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12703981458,-12703980962⟩,⟨49821885880,49821892811⟩,⟨-104861858353,-104861852963⟩,⟨261299099051,261299248045⟩,⟨273436283773,273436367358⟩,⟨175211041255,175211060823⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114227571152,-114227570654⟩,⟨-823344965398,-823344958465⟩,⟨-104861858353,-104861852963⟩,⟨2460322354603,2460322503597⟩,⟨273436283773,273436367358⟩,⟨175211041255,175211060823⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨83844265438,83844267113⟩,⟨-550399714398,-550399710144⟩,⟨619558747955,619558763305⟩,⟨3423655607766,3423655608838⟩,⟨-3533953256274,-3533953216942⟩,⟨-2438277915796,-2438277915396⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨112180662880,112180666729⟩,⟨-1297518625133,-1297518568958⟩,⟨723739165604,723739205244⟩,⟨20141506488825,20141507722103⟩,⟨-6440767447789,-6440766823343⟩,⟨-4430186440691,-4430186249509⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-112180666729,-112180662880⟩,⟨1297518568958,1297518625133⟩,⟨-723739205244,-723739165604⟩,⟨-20141507722103,-20141506488825⟩,⟨6440766823343,6440767447789⟩,⟨4430186249509,4430186440691⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨987330961047,987330964896⟩,⟨1297518568958,1297518625133⟩,⟨-723739205244,-723739165604⟩,⟨-20141507722103,-20141506488825⟩,⟨6440766823343,6440767447789⟩,⟨4430186249509,4430186440691⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123192851146,123192851631⟩,⟨784656760686,784656770136⟩,⟨187161372126,187161378163⟩,⟨-2444693536897,-2444693305938⟩,⟨-685787193425,-685787069224⟩,⟨-165342377709,-165342330332⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11867030386,11867030491⟩,⟨171073578558,171073580746⟩,⟨21788063746,21788064962⟩,⟨721884601793,721884655751⟩,⟨100232693264,100232720276⟩,⟨-16403511309,-16403505026⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨173499937957,173500090498⟩,⟨1671648244969,1671653645259⟩,⟨113785322308,113788146096⟩,⟨-1841919457714,-1841712069183⟩,⟨417419404830,417560765434⟩,⟨-568614360440,-568500485895⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-173500090498,-173499937957⟩,⟨-1671653645259,-1671648244969⟩,⟨-113788146096,-113785322308⟩,⟨1841712069183,1841919457714⟩,⟨-417560765434,-417419404830⟩,⟨568500485895,568614360440⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56490023092,56490235938⟩,⟨-67751380210,-67744330497⟩,⟨126493856814,126497618022⟩,⟨-2051512622562,-2051251516562⟩,⟨-1702385740487,-1702201761760⟩,⟨436900486484,437053422258⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28377751531074,28377776793729⟩,⟨-250493627629827,-250493004199533⟩,⟨-84647881978130,-84647423475468⟩,⟨3562539524905541,3562561489323712⟩,⟨1328018147691062,1328037015709064⟩,⟨305170848579474,305189491506518⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13802926854,13802926963⟩,⟨175830980004,175830982816⟩,⟨41940335098,41940336618⟩,⟨572103934093,572104014981⟩,⟨113456473640,113456513914⟩,⟨26667076254,26667091130⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨356245462775,356245782729⟩,⟨1393475590836,1393487554533⟩,⟨19812319827,19819086983⟩,⟨-20627872529259,-20627380533224⟩,⟨-3491850632651,-3491512325761⟩,⟨-1938423123117,-1938152845941⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-356245782729,-356245462775⟩,⟨-1393487554533,-1393475590836⟩,⟨-19819086983,-19812319827⟩,⟨20627380533224,20627872529259⟩,⟨3491512325761,3491850632651⟩,⟨1938152845941,1938423123117⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83618618199,83619096722⟩,⟨-504752809360,-504737582215⟩,⟨-89522263983,-89512429257⟩,⟨1514749347297,1515334960379⟩,⟨-2052974220557,-2052527514687⟩,⟨669670137336,670067275743⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238713627925,238713627931⟩,⟨1566685678416,1566685678426⟩,⟨308990527190,308990527196⟩,⟨-3945612726766,-3945612726762⟩,⟨-1556351696246,-1556351696236⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1670046600725,-1670045139928⟩,⟨-4053120898695,-4053079636790⟩,⟨437834761338,437860506531⟩,⟨40186102222997,40187591636623⟩,⟨-7452104838717,-7450959822610⟩,⟨2106653896444,2107704737727⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187117441874,-187117277464⟩,⟨-1645938840027,-1645933158281⟩,⟨-235222715500,-235219572900⟩,⟨2430871224359,2431100681676⟩,⟨-170792528905,-170637711973⟩,⟨636232802633,636359604485⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51596186051,51596350467⟩,⟨-79253161611,-79247479855⟩,⟨73767811690,73770954296⟩,⟨-1514741502407,-1514512045086⟩,⟨-1727144225151,-1726989408209⟩,⟨289524168130,289650969985⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4296105246,4296146020⟩,⟨-31085541656,-31084095990⟩,⟨5020508708,5021372419⟩,⟨-15999091955,-15939612201⟩,⟨-287501301929,-287458562910⟩,⟨47033600080,47068830165⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2421226249,2421241681⟩,⟨-7438163998,-7437607044⟩,⟨6923324210,6923641218⟩,⟨-130739809470,-130716183100⟩,⟨-172732907436,-172716645436⟩,⟨37071063862,37083894601⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4274213969,4274241297⟩,⟨-30424680347,-30423586661⟩,⟨4516630416,4517239389⟩,⟨-37124568711,-37074342782⟩,⟨-272355445097,-272322322925⟩,⟨38729459716,38754239514⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4274241297,-4274213969⟩,⟨30423586661,30424680347⟩,⟨-4517239389,-4516630416⟩,⟨37074342782,37124568711⟩,⟨272322322925,272355445097⟩,⟨-38754239514,-38729459716⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨21863949,21932051⟩,⟨-661954995,-659415643⟩,⟨503269319,504742003⟩,⟨21075250827,21184956510⟩,⟨-15178979004,-15103117813⟩,⟨8279360566,8339370449⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56490023092,56490235938⟩,⟨-67751380210,-67744330497⟩,⟨126493856814,126497618022⟩,⟨-2051512622562,-2051251516562⟩,⟨-1702385740487,-1702201761760⟩,⟨436900486484,437053422258⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨21863949,21932051⟩,⟨-661954995,-659415643⟩,⟨503269319,504742003⟩,⟨21075250827,21184956510⟩,⟨-15178979004,-15103117813⟩,⟨8279360566,8339370449⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112957639884,113387136615⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨117682103910,121547574477⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113387136615,-112957639884⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436368677273,436798174004⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46705084989,48286673142⟩,⟨-121547574477,-117682103910⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159662724873,161673809757⟩,⟨977964053299,981829523866⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46275588258,48716169873⟩,⟨-121547574477,-117682103910⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2121571235264,-2107808428352⟩,⟨6650940246693,6761333798125⟩,⟨2967657132469,3007994957438⟩,⟨-41578127574812,-40231503740037⟩,⟨-26069103353822,-25428904185932⟩,⟨-8229138678844,-8009909703009⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311958960334,-306079925559⟩,⟨-928697802932,-880600309743⟩,⟨-411886701226,-394236459511⟩,⟨5717690033841,6233206272148⟩,⟨3553752882068,3801069963787⟩,⟨1145553172830,1226807763011⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306079925559,311958960334⟩,⟨880600309743,928697802932⟩,⟨394236459511,411886701226⟩,⟨-6233206272148,-5717690033841⟩,⟨-3801069963787,-3553752882068⟩,⟨-1226807763011,-1145553172830⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-161673809757,-159662724873⟩,⟨-981829523866,-977964053299⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937837818019,939848902903⟩,⟨-981829523866,-977964053299⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-174871115840,-172515864448⟩,⟨-1151087061370,-1144101828312⟩,⟨-512097787146,-510499542188⟩,⟨-1205081773927,-1190500364415⟩,⟨750179002154,757853754708⟩,⟨-238509659175,-237023216481⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149477661009,-147148877556⟩,⟨-830490169138,-819716968046⟩,⟨-369267603539,-365964654211⟩,⟨1005160938504,1040322111907⟩,⟨1373131286751,1389862767647⟩,⟨201333913026,204706721443⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147148877556,149477661009⟩,⟨819716968046,830490169138⟩,⟨365964654211,369267603539⟩,⟨-1040322111907,-1005160938504⟩,⟨-1389862767647,-1373131286751⟩,⟨-204706721443,-201333913026⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨453228803115,461436621343⟩,⟨1700317277789,1759187972070⟩,⟨760201113722,781154304765⟩,⟨-7273528384055,-6722850972345⟩,⟨-5190932731434,-4926884168819⟩,⟨-1431514484454,-1346887085856⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨816746669863,826836691949⟩,⟨4073873731698,4146699009366⟩,⟨760201113722,781154304765⟩,⟨-19283928246382,-18527883383580⟩,⟨-5190932731434,-4926884168819⟩,⟨-1431514484454,-1346887085856⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92551176516,97432339746⟩,⟨-243095148954,-235364207820⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12407849619194,13062241509223⟩,⟨29973248143115,34309315828190⟩,⟨-123295315184718,-111141679246228⟩,⟨144810846652914,180233867482437⟩,⟨-367653532667872,-226602958680689⟩,⟨1991073916073796,2327584394418842⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9216882842008,9822852515686⟩,⟨68238080745103,75063676494037⟩,⟨-84139746323432,-73278870534094⟩,⟨100587299394503,185240056357081⟩,⟨-782417839624275,-611349194120274⟩,⟨1286824835967004,1581465905301435⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨84939876864,90471687424⟩,⟨-730060613240,-584657937294⟩,⟨627846985523,818333415945⟩,⟨6199334954464,10878640986215⟩,⟨-7922035929158,-982288883788⟩,⟨-6154463959816,3725818910918⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1184451504640,1189983315200⟩,⟨-730060613240,-584657937294⟩,⟨627846985523,818333415945⟩,⟨6199334954464,10878640986215⟩,⟨-7922035929158,-982288883788⟩,⟨-6154463959816,3725818910918⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨81818723648,86941880576⟩,⟨-677706204176,-540207742507⟩,⟨580113226991,759648751093⟩,⟨5310295903167,9833094627969⟩,⟨-7068908651102,-439382870848⟩,⟨-6237951165590,3152557956682⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨88139413794,94095764578⟩,⟨-791198470531,-625446627628⟩,⟨671648761974,886863549872⟩,⟨6756347952357,12402380219605⟩,⟨-9285776576960,-1163364623236⟩,⟨-6575368203843,4837341281251⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-90471687424,-84939876864⟩,⟨584657937294,730060613240⟩,⟨-818333415945,-627846985523⟩,⟨-10878640986215,-6199334954464⟩,⟨982288883788,7922035929158⟩,⟨-3725818910918,6154463959816⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1009039940352,1014571750912⟩,⟨584657937294,730060613240⟩,⟨-818333415945,-627846985523⟩,⟨-10878640986215,-6199334954464⟩,⟨982288883788,7922035929158⟩,⟨-3725818910918,6154463959816⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-94411525056,-88400188736⟩,⟨633605459395,795518691717⟩,⟨-891706135949,-680410291756⟩,⟨-12429606223805,-7083464842575⟩,⟨1456619825973,9277502082769⟩,⟨-4783055606414,6285222314213⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-87118011182,-81126310005⟩,⟨518782216272,687056781259⟩,⟨-772341139630,-554156080765⟩,⟨-10297135347832,-4510071565486⟩,⟨-527636955838,7758210316846⟩,⟨-4164956706939,7446938170839⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1021402612,12969454573⟩,⟨-272416254259,61610153631⟩,⟨-100692377656,332707469107⟩,⟨-3540787395475,7892308654119⟩,⟨-9813413532798,6594845693610⟩,⟨-10740324910782,12284279452090⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨510701306,6484727287⟩,⟨-136208127130,30805076816⟩,⟨-50346188828,166353734554⟩,⟨-1770393697738,3946154327060⟩,⟨-4906706766399,3297422846805⟩,⟨-5370162455391,6142139726045⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6484727287,-510701306⟩,⟨-30805076816,136208127130⟩,⟨-166353734554,50346188828⟩,⟨-3946154327060,1770393697738⟩,⟨-3297422846805,4906706766399⟩,⟨-6142139726045,5370162455391⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755638656329,761612701574⟩,⟨-30805076816,136208127130⟩,⟨-166353734554,50346188828⟩,⟨-3946154327060,1770393697738⟩,⟨-3297422846805,4906706766399⟩,⟨-6142139726045,5370162455391⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6561806623,7444328936⟩,⟨-120143914686,-90332420224⟩,⟨97005332716,134670708606⟩,⟨1579602487820,2759766186333⟩,⟨-2390430297648,-819475135950⟩,⟨-295791146354,1831268861789⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7444328936,-6561806623⟩,⟨90332420224,120143914686⟩,⟨-134670708606,-97005332716⟩,⟨-2759766186333,-1579602487820⟩,⟨819475135950,2390430297648⟩,⟨-1831268861789,295791146354⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092067298840,1092949821153⟩,⟨90332420224,120143914686⟩,⟨-134670708606,-97005332716⟩,⟨-2759766186333,-1579602487820⟩,⟨819475135950,2390430297648⟩,⟨-1831268861789,295791146354⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7469644480,-6581465024⟩,⟨90874754246,120962903426⟩,⟨-135588722592,-97587729292⟩,⟨-2791886518173,-1596596847665⟩,⟨832460702962,2421642027358⟩,⟨-1860472553873,289146025084⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3734822240,-3290732512⟩,⟨45437377123,60481451713⟩,⟨-67794361296,-48793864646⟩,⟨-1395943259087,-798298423832⟩,⟨416230351481,1210821013679⟩,⟨-930236276937,144573012542⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3290732512,3734822240⟩,⟨-60481451713,-45437377123⟩,⟨48793864646,67794361296⟩,⟨798298423832,1395943259087⟩,⟨-1210821013679,-416230351481⟩,⟨-144573012542,930236276937⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765414116128,765858225120⟩,⟨-60481451713,-45437377123⟩,⟨48793864646,67794361296⟩,⟨798298423832,1395943259087⟩,⟨-1210821013679,-416230351481⟩,⟨-144573012542,930236276937⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273016824710,273237455289⟩,⟨22583105056,30035978672⟩,⟨-33667677152,-24251333179⟩,⟨-689941546584,-394900621955⟩,⟨204868783987,597607574412⟩,⟨-457817215448,73947786589⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530828232256,1531716450240⟩,⟨-120962903426,-90874754246⟩,⟨97587729292,135588722592⟩,⟨1596596847664,2791886518174⟩,⟨-2421642027358,-832460702962⟩,⟨-289146025084,1860472553874⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1191562665260,1198095111273⟩,⟨-866845817175,-686650864663⟩,⟨737374194355,971657538843⟩,⟨8072182011927,14171239401728⟩,⟨-10812347340375,-2003487786412⟩,⟨-6394955267619,5999926114255⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1283613702744,1296678594770⟩,⟨-1733691634350,-1373301729326⟩,⟨1474748388710,1943315077685⟩,⟨16144364023861,28342478803446⟩,⟨-21624694680743,-4006975572824⟩,⟨-12785319015550,11999852228508⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨170218912384,181353405568⟩,⟨-1485037209303,-1164483801867⟩,⟨1250504950085,1664595446263⟩,⟨11683785521540,23044168344600⟩,⟨-17198776959663,-1149435016856⟩,⟨-13471685690508,8856541655574⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨58374875536,62668174246⟩,⟨-508235119236,-390598105737⟩,⟨417799264546,570988075530⟩,⟨3754904825361,7722029115710⟩,⟨-5815137399899,-59504091042⟩,⟨-5016111852722,3097628544100⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380115910181,380643819052⟩,⟨1381757896,19277891426⟩,⟨-22670285902,-69765494⟩,⟨-571311368996,140260889034⟩,⟨-312553965030,633221729602⟩,⟨-717938381860,561053241072⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176002759286,3180413624463⟩,⟨-161297296167,-11529063840⟩,⟨582106920,189681316204⟩,⟨-1173473180032,4796498532313⟩,⟨-5317378919523,2615121481914⟩,⟨-4694308349252,6029585211098⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨168619195187,181272039474⟩,⟨-1479298684636,-1128877255959⟩,⟨1206868180310,1662433748241⟩,⟨10787566794056,22759002890779⟩,⟨-17295200616454,-27416238377⟩,⟨-14776567517527,9500776887971⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨338838107571,362625445042⟩,⟨-2964335893939,-2293361057826⟩,⟨2457373130395,3327029194504⟩,⟨22471352315596,45803171235379⟩,⟨-34493977576117,-1176851255233⟩,⟨-28248253208035,18357318543545⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519312178711,527555955341⟩,⟨-42676288606,188698031126⟩,⟨-230460713630,69747869726⟩,⟨-5474498101976,2486389313855⟩,⟨-4609351623390,6810055776946⟩,⟨-8524342605108,7489975360918⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356896959543,365428892455⟩,⟨-44341691308,196061797308⟩,⟨-239454229880,72469715848⟩,⟨-5696065472722,2618482387203⟩,⟨-4832051715190,7088772515355⟩,⟨-8872826246119,7834567035937⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713793919086,730857784910⟩,⟨-88683382616,392123594616⟩,⟨-478908459760,144939431696⟩,⟨-11392130945444,5236964774406⟩,⟨-9664103430380,14177545030710⟩,⟨-17745652492238,15669134071874⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523383903320,1525154643617⟩,⟨-30630483202,29269160440⟩,⟨-37082979314,38583389876⟩,⟨-1163169338669,1212284030354⟩,⟨-1602166891408,1557969594686⟩,⟨-2120414886873,2156263700228⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988968319346,1013787500123⟩,⟨-143374927495,563378048325⟩,⟨-688953009913,226695208907⟩,⟨-16597272996323,8090994580978⟩,⟨-14496223892132,20728658910839⟩,⟨-26058425513382,23200567200385⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67792085769,67901698433⟩,⟨11215102192,14928363052⟩,⟨-16733375434,-12043568820⟩,⟨-341984333961,-194472438792⟩,⟨99901414164,296024340950⟩,⟨-226472700481,38815082949⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50357776030,51062321027⟩,⟨259511848342,267310700974⟩,⟨34287814117,39294863478⟩,⟨-1364968607363,-1174222888642⟩,⟨-301717172754,-115180765467⟩,⟨-282489872750,-70509139660⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131341786182,2133815800277⟩,⟨-337023937476,-253046235954⟩,⟨271738919984,377774043704⟩,⟨4460841866409,7805302686568⟩,⟨-6776954497500,-2334168324984⟩,⟨-788288813482,5217044813770⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2967424897064,2972593177280⟩,⟨-704256002551,-528466883313⟩,⟨567505063165,789408728290⟩,⟨9347483933062,16365826811291⟩,⟨-14223682225995,-4908413272863⟩,⟨-1611063027431,10971582827877⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135908447511,138049933504⟩,⟨667679136099,698486063794⟩,⟨118529720697,142896792552⟩,⟨-3604589618152,-2658478449392⟩,⟨-1367494399162,-360223221935⟩,⟨-803152097121,375660715188⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8757163360600,8895148474982⟩,⟨-45715607520649,-42354060729142⟩,⟨-9352532602846,-7518903492986⟩,⟨578331140054299,705819182719868⟩,⟨95581093326645,185634473425534⟩,⟨-11675363298816,72232824037369⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7876730825019,8201632531996⟩,⟨-43311277052110,-33538065389967⟩,⟨-14197048551724,-4928979077692⟩,⟨339064743945439,728168931094693⟩,⟨-45521948214159,368723005099196⟩,⟨-225436679103906,266016409143934⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15753461650038,16403265063992⟩,⟨-86622554104220,-67076130779934⟩,⟨-28394097103448,-9857958155384⟩,⟨678129487890878,1456337862189386⟩,⟨-91043896428318,737446010198392⟩,⟨-450873358207812,532032818287868⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10661930935953,10702470597440⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710694,2028067813858452⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9562419308177,9602958969664⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710699,2028067813858436⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2378215779456,2382867339072⟩,⟨-11978441145317,-11837681660582⟩,⟨0,0⟩,⟨99082204851667,105744330752101⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7477561278673,7571747385473⟩,⟨-46561682673436,-45231730160086⟩,⟨-20714449378369,-20182449645407⟩,⟨547213011576402,572652568293857⟩,⟨295020487031540,306905323534396⟩,⟨108947625705507,113339336669433⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6378049650897,6472235757697⟩,⟨-46561682673437,-45231730160086⟩,⟨-20714449378370,-20182449645407⟩,⟨547213011576411,572652568293858⟩,⟨295020487031543,306905323534397⟩,⟨108947625705507,113339336669434⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1932937312576,1949055370496⟩,⟨-8026765909712,-7684023746517⟩,⟨-3570962786610,-3428620169720⟩,⟨34363433418520,45019138573402⟩,⟨24049351456897,28946209283290⟩,⟨6910488972409,8847054998694⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101308883270,101738380002⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136185682562,138196767447⟩,⟨689793118173,697243190431⟩,⟨307976936945,310003517886⟩,⟨-1753486165281,-1739706366688⟩,⟨-1560280416916,-1552422975566⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4311153092032,4331922709568⟩,⟨-20005207055029,-19521705407099⟩,⟨-3570962786610,-3428620169720⟩,⟨133445638270187,150763469325503⟩,⟨24049351456897,28946209283290⟩,⟨6910488972409,8847054998694⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨677676215142,725250890084⟩,⟨-5928671787878,-4586722115652⟩,⟨4914746260790,6654058389008⟩,⟨44942704631192,91606342470758⟩,⟨-68987955152234,-2353702510466⟩,⟨-56496506416070,36714637087090⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4988829307174,5057173599652⟩,⟨-25933878842907,-24108427522751⟩,⟨1343783474180,3225438219288⟩,⟨178388342901379,242369811796261⟩,⟨-44938603695337,26592506772824⟩,⟨-49586017443661,45561692085784⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459670196445,467942890662⟩,⟨1560208030403,1796734539470⟩,⟨123816064957,298451467850⟩,⟨-34888218796337,-25823183175682⟩,⟨-3091564126570,5023329875581⟩,⟨-4588219858733,4215846950463⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33173170457,35168800896⟩,⟨-720584107765,-680007533373⟩,⟨312815742780,315329962371⟩,⟨8332435067553,9003354852408⟩,⟨-6467888110707,-6405006849897⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨492843366902,503111691558⟩,⟨839623922638,1116727006097⟩,⟨436631807737,613781430221⟩,⟨-26555783728784,-16819828323274⟩,⟨-9559452237277,-1381676974316⟩,⟨-4588219858733,4215846950463⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507340798957,508333108400⟩,⟨2520383226112,2560338836291⟩,⟨0,0⟩,⟨2439291441574,4695713285828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227409643707,232601751161⟩,⟨1517155057421,1687845463614⟩,⟨201472294236,283767278509⟩,⟨-7334754063971,-411562577076⟩,⟨-3418705624581,791721806982⟩,⟨-2121254567840,1949096790548⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-725250890084,-677676215142⟩,⟨4586722115652,5928671787878⟩,⟨-6654058389008,-4914746260790⟩,⟨-91606342470758,-44942704631192⟩,⟨2353702510466,68987955152234⟩,⟨-36714637087090,56496506416070⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3585902201948,3654246494426⟩,⟨-15418484939377,-13593033619221⟩,⟨-10225021175618,-8343366430510⟩,⟨41839295799429,105820764694311⟩,⟨26403053967363,97934164435524⟩,⟨-29804148114681,65343561414764⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨444150408814,459299420058⟩,⟨311725565363,633664897463⟩,⟨-280751644102,-3108456174⟩,⟨-20200445649273,-9428814676349⟩,⟨-12746606695113,-1795515002251⟩,⟨-10665305588049,2409342062078⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨319325449746,323347619514⟩,⟨1955928106598,1963659047732⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-323347619514,-319325449746⟩,⟨-1963659047732,-1955928106598⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨776164008262,780186178030⟩,⟨-1963659047732,-1955928106598⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1364493411754,1383001345199⟩,⟨-9176485063877,-8862797666220⟩,⟨-4082452016614,-3954590438678⟩,⟨51596049393011,60615068529889⟩,⟨33041109635061,37192655550232⟩,⟨10321166531143,11952133831767⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1383001345199,-1364493411754⟩,⟨8862797666220,9176485063877⟩,⟨3954590438678,4082452016614⟩,⟨-60615068529889,-51596049393011⟩,⟨-37192655550232,-33041109635061⟩,⟨-11952133831767,-10321166531143⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-283489717423,-264981783978⟩,⟨8862797666220,9176485063877⟩,⟨3954590438678,4082452016614⟩,⟨-60615068529889,-51596049393011⟩,⟨-37192655550232,-33041109635061⟩,⟨-11952133831767,-10321166531143⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12560606803,-11152394955⟩,⟨401373462820,437922328958⟩,⟨53817719116,75716957658⟩,⟨-4714541299876,-4068736315483⟩,⟨1683203646123,2115112558707⟩,⟨2609391791039,2809244615397⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨431589802011,448147025103⟩,⟨713099028183,1071587226421⟩,⟨-226933924986,72608501484⟩,⟨-24914986949149,-13497550991832⟩,⟨-11063403048990,319597556456⟩,⟨-8055913797010,5218586677475⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101738380002,-101308883270⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4263827731,4507732413⟩,⟨25484388202,27863302933⟩,⟨40206963047,40417161119⟩,⟨-290579032314,-279371516472⟩,⟨244629257582,245740915920⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9222551298,9769181216⟩,⟨6013366822,14479809746⟩,⟨86966641867,87592282552⟩,⟨-852614631568,-719492846911⟩,⟨88809042402,99690417602⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1462109545193,1480172327875⟩,⟨-7514972943476,-7203900996439⟩,⟨-1415669054284,-1344276705982⟩,⟨103751275255349,111256283051095⟩,⟨21958957154838,23782382752997⟩,⟨4853603863591,5302256181006⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12263972424,13151358601⟩,⟨-58774213804,-40932475517⟩,⟨103068332148,106641902576⟩,⟨-475480085378,-47051768982⟩,⟨-315036317807,-231638571308⟩,⟨-184846391671,-165542369569⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13151358601,-12263972424⟩,⟨40932475517,58774213804⟩,⟨-106641902576,-103068332148⟩,⟨47051768982,475480085378⟩,⟨231638571308,315036317807⟩,⟨165542369569,184846391671⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114889738603,-113572855694⟩,⟨-832663872491,-813963140742⟩,⟨-106641902576,-103068332148⟩,⟨2246075024534,2674503340930⟩,⟨231638571308,315036317807⟩,⟨165542369569,184846391671⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨81352310376,86356988069⟩,⟨-571104687328,-530285295760⟩,⟨608915496393,629990983361⟩,⟨3091128981373,3769335177567⟩,⟨-3758669312982,-3305252917431⟩,⟨-2546396996792,-2329479923420⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨108180747269,116254545045⟩,⟨-1359061373771,-1238176248431⟩,⟨698535808497,748637107396⟩,⟨18735791560730,21619321777226⟩,⟨-7092768494380,-5781601989660⟩,⟨-4691148171085,-4170187633489⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-116254545045,-108180747269⟩,⟨1238176248431,1359061373771⟩,⟨-748637107396,-698535808497⟩,⟨-21619321777226,-18735791560730⟩,⟨5781601989660,7092768494380⟩,⟨4170187633489,4691148171085⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨983257082731,991330880507⟩,⟨1238176248431,1359061373771⟩,⟨-748637107396,-698535808497⟩,⟨-21619321777226,-18735791560730⟩,⟨5781601989660,7092768494380⟩,⟨4170187633489,4691148171085⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121786376390,124599612861⟩,⟨770220000582,799460935483⟩,⟨181318024565,192981573921⟩,⟨-2744704450097,-2152712652309⟩,⟨-818577194081,-551849183967⟩,⟨-218534849009,-111442893574⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11731384393,12005013593⟩,⟨168154871650,174012774832⟩,⟨21292662156,22286367878⟩,⟨646219641118,797146585526⟩,⟨86764672490,113666838910⟩,⟨-19306521662,-13512588820⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨168083637742,179098988213⟩,⟨1463482824259,1880363739762⟩,⟨-4946182332,227302464888⟩,⟨-10924184590196,7276690889437⟩,⟨-6000461332090,6940957595712⟩,⟨-6361945791937,5233584325288⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-179098988213,-168083637742⟩,⟨-1880363739762,-1463482824259⟩,⟨-227302464888,4946182332⟩,⟨-7276690889437,10924184590196⟩,⟨-6940957595712,6000461332090⟩,⟨-5233584325288,6361945791937⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48310655494,64518113419⟩,⟨-363208682341,224362639355⟩,⟨-25830170652,288713460841⟩,⟨-14611444953408,10512622013120⟩,⟨-10359663220293,6792183139072⟩,⟨-7354838893128,8311042582485⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27694526420958,29077338573773⟩,⟨-273300723262339,-228013895481580⟩,⟨-103607013963735,-66454460011832⟩,⟨2622031373811847,4517953059913326⟩,⟨461239596967985,2227692801128712⟩,⟨-638751433954019,1259532417111581⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13489553997,14119963021⟩,⟨170625394992,181194123906⟩,⟨40167042580,43738381284⟩,⟨457020609966,685698458310⟩,⟨68503809428,158385805098⟩,⟨10271593871,43054863802⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339775223962,373412099553⟩,⟨787980210238,1994373754522⟩,⟨-318796068225,341383106018⟩,⟨-46396932768680,5385749689564⟩,⟨-20561507295429,14154389025010⟩,⟨-16187082892504,12458179986001⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-373412099553,-339775223962⟩,⟨-1994373754522,-787980210238⟩,⟨-341383106018,318796068225⟩,⟨-5385749689564,46396932768680⟩,⟨-14154389025010,20561507295429⟩,⟨-12458179986001,16187082892504⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58177702458,108371801141⟩,⟨-1281274726339,283607016183⟩,⟨-568317031004,391404569709⟩,⟨-30300736638713,32899381776848⟩,⟨-25217792074000,20881104851885⟩,⟨-20514093783011,21405669569979⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237494565832,239935147449⟩,⟨1562530472719,1570839538439⟩,⟨307976936945,310003517886⟩,⟨-3952509420833,-3938729622240⟩,⟨-1560280416916,-1552422975566⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1714003551968,-1627236658042⟩,⟨-5493692231630,-2610881460045⟩,⟨-572689655987,1490213777522⟩,⟨-20681748888432,101052526075995⟩,⟨-60152552112286,44117738537836⟩,⟨-51372953239416,55378048000724⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-194235489305,-180239345456⟩,⟨-1868821353416,-1429089035724⟩,⟨-365733296887,-99468958592⟩,⟨-7146763550036,12072298491069⟩,⟨-7380567572497,6928589930133⟩,⟨-5857821839361,7139370109007⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43259076527,59695801993⟩,⟨-306290880697,141750502715⟩,⟨-57756359942,210534559294⟩,⟨-11099272970869,8133568868829⟩,⟨-8940847989413,5376166954567⟩,⟨-6204871638551,6793002471423⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2556228483,6359136167⟩,⟨-110982916532,38755727449⟩,⟨-35894122250,51423814682⟩,⟨-3741074877955,3813163891493⟩,⟨-2966573929518,2156948043880⟩,⟨-2227124533496,2280779523945⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1701980820,3241065111⟩,⟨-33258911148,15392124520⟩,⟨-6271533908,22861112238⟩,⟨-1284200857940,1053838823807⟩,⟨-1088148395520,638061424290⟩,⟨-695880768971,818251521432⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨2992075890,5745292002⟩,⟨-82617343955,15390507472⟩,⟨-21643508940,35217570090⟩,⟨-2447987421991,2486397685908⟩,⟨-2108568368851,1370190205608⟩,⟨-1371355203834,1517293851027⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5745292002,-2992075890⟩,⟨-15390507472,82617343955⟩,⟨-35217570090,21643508940⟩,⟨-2486397685908,2447987421991⟩,⟨-1370190205608,2108568368851⟩,⟨-1517293851027,1371355203834⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3189063519,3367060277⟩,⟨-126373424004,121373071404⟩,⟨-71111692340,73067323622⟩,⟨-6227472563863,6261151313484⟩,⟨-4336764135126,4265516412731⟩,⟨-3744418384523,3652134727779⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48310655494,64518113419⟩,⟨-363208682341,224362639355⟩,⟨-25830170652,288713460841⟩,⟨-14611444953408,10512622013120⟩,⟨-10359663220293,6792183139072⟩,⟨-7354838893128,8311042582485⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3189063519,3367060277⟩,⟨-126373424004,121373071404⟩,⟨-71111692340,73067323622⟩,⟨-6227472563863,6261151313484⟩,⟨-4336764135126,4265516412731⟩,⟨-3744418384523,3652134727779⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (527/5120) u, BivariateJet2.affineZ (557/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000046

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000047Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2104217097472,-2104217058624⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2104217097408,-2104217058624⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-175491419008,-175491418944⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-175491419008,-175491418944⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨86694135744,86694135808⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-94119425856,-94119425792⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨86694259008,86694259072⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-94119571136,-94119571072⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7425312064,-7425312000⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7425290048,-7425289984⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨180813561600,180813561664⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨180813830144,180813830208⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1928725639680,1928725678272⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1928725639680,1928725678272⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2497885341504,-2497885283648⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-119669504256,-119669504192⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2111057082880,-2111057044032⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2097414313984,-2097414275200⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-176672935168,-176672935104⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-174312055808,-174312055744⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨84144379776,84144379840⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-91121490752,-91121490688⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨89265855040,89265855104⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-97158567360,-97158567296⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7892712256,-7892712192⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6977110912,-6977110848⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨175265870464,175265870528⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨186424422336,186424422400⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2378215779456,2378215837312⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1920741340096,1920741378688⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1936744988288,1936745026880⟩



end LaneCBRB2Cell000047Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000047
open Set LaneCBRB2Cell000047Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨113172388249,113172388250⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨123480309760,123480309760⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113172388250,-113172388249⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436583425638,436583425639⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49030365183,49030365185⟩,⟨-123480309760,-123480309760⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨162202753432,162202753435⟩,⟨976031318016,976031318016⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49030365182,49030365186⟩,⟨-123480309760,-123480309760⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2104217097472,-2104217058624⟩,⟨6616150222517,6616150222642⟩,⟨2959435292049,2959435292112⟩,⟨-39811715185859,-39811715184372⟩,⟨-25261145459381,-25261145458535⟩,⟨-7965588564000,-7965588563665⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310419461162,-310419455424⟩,⟨-891872335912,-891872301388⟩,⟨-398938714834,-398938699386⟩,⟨5873125539104,5873125539656⟩,⟨3631782267121,3631782306277⟩,⟨1175103896186,1175103896315⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨310419455424,310419461162⟩,⟨891872301388,891872335912⟩,⟨398938699386,398938714834⟩,⟨-5873125539656,-5873125539104⟩,⟨-3631782306277,-3631782267121⟩,⟨-1175103896315,-1175103896186⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162202753435,-162202753432⟩,⟨-976031318016,-976031318016⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨937308874341,937308874344⟩,⟨-976031318016,-976031318016⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175491419008,-175491418944⟩,⟨-1144935050346,-1144935050340⟩,⟨-512134864105,-512134864101⟩,⟨-1192235021800,-1192235021788⟩,⟨756491453998,756491454010⟩,⟨-238544197630,-238544197625⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149602478275,-149602478219⟩,⟨-820248408041,-820248407974⟩,⟨-366900993081,-366900993049⟩,⟨1016353477293,1016353477319⟩,⟨1378639926989,1378639927075⟩,⟨203353550526,203353550537⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149602478219,149602478275⟩,⟨820248407974,820248408041⟩,⟨366900993049,366900993081⟩,⟨-1016353477319,-1016353477293⟩,⟨-1378639927075,-1378639926989⟩,⟨-203353550537,-203353550526⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨460021933643,460021939437⟩,⟨1712120709362,1712120743953⟩,⟨765839692435,765839707915⟩,⟨-6889479016975,-6889479016397⟩,⟨-5010422233352,-5010422194110⟩,⟨-1378457446852,-1378457446712⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨824480217914,824480229725⟩,⟨4092660286246,4092660378781⟩,⟨765839692435,765839707915⟩,⟨-18797310716887,-18797310715819⟩,⟨-5010422233352,-5010422194110⟩,⟨-1378457446852,-1378457446712⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98060730364,98060730372⟩,⟨-246960619520,-246960619520⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12328337908849,12328337909856⟩,⟨31048248937888,31048248942962⟩,⟨-109775808871525,-109775808853338⟩,⟨156386654752085,156386654790409⟩,⟨-276464408047561,-276464407865631⟩,⟨1954963969758663,1954963970246689⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9244532271264,9244532404451⟩,⟨69171042928359,69171044306991⟩,⟨-73729510044628,-73729508677500⟩,⟨137641087026755,137641094028419⟩,⟨-650476739903342,-650476726605430⟩,⟨1297570346466170,1297570370951659⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨90203587584,90203720960⟩,⟨-668401810872,-668399794346⟩,⟨712448249311,712450397738⟩,⟨8527341436329,8527391009374⟩,⟨-4221477329907,-4221409859038⟩,⟨-1339050073070,-1338960573184⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1189715215360,1189715348736⟩,⟨-668401810872,-668399794346⟩,⟨712448249311,712450397738⟩,⟨8527341436329,8527391009374⟩,⟨-4221477329907,-4221409859038⟩,⟨-1339050073070,-1338960573184⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨86694135744,86694259072⟩,⟨-617723933924,-617722001037⟩,⟨658430720540,658432779891⟩,⟨7533754381193,7533803250997⟩,⟨-3531490937936,-3531425830831⟩,⟨-1631820620910,-1631735301685⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨93806495330,93806639294⟩,⟨-721104011270,-721101610904⟩,⟨768623187216,768625744700⟩,⟨9575217726722,9575281000755⟩,⟨-4954601669783,-4954520080539⟩,⟨-1017992294459,-1017887328731⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-90203720960,-90203587584⟩,⟨668399794346,668401810872⟩,⟨-712450397738,-712448249311⟩,⟨-8527391009374,-8527341436329⟩,⟨4221409859038,4221477329907⟩,⟨1338960573184,1339050073070⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1009307906816,1009308040192⟩,⟨668399794346,668401810872⟩,⟨-712450397738,-712448249311⟩,⟨-8527391009374,-8527341436329⟩,⟨4221409859038,4221477329907⟩,⟨1338960573184,1339050073070⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-94119571136,-94119425792⟩,⟨728135828330,728138121299⟩,⟨-776123412129,-776120969131⟩,⟨-9771700332117,-9771642064091⟩,⟨5112659481827,5112736826796⟩,⟨910775676014,910876816347⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-86398031169,-86397886331⟩,⟨611183674648,611186128804⟩,⟨-651464124451,-651461509640⟩,⟨-7354806763224,-7354741260740⟩,⟨3388231030620,3388314801122⟩,⟨1727234415693,1727341406321⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7408464161,7408752963⟩,⟨-109920336622,-109915482100⟩,⟨117159062765,117164235060⟩,⟨2220410963498,2220539740015⟩,⟨-1566370639163,-1566205279417⟩,⟨709242121234,709454077590⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3704232080,3704376482⟩,⟨-54960168311,-54957741050⟩,⟨58579531382,58582117530⟩,⟨1110205481749,1110269870008⟩,⟨-783185319582,-783102639708⟩,⟨354621060617,354727038795⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3704376482,-3704232080⟩,⟨54957741050,54960168311⟩,⟨-58582117530,-58579531382⟩,⟨-1110269870008,-1110205481749⟩,⟨783102639708,783185319582⟩,⟨-354727038795,-354621060617⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758419007134,758419170800⟩,⟨54957741050,54960168311⟩,⟨-58582117530,-58579531382⟩,⟨-1110269870008,-1110205481749⟩,⟨783102639708,783185319582⟩,⟨-354727038795,-354621060617⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7400273910,7400295795⟩,⟨-109671110182,-109670617148⟩,⟨116898059888,116898585250⟩,⟨2211809396962,2211824503146⟩,⟨-1558866823164,-1558849503032⟩,⟨703576386155,703596964563⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7400295795,-7400273910⟩,⟨109670617148,109671110182⟩,⟨-116898585250,-116898059888⟩,⟨-2211824503146,-2211809396962⟩,⟨1558849503032,1558866823164⟩,⟨-703596964563,-703576386155⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092111331981,1092111353866⟩,⟨109670617148,109671110182⟩,⟨-116898585250,-116898059888⟩,⟨-2211824503146,-2211809396962⟩,⟨1558849503032,1558866823164⟩,⟨-703596964563,-703576386155⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7425312064,-7425289984⟩,⟨110413758040,110414256629⟩,⟨-117690706057,-117690174775⟩,⟨-2237900058671,-2237884705362⟩,⟨1581230982099,1581248557767⟩,⟨-720962138002,-720941292219⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3712656032,-3712644992⟩,⟨55206879020,55207128315⟩,⟨-58845353029,-58845087387⟩,⟨-1118950029336,-1118942352681⟩,⟨790615491049,790624278884⟩,⟨-360481069001,-360470646109⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3712644992,3712656032⟩,⟨-55207128315,-55206879020⟩,⟨58845087387,58845353029⟩,⟨1118942352681,1118950029336⟩,⟨-790624278884,-790615491049⟩,⟨360470646109,360481069001⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765836028608,765836058912⟩,⟨-55207128315,-55206879020⟩,⟨58845087387,58845353029⟩,⟨1118942352681,1118950029336⟩,⟨-790624278884,-790615491049⟩,⟨360470646109,360481069001⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273027832995,273027838467⟩,⟨27417654287,27417777546⟩,⟨-29224646313,-29224514972⟩,⟨-552956125787,-552952349240⟩,⟨389712375758,389716705791⟩,⟨-175899241141,-175894096538⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531672057216,1531672117824⟩,⟨-110414256630,-110413758040⟩,⟨117690174774,117690706058⟩,⟨2237884705362,2237900058672⟩,⟨-1581248557768,-1581230982098⟩,⟨720941292218,720962138002⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1197776864419,1197777022701⟩,⟨-793213176662,-793210573946⟩,⟨845484228935,845487001997⟩,⟨11170242787604,11170311047662⟩,⟨-6129585027768,-6129496434696⟩,⟨-395475007009,-395360702705⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1296042101062,1296042417626⟩,⟨-1586426353324,-1586421147892⟩,⟨1690968457870,1690974003994⟩,⟨22340485575213,22340622095319⟩,⟨-12259170055534,-12258992869394⟩,⟨-790949869225,-790721550202⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨180813561600,180813830208⟩,⟨-1345862314706,-1345857569886⟩,⟨1434551413089,1434556468603⟩,⟨17305383982459,17305516045961⟩,⟨-8644239157195,-8644073920220⟩,⟨-2542707733936,-2542500681062⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62220456434,62220561862⟩,⟨-456540293958,-456538597708⟩,⟨486625111892,486626919155⟩,⟨5724065340508,5724109374003⟩,⟨-2776415908945,-2776358502845⟩,⟨-1028668203410,-1028593951161⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380340773190,380340795864⟩,⟨10776319978,10776617555⟩,⟨-11486811244,-11486494154⟩,⟨-220095258287,-220086093641⟩,⟨156105904845,156116383370⟩,⟨-72270143383,-72257730689⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178533128081,3178533317570⟩,⟨-90060914748,-90058417138⟩,⟨95993389589,95996050977⟩,⟨1844377316173,1844454407795⟩,⟨-1310114998289,-1310026971655⟩,⟨609660726098,609764852974⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨179870568917,179870884419⟩,⟨-1324890195863,-1324885063587⟩,⟨1412196790278,1412202258498⟩,⟨16726625833595,16726761006115⟩,⟨-8180085107710,-8179911062712⟩,⟨-2854264676642,-2854041224305⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨360684130517,360684714627⟩,⟨-2670752510569,-2670742633473⟩,⟨2846748203367,2846758727101⟩,⟨34032009816054,34032277052076⟩,⟨-16824324264905,-16823984982932⟩,⟨-5396972410578,-5396541905367⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523140798015,523141023803⟩,⟨75817288964,75820653870⟩,⟨-80817337224,-80813752044⟩,⟨-1526185953252,-1526096310192⟩,⟨1074477483510,1074592295380⟩,⟨-483123995086,-482977135484⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360851049319,360851282935⟩,⟨78445654734,78449153223⟩,⟨-83619058228,-83615330715⟩,⟨-1573410288782,-1573316693113⟩,⟨1105666903806,1105786473098⟩,⟨-493414247600,-493261616347⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721702098638,721702565870⟩,⟨156891309468,156898306446⟩,⟨-167238116456,-167230661430⟩,⟨-3146820577564,-3146633386226⟩,⟨2211333807612,2211572946196⟩,⟨-986828495200,-986523232694⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524271761421,1524271843914⟩,⟨-743639482,-742647858⟩,⟨791589524,792646170⟩,⟨26060202216,26090661710⟩,⟨-22399054736,-22364158934⟩,⟨17344327655,17385751847⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000507954006,1000508655886⟩,⟨217012990207,217023353213⟩,⟨-231325484786,-231314443305⟩,⟨-4345598111424,-4345318072097⟩,⟨3051133362305,3051488276398⟩,⟨-1356913866079,-1356463071662⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67797552755,67797555474⟩,⟨13616559472,13616620962⟩,⟨-14513974772,-14513909250⟩,⟨-273249839711,-273247946345⟩,⟨192087192030,192089359462⟩,⟨-85804126360,-85801555655⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50838699343,50838702111⟩,⟨262570152321,262570214406⟩,⟨36339380762,36339432901⟩,⟨-1262601383438,-1262599454136⟩,⟨-209452043365,-209450113084⟩,⟨-169557649711,-169555626015⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133692115290,2133692284151⟩,⟨-307624647196,-307623245902⟩,⟨327896035942,327897529126⟩,⟨6257135589181,6257178811962⟩,⟨-4429146536686,-4429097181426⟩,⟨2033805884677,2033864269974⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2972334724919,2972335077767⟩,⟨-642803699792,-642800746251⟩,⟨685162189152,685165336380⟩,⟨13121069394582,13121160649366⟩,⟨-9304410220368,-9304306274850⟩,⟨4302428967737,4302551613558⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137433409169,137433432968⟩,⟨680090193473,680090583756⟩,⟨129917278042,129917577899⟩,⟨-3113544598611,-3113533242228⟩,⟨-854053520619,-854042487256⟩,⟨-214145545993,-214134066185⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8796446348656,8796447871915⟩,⟨-43529309244114,-43529269188270⟩,⟨-8315395860033,-8315373787730⟩,⟨630091852163483,630093366313365⟩,⟨136960467684728,136961472737888⟩,⟨29426902858235,29427723110404⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8004385143810,8004392145177⟩,⟨-37873639992685,-37873492548356⟩,⟨-9417333879763,-9417219830863⟩,⟨521406336041851,521411198849529⟩,⟨156554489698447,156558863623267⟩,⟨19420222451068,19424772306765⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16008770287620,16008784290354⟩,⟨-75747279985370,-75746985096712⟩,⟨-18834667759526,-18834439661726⟩,⟨1042812672083702,1042822397699058⟩,⟨313108979396894,313117727246534⟩,⟨38840444902136,38849544613530⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10682162303971,10682162304067⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848532,2016544728902914⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9582650676195,9582650676291⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848550,2016544728902902⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2380539576896,2380539634752⟩,⟨-11907831699843,-11907831699439⟩,⟨0,0⟩,⟨102414856889766,102414856913318⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7453176928337,7453176928476⟩,⟨-44848400825433,-44848400823759⟩,⟨-20060901843395,-20060901842600⟩,⟨539737369926453,539737369956659⟩,⟨291949369697936,291949369713886⟩,⟨107991474402914,107991474409453⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6353665300561,6353665300700⟩,⟨-44848400825434,-44848400823758⟩,⟨-20060901843396,-20060901842599⟩,⟨539737369926462,539737369956659⟩,⟨291949369697939,291949369713887⟩,⟨107991474402915,107991474409454⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1928725639680,1928725678272⟩,⟨-7761085273186,-7761085272691⟩,⟨-3471570156306,-3471570156076⟩,⟨38619480154477,38619480171262⟩,⟨26017636908669,26017636916888⟩,⟨7727044364360,7727044367880⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101523589692,101523589694⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138274190462,138274190466⟩,⟨688058070218,688058070224⟩,⟨307771629648,307771629653⟩,⟨-1732836851712,-1732836851712⟩,⟨-1550212241822,-1550212241814⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4309265216576,4309265313024⟩,⟨-19668916973029,-19668916972130⟩,⟨-3471570156306,-3471570156076⟩,⟨141034337044243,141034337084580⟩,⟨26017636908669,26017636916888⟩,⟨7727044364360,7727044367880⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨721368261034,721369429254⟩,⟨-5341505021138,-5341485266946⟩,⟨5693496406734,5693517454202⟩,⟨68064019632108,68064554104152⟩,⟨-33648648529810,-33647969965864⟩,⟨-10793944821156,-10793083810734⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5030633477610,5030634742278⟩,⟨-25010421994167,-25010402239076⟩,⟨2221926250428,2221947298126⟩,⟨209098356676351,209098891188732⟩,⟨-7631011621141,-7630333048976⟩,⟨-3066900456796,-3066039442854⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨464504381917,464504498701⟩,⟨1685688924188,1685691752658⟩,⟨205161931239,205163874686⟩,⟨-30477722124068,-30477638863329⟩,⟨1059911169321,1059990540247⟩,⟨-283182765642,-283103263769⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35271681934,35271683987⟩,⟨-722831987168,-722831976779⟩,⟨314071324370,314071342618⟩,⟨8944234224033,8944234251485⟩,⟨-6436347433334,-6436347341287⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨499776063851,499776182688⟩,⟨962856937020,962859775879⟩,⟨519233255609,519235217304⟩,⟨-21533487900035,-21533404611844⟩,⟨-5376436264013,-5376356801040⟩,⟨-283182765642,-283103263769⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507836879489,507836891833⟩,⟨2540279524621,2540279648204⟩,⟨0,0⟩,⟨3565745386739,3565748309078⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨230834045132,230834105631⟩,⟨1599387509655,1599389162397⟩,⟨239820834627,239821746515⟩,⟨-3875878834967,-3875825076680⟩,⟨-1283619961878,-1283578608955⟩,⟨-130795029258,-130758306154⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-721369429254,-721368261034⟩,⟨5341485266946,5341505021138⟩,⟨-5693517454202,-5693496406734⟩,⟨-68064554104152,-68064019632108⟩,⟨33647969965864,33648648529810⟩,⟨10793083810734,10793944821156⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3587895787322,3587897051990⟩,⟨-14327431706083,-14327411950992⟩,⟨-9165087610508,-9165066562810⟩,⟨72969782940091,72970317452472⟩,⟨59665606874533,59666285446698⟩,⟨18520128175094,18520989189036⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451212495549,451212654607⟩,⟨443439267612,443442543489⟩,⟨-148286323040,-148283322036⟩,⟨-14409681707108,-14409587768587⟩,⟨-7300948657791,-7300842836252⟩,⟨-3933207205198,-3933086742238⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨324405506864,324405506870⟩,⟨1952062636032,1952062636032⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-324405506870,-324405506864⟩,⟨-1952062636032,-1952062636032⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨775106120906,775106120912⟩,⟨-1952062636032,-1952062636032⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1359664610267,1359664637484⟩,⟨-8895456659845,-8895456590937⟩,⟨-3978979843673,-3978979812839⟩,⟨54782908233118,54782908246920⟩,⟨34525498390152,34525498474090⟩,⟨10961047653524,10961047656426⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1359664637484,-1359664610267⟩,⟨8895456590937,8895456659845⟩,⟨3978979812839,3978979843673⟩,⟨-54782908246920,-54782908233118⟩,⟨-34525498474090,-34525498390152⟩,⟨-10961047656426,-10961047653524⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-260153009708,-260152982491⟩,⟨8895456590937,8895456659845⟩,⟨3978979812839,3978979843673⟩,⟨-54782908246920,-54782908233118⟩,⟨-34525498474090,-34525498390152⟩,⟨-10961047656426,-10961047653524⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11600966055,-11600964839⟩,⟨425890226303,425890232467⟩,⟨74135042365,74135054563⟩,⟨-4440929374075,-4440929357780⟩,⟨1805825994138,1805826056058⟩,⟨2671085080738,2671085105403⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439611529494,439611689768⟩,⟨869329493915,869332775956⟩,⟨-74151280675,-74148267473⟩,⟨-18850611081183,-18850517126367⟩,⟨-5495122663653,-5495016780194⟩,⟨-1262122124460,-1262001636835⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101523589694,-101523589692⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4527226953,4527226955⟩,⟨27535429834,27535429839⟩,⟨40312003485,40312003486⟩,⟨-294182191109,-294182191099⟩,⟨245185044806,245185044811⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9801845349,9801845592⟩,⟨10586267161,10586268646⟩,⟨87279040344,87279042468⟩,⟨-811661806335,-811661790419⟩,⟨94263805138,94263818079⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1466288427580,1466288448586⟩,⟨-7278550178655,-7278549805540⟩,⟨-1361999830665,-1361999764109⟩,⟨105690275511445,105690282844468⟩,⟨22432470910269,22432472395564⟩,⟨4981760647282,4981760928811⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13071560173,13071560686⟩,⟨-50768634498,-50768627378⟩,⟨104251862275,104251867672⟩,⟨-280375361783,-280375209472⟩,⟨-265195784761,-265195701341⟩,⟨-171819587826,-171819568385⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13071560686,-13071560173⟩,⟨50768627378,50768634498⟩,⟨-104251867672,-104251862275⟩,⟨280375209472,280375361783⟩,⟨265195701341,265195784761⟩,⟨171819568385,171819587826⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114595150380,-114595149865⟩,⟨-822398223900,-822398216778⟩,⟨-104251867672,-104251862275⟩,⟨2479398465024,2479398617335⟩,⟨265195701341,265195784761⟩,⟨171819568385,171819587826⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86007387334,86007389063⟩,⟨-562693903139,-562693898753⟩,⟨611032459668,611032475019⟩,⟨3465365482228,3465365483231⟩,⟨-3460347860041,-3460347820755⟩,⟨-2412343906518,-2412343906143⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨114697865441,114697869391⟩,⟨-1319750178749,-1319750121515⟩,⟨708321545195,708321584690⟩,⟨20338630658415,20338631905739⟩,⟨-6207802883799,-6207802265368⟩,⟨-4341178320431,-4341178131979⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-114697869391,-114697865441⟩,⟨1319750121515,1319750178749⟩,⟨-708321584690,-708321545195⟩,⟨-20338631905739,-20338630658415⟩,⟨6207802265368,6207802883799⟩,⟨4341178131979,4341178320431⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨984813758385,984813762335⟩,⟨1319750121515,1319750178749⟩,⟨-708321584690,-708321545195⟩,⟨-20338631905739,-20338630658415⟩,⟨6207802265368,6207802883799⟩,⟨4341178131979,4341178320431⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123849827283,123849827785⟩,⟨782253149539,782253159220⟩,⟨186587514331,186587520412⟩,⟨-2458091328519,-2458091093707⟩,⟨-681644682600,-681644558478⟩,⟨-161138013760,-161137966677⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11943528418,11943528526⟩,⟨171426739870,171426742128⟩,⟨21731025810,21731027034⟩,⟨713429052764,713429108147⟩,⟨100674505656,100674532722⟩,⟨-16045743393,-16045737129⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨173896480980,173896634659⟩,⟨1673144197831,1673149624590⟩,⟨111808375224,111811149381⟩,⟨-1904694963746,-1904487059587⟩,⟨433346127492,433484373017⟩,⟨-556223527219,-556115323243⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-173896634659,-173896480980⟩,⟨-1673149624590,-1673144197831⟩,⟨-111811149381,-111808375224⟩,⟨1904487059587,1904694963746⟩,⟨-433484373017,-433346127492⟩,⟨556115323243,556223527219⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56937410473,56937624651⟩,⟨-73762114935,-73755035434⟩,⟨128009685246,128013371291⟩,⟨-1971391775380,-1971130112934⟩,⟨-1717104334895,-1716924736447⟩,⟨425320293985,425465221065⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28082036545565,28082061670578⟩,⟨-245873947246328,-245873328456243⟩,⟨-83584859685884,-83584414688224⟩,⟨3460907051176983,3460928803309244⟩,⟨1300166654279472,1300184883077368⟩,⟨299572272927197,299589775539512⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13950538885,13950538999⟩,⟨176227181258,176227184154⟩,⟨42034719486,42034721028⟩,⟨559313416025,559313498723⟩,⟨111935322272,111935362800⟩,⟨27026517726,27026532611⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨356303228544,356303550241⟩,⟨1381289670926,1381301648538⟩,⟨13066422993,13073077686⟩,⟨-20619307702916,-20618816809543⟩,⟨-3441318733728,-3440988175318⟩,⟨-1899732721817,-1899475361598⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-356303550241,-356303228544⟩,⟨-1381301648538,-1381289670926⟩,⟨-13073077686,-13066422993⟩,⟨20618816809543,20619307702916⟩,⟨3440988175318,3441318733728⟩,⟨1899475361598,1899732721817⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83307979253,83308461224⟩,⟨-511972154623,-511956894970⟩,⟨-87224358361,-87214690466⟩,⟨1768205728360,1768790576549⟩,⟨-2054134488335,-2053698046466⟩,⟨637353237138,637731084982⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239797780154,239797780160⟩,⟨1561224921494,1561224921502⟩,⟨307771629648,307771629653⟩,⟨-3931860107264,-3931860107264⟩,⟨-1550212241822,-1550212241814⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1668494444998,-1668492978082⟩,⟨-4079409935191,-4079368588052⟩,⟨445097406764,445122595050⟩,⟨40725446464222,40726936501064⟩,⟨-7503460552985,-7502345017549⟩,⟨2024263643118,2025257977772⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187940485988,-187940319991⟩,⟨-1646566732851,-1646561015279⟩,⟨-233007999089,-233004903492⟩,⟨2512828924263,2513059322639⟩,⟨-186420287874,-186268568473⟩,⟨623605506919,623726350736⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51857294166,51857460169⟩,⟨-85341811357,-85336093777⟩,⟨74763630559,74766726161⟩,⟨-1419031183001,-1418800784625⟩,⟨-1736632529696,-1736480810287⟩,⟨276896872416,277017716236⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4314043153,4314084341⟩,⟨-32101058118,-32099599443⟩,⟨5182192057,5183045095⟩,⟨10879592024,10939552529⟩,⟨-290232144214,-290190079629⟩,⟨44919987668,44953681816⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2445794014,2445809674⟩,⟨-8050136938,-8049571838⟩,⟨7052293918,7052608498⟩,⟨-120608281851,-120584345285⟩,⟨-175419845760,-175403751892⟩,⟨36286515788,36298840365⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4290328092,4290355649⟩,⟨-31385428218,-31384326115⟩,⟨4648554955,4649156475⟩,⟨-12021855535,-11971334799⟩,⟨-274207398413,-274174785609⟩,⟨36305429470,36329146656⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4290355649,-4290328092⟩,⟨31384326115,31385428218⟩,⟨-4649156475,-4648554955⟩,⟨11971334799,12021855535⟩,⟨274174785609,274207398413⟩,⟨-36329146656,-36305429470⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨23687504,23756249⟩,⟨-716732003,-714171225⟩,⟨533035582,534490140⟩,⟨22850926823,22961408064⟩,⟨-16057358605,-15982681216⟩,⟨8590841012,8648252346⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56937410473,56937624651⟩,⟨-73762114935,-73755035434⟩,⟨128009685246,128013371291⟩,⟨-1971391775380,-1971130112934⟩,⟨-1717104334895,-1716924736447⟩,⟨425320293985,425465221065⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨23687504,23756249⟩,⟨-716732003,-714171225⟩,⟨533035582,534490140⟩,⟨22850926823,22961408064⟩,⟨-16057358605,-15982681216⟩,⟨8590841012,8648252346⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112957639884,113387136615⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121547574476,125413045044⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113387136615,-112957639884⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436368677273,436798174004⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨48239193620,49822291723⟩,⟨-125413045044,-121547574476⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161196833504,163209428338⟩,⟨974098582732,977964053300⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47809696889,50251788454⟩,⟨-125413045044,-121547574476⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2111057082880,-2097414275200⟩,⟨6562321363541,6670620165276⟩,⟨2939734790720,2979367899909⟩,⟨-40469943441518,-39166535933323⟩,⟨-25575195477891,-24952708641496⟩,⟨-8073250758578,-7859890174380⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313361324230,-307497011552⟩,⟨-915599700678,-868003707218⟩,⟨-407662755075,-390159549359⟩,⟨5620331235470,6124293484341⟩,⟨3509923168860,3752814886414⟩,⟨1135036403122,1214880748134⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307497011552,313361324230⟩,⟨868003707218,915599700678⟩,⟨390159549359,407662755075⟩,⟨-6124293484341,-5620331235470⟩,⟨-3752814886414,-3509923168860⟩,⟨-1214880748134,-1135036403122⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-163209428338,-161196833504⟩,⟨-977964053300,-974098582732⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨936302199438,938314794272⟩,⟨-977964053300,-974098582732⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-176672935168,-174312055744⟩,⟨-1148435674718,-1141442855693⟩,⟨-512937672898,-511334189322⟩,⟨-1199536653953,-1184973182546⟩,⟨752639676535,760335995996⟩,⟨-239292654695,-237798897769⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150771328496,-148437503577⟩,⟨-825636613995,-814866940829⟩,⟨-368556980741,-365246624489⟩,⟨998818675110,1033881396971⟩,⟨1370266596709,1387020886673⟩,⟨201660995677,205044531681⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148437503577,150771328496⟩,⟨814866940829,825636613995⟩,⟨365246624489,368556980741⟩,⟨-1033881396971,-998818675110⟩,⟨-1387020886673,-1370266596709⟩,⟨-205044531681,-201660995677⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨455934515129,464132652726⟩,⟨1682870648047,1741236314673⟩,⟨755406173848,776219735816⟩,⟨-7158174881312,-6619149910580⟩,⟨-5139835773087,-4880189765569⟩,⟨-1419925279815,-1336697398799⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨819452381877,829532723332⟩,⟨4056427101956,4128747351969⟩,⟨755406173848,776219735816⟩,⟨-19168574743639,-18424182321815⟩,⟨-5139835773087,-4880189765569⟩,⟨-1419925279815,-1336697398799⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95619393778,100503576908⟩,⟨-250826090088,-243095148952⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12028684518574,12643102741495⟩,⟨29094634685648,33165029623520⟩,⟨-115509709338924,-104452822758913⟩,⟨140746524058256,173995135912159⟩,⟨-342815392098209,-214533037951189⟩,⟨1814062404822040,2110635850133860⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8964829412063,9538659877325⟩,⟨66061283700962,72497327262322⟩,⟨-78882786702348,-68921770920195⟩,⟨99157972553561,178784865738725⟩,⟨-731499492261089,-575222459341216⟩,⟨1172578472662740,1434231470776353⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨87447846912,92989546752⟩,⟨-744700651637,-599759457949⟩,⟨625729347845,810292804970⟩,⟨6339146569886,10982270542831⟩,⟨-7706754072910,-1015609704840⟩,⟨-5833593378480,3422234412407⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1186959474688,1192501174528⟩,⟨-744700651637,-599759457949⟩,⟨625729347845,810292804970⟩,⟨6339146569886,10982270542831⟩,⟨-7706754072910,-1015609704840⟩,⟨-5833593378480,3422234412407⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨84144379776,89265855104⟩,⟨-689835704714,-552991067823⟩,⟨576935862615,750595433094⟩,⟨5412024685240,9895041963113⟩,⟨-6848802473037,-465488888722⟩,⟨-5916213636598,2867375457119⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨90836664473,96815380909⟩,⟨-808637404197,-642871214016⟩,⟨670707864901,879861013965⟩,⟨6930877843841,12557969177262⟩,⟨-9070475063605,-1209645939528⟩,⟨-6233513895074,4494032909295⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-92989546752,-87447846912⟩,⟨599759457949,744700651637⟩,⟨-810292804970,-625729347845⟩,⟨-10982270542831,-6339146569886⟩,⟨1015609704840,7706754072910⟩,⟨-3422234412407,5833593378480⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1006522081024,1012063780864⟩,⟨599759457949,744700651637⟩,⟨-810292804970,-625729347845⟩,⟨-10982270542831,-6339146569886⟩,⟨1015609704840,7706754072910⟩,⟨-3422234412407,5833593378480⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-97158567360,-91121490688⟩,⟨651581955951,813501304268⟩,⟨-885153319301,-679795786396⟩,⟨-12598778856122,-7273017712570⟩,⟨1506217948849,9073660818220⟩,⟨-4450990176775,5952243725632⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-89431220682,-83415027286⟩,⟨530669765644,699096044513⟩,⟨-762897092531,-550701389803⟩,⟨-10360554730904,-4585491613657⟩,⟨-501208039837,7526206626586⟩,⟨-3838734459288,7085888150066⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1405443791,13400353623⟩,⟨-277967638553,56224830497⟩,⟨-92189227630,329159624162⟩,⟨-3429676887063,7972477563605⟩,⟨-9571683103442,6316560687058⟩,⟨-10072248354362,11579921059361⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨702721895,6700176812⟩,⟨-138983819277,28112415249⟩,⟨-46094613815,164579812081⟩,⟨-1714838443532,3986238781803⟩,⟨-4785841551721,3158280343529⟩,⟨-5036124177181,5789960529681⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6700176812,-702721895⟩,⟨-28112415249,138983819277⟩,⟨-164579812081,46094613815⟩,⟨-3986238781803,1714838443532⟩,⟨-3158280343529,4785841551721⟩,⟨-5789960529681,5036124177181⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755423206804,761420680985⟩,⟨-28112415249,138983819277⟩,⟨-164579812081,46094613815⟩,⟨-3986238781803,1714838443532⟩,⟨-3158280343529,4785841551721⟩,⟨-5789960529681,5036124177181⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6955020516,7864451441⟩,⟨-125963881260,-95401761904⟩,⟨99532706768,137058597232⟩,⟨1662658407793,2866391552079⟩,⟨-2401199068206,-844192939398⟩,⟨-274532771884,1773162615201⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7864451441,-6955020516⟩,⟨95401761904,125963881260⟩,⟨-137058597232,-99532706768⟩,⟨-2866391552079,-1662658407793⟩,⟨844192939398,2401199068206⟩,⟨-1773162615201,274532771884⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091647176335,1092556607260⟩,⟨95401761904,125963881260⟩,⟨-137058597232,-99532706768⟩,⟨-2866391552079,-1662658407793⟩,⟨844192939398,2401199068206⟩,⟨-1773162615201,274532771884⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7892712256,-6977110848⟩,⟨96009072506,126871351045⟩,⟨-138045995639,-100166314228⟩,⟨-2901681163785,-1681626082213⟩,⟨858313417889,2434426766370⟩,⟨-1803268809322,267385338047⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3946356128,-3488555424⟩,⟨48004536253,63435675523⟩,⟨-69022997820,-50083157114⟩,⟨-1450840581893,-840813041106⟩,⟨429156708944,1217213383185⟩,⟨-901634404661,133692669024⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3488555424,3946356128⟩,⟨-63435675523,-48004536253⟩,⟨50083157114,69022997820⟩,⟨840813041106,1450840581893⟩,⟨-1217213383185,-429156708944⟩,⟨-133692669024,901634404661⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765611939040,766069759008⟩,⟨-63435675523,-48004536253⟩,⟨50083157114,69022997820⟩,⟨840813041106,1450840581893⟩,⟨-1217213383185,-429156708944⟩,⟨-133692669024,901634404661⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272911794083,273139151815⟩,⟨23850440476,31490970315⟩,⟨-34264649308,-24883176692⟩,⟨-716597888020,-415664601948⟩,⟨211048234849,600299767052⟩,⟨-443290653801,68633192971⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531223878080,1532139518016⟩,⟨-126871351046,-96009072506⟩,⟨100166314228,138045995640⟩,⟨1681626082212,2901681163786⟩,⟨-2434426766370,-858313417888⟩,⟨-267385338048,1803268809322⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1194515447023,1201092198976⟩,⟨-888658242196,-707882201264⟩,⟨738533860996,966929971319⟩,⟨8320944537822,14420238257836⟩,⟨-10627356475857,-2074026219058⟩,⟨-6048053812975,5640623251282⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1289519266270,1302672770176⟩,⟨-1777316484392,-1415764402527⟩,⟨1477067721991,1933859942638⟩,⟨16641889075649,28840476515665⟩,⟨-21254712951709,-4148052438116⟩,⟨-12091504824701,11281246502562⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨175265870464,186424422400⟩,⟨-1515433070248,-1194965810606⟩,⟨1246708438621,1648910217194⟩,⟨11957778770834,23292193109504⟩,⟨-16767939341372,-1228476720046⟩,⟨-12782679562278,8205370116540⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨60081340909,64396012033⟩,⟨-518088780202,-400312429222⟩,⟨415990387782,565032693525⟩,⟨3829934222351,7788422074566⟩,⟨-5656033835106,-79127513616⟩,⟨-4772064242703,2863787112123⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380067882096,380611971572⟩,⟨1697872671,20051222105⟩,⟨-22884391687,-360112746⟩,⟨-588427570246,137795223784⟩,⟨-306497117042,631365351817⟩,⟨-692740948904,539070268207⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176268509425,3180815524184⟩,⟨-167810124336,-14169022260⟩,⟨3005199153,191521124959⟩,⟨-1153091755460,4942299086382⟩,⟨-5304150318104,2565069672096⟩,⟨-4511512277639,5820662459537⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨173562940411,186293468478⟩,⟨-1508625371352,-1157196544887⟩,⟨1201876989698,1645819756872⟩,⟨11006694898700,22979001442183⟩,⟨-16849671290668,-84807805154⟩,⟨-14067226544821,8822496373058⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨348828810875,372717890878⟩,⟨-3024058441600,-2352162355493⟩,⟨2448585428319,3294729974066⟩,⟨22964473669534,46271194551687⟩,⟨-33617610632040,-1313284525200⟩,⟨-26849906107099,17027866489598⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519016085834,527289970189⟩,⟨-38936149146,192494834338⟩,⟨-227945697756,63841784580⟩,⟨-5528112194317,2410215452028⟩,⟨-4415876720980,6640121025838⟩,⟨-8032988138923,7024383403512⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356591768598,365152562316⟩,⟨-40445396550,199956340813⟩,⟨-236781354597,66316427034⟩,⟨-5749776091230,2540138973117⟩,⟨-4630265662443,6909611031512⟩,⟨-8358697916258,7347843240550⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713183537196,730305124632⟩,⟨-80890793100,399912681626⟩,⟨-473562709194,132632854068⟩,⟨-11499552182460,5080277946234⟩,⟨-9260531324886,13819222063024⟩,⟨-16717395832516,14695686481100⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523359426639,1525184497500⟩,⟨-31469589142,29954808754⟩,⟨-36892283004,38513288872⟩,⟨-1184765469867,1239022755993⟩,⟨-1590233826972,1542885650318⟩,⟨-2040547953249,2077801581206⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988106752912,1013040723168⟩,⟨-133109811803,574634007272⟩,⟨-681405368592,209562154045⟩,⟨-16761395442317,7891853284145⟩,⟨-13928287354017,20221655478696⟩,⟨-24578014294527,21796953626830⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67739936048,67852848820⟩,⟨11839922990,15645886236⟩,⟨-17023953204,-12352597684⟩,⟨-354997784264,-204541886054⟩,⟨102806598726,297171744904⟩,⟨-219117029164,36235138955⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50485734339,51191962910⟩,⟨258737023218,266596584432⟩,⟨33696087159,38695684263⟩,⟨-1363395416711,-1170037144405⟩,⟨-296359792866,-110988205157⟩,⟨-276976950952,-71988342750⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132443628217,2134994704344⟩,⟨-353583546970,-267412150302⟩,⟨278991232562,384726672972⟩,⟨4700566483894,8116106472582⟩,⟨-6816472768052,-2408136197612⟩,⟨-726937928369,5060275909784⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2969726303659,2975056993165⟩,⟨-739063569063,-558613287236⟩,⟨582801526989,804159216335⟩,⟨9854320933073,17025559484020⟩,⟨-14314443561755,-5067042371038⟩,⟨-1481335458281,10649489927434⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136359461272,138515140179⟩,⟨664425923572,695707086244⟩,⟨117771668947,142143430684⟩,⟨-3594996166247,-2630427982246⟩,⟨-1357218913155,-354570992274⟩,⟨-782691515828,357993122289⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8727752201328,8865727455488⟩,⟨-45233013961446,-41865061173677⟩,⟨-9241785676454,-7420719075025⟩,⟨567376153843923,695295449390638⟩,⟨93532331495224,182546075780760⟩,⟨-10656911334616,70156099292348⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7843437640872,8168483830485⟩,⟨-42748979910966,-32989738576048⟩,⟨-14009364831220,-4979066658730⟩,⟨327455735843489,715200750304049⟩,⟨-41704191438584,360394993273404⟩,⟨-211522381800644,251849669919263⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15686875281744,16336967660970⟩,⟨-85497959821932,-65979477152096⟩,⟨-28018729662440,-9958133317460⟩,⟨654911471686978,1430401500608098⟩,⟨-83408382877168,720789986546808⟩,⟨-423044763601288,503699339838526⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10661930935953,10702470597440⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710694,2028067813858452⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9562419308177,9602958969664⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710699,2028067813858436⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2378215779456,2382867339072⟩,⟨-11978441145317,-11837681660582⟩,⟨0,0⟩,⟨99082204851667,105744330752101⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7407205771905,7499687142333⟩,⟨-45499804659728,-44209141088796⟩,⟨-20322047140532,-19804447683506⟩,⟨527715366899134,552084956287751⟩,⟨286302563472943,297738208376820⟩,⟨105901242688946,110134087501017⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6307694144129,6400175514557⟩,⟨-45499804659728,-44209141088795⟩,⟨-20322047140532,-19804447683505⟩,⟨527715366899138,552084956287745⟩,⟨286302563472943,297738208376818⟩,⟨105901242688946,110134087501017⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1920741340096,1936745026880⟩,⟨-7931196906822,-7594864323711⟩,⟨-3542392294355,-3402284899861⟩,⟨33447573909532,43774016329494⟩,⟨23632429742767,28398326273130⟩,⟨6780362499725,8669883065397⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101308883270,101738380002⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137269080143,139281674978⟩,⟨684338093748,691776706318⟩,⟨306757439846,308785219898⟩,⟨-1739706366693,-1725980926276⟩,⟨-1554140962494,-1546283521142⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4298957119552,4319612365952⟩,⟨-19909638052139,-19432545984293⟩,⟨-3542392294355,-3402284899861⟩,⟨132529778761199,149518347081595⟩,⟨23632429742767,28398326273130⟩,⟨6780362499725,8669883065397⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨697657621750,745435781756⟩,⟨-6048116883200,-4704324710986⟩,⟨4897170856638,6589459948132⟩,⟨45928947339068,92542389103374⟩,⟨-67235221264080,-2626569050400⟩,⟨-53699812214198,34055732979196⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4996614741302,5065048147708⟩,⟨-25957754935339,-24136870695279⟩,⟨1354778562283,3187175048271⟩,⟨178458726100267,242060736184969⟩,⟨-43602791521313,25771757222730⟩,⟨-46919449714473,42725616044593⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨460387545510,468671526669⟩,⟨1564178451552,1800370363118⟩,⟨124829151193,294910956831⟩,⟨-34935423395195,-25912506506610⟩,⟨-2959233383537,4916984209811⟩,⟨-4341480966592,3953423366479⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34272913303,36277382795⟩,⟨-743322776911,-702525135578⟩,⟨312815742780,315329962371⟩,⟨8607744828889,9288041686265⟩,⟨-6467888110707,-6405006849897⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨494660458813,504948909464⟩,⟨820855674641,1097845227540⟩,⟨437644893973,610240919202⟩,⟨-26327678566306,-16624464820345⟩,⟨-9427121494244,-1488022640086⟩,⟨-4341480966592,3953423366479⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507340798957,508333108400⟩,⟨2520383226112,2560338836291⟩,⟨0,0⟩,⟨2439291441574,4695713285828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228248093104,233451145261⟩,⟨1512660216407,1683394093836⟩,⟨201939756305,282130407260⟩,⟨-7311307774265,-401507729053⟩,⟨-3355203373459,734406903430⟩,⟨-2007180696462,1827771474113⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-745435781756,-697657621750⟩,⟨4704324710986,6048116883200⟩,⟨-6589459948132,-4897170856638⟩,⟨-92542389103374,-45928947339068⟩,⟨2626569050400,67235221264080⟩,⟨-34055732979196,53699812214198⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3553521337796,3621954744202⟩,⟨-15205313341153,-13384429101093⟩,⟨-10131852242487,-8299455756499⟩,⟨39987389657825,103589399742527⟩,⟨26258998793167,95633547537210⟩,⟨-27275370479471,62369695279595⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443641152112,458814541587⟩,⟨285570884151,607829544998⟩,⟨-292049883632,-18965297596⟩,⟨-19871976015625,-9116915260109⟩,⟨-12486120812652,-1782753077339⟩,⟨-10289195777676,2150310352205⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨322393667008,326418856676⟩,⟨1948197165464,1955928106600⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-326418856676,-322393667008⟩,⟨-1955928106600,-1948197165464⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨773092771100,777117960768⟩,⟨-1955928106600,-1948197165464⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1350518910095,1368861690769⟩,⟨-9050936205379,-8743443268494⟩,⟨-4042513008732,-3916815855725⟩,⟨50432085022626,59156515092278⟩,⟨32514853108708,36548159244420⟩,⟨10168561384313,11756823178984⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1368861690769,-1350518910095⟩,⟨8743443268494,9050936205379⟩,⟨3916815855725,4042513008732⟩,⟨-59156515092278,-50432085022626⟩,⟨-36548159244420,-32514853108708⟩,⟨-11756823178984,-10168561384313⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-269350062993,-251007282319⟩,⟨8743443268494,9050936205379⟩,⟨3916815855725,4042513008732⟩,⟨-59156515092278,-50432085022626⟩,⟨-36548159244420,-32514853108708⟩,⟨-11756823178984,-10168561384313⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12310303997,-10914465824⟩,⟨407936294117,444384334594⟩,⟨63310074573,85139429545⟩,⟨-4768418532081,-4126042169554⟩,⟨1589574791669,2018151640451⟩,⟨2571641850306,2769746755459⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨431330848115,447900075763⟩,⟨693507178268,1052213879592⟩,⟨-228739809059,66174131949⟩,⟨-24640394547706,-13242957429663⟩,⟨-10896546020983,235398563112⟩,⟨-7717553927370,4920057107664⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101738380002,-101308883270⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4405180335,4649823995⟩,⟨26344412935,28727235841⟩,⟨40206963047,40417161119⟩,⟨-299792743799,-288576168258⟩,⟨244629257582,245740915920⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9528293398,10077122834⟩,⟨6325586111,14830283877⟩,⟨86966641867,87592282552⟩,⟨-878668620233,-744255356201⟩,⟨88809042402,99690417602⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1457357600986,1475285015154⟩,⟨-7433109274479,-7126499900007⟩,⟨-1397451969198,-1327128994823⟩,⟨102065746703145,109412058018129⟩,⟨21553080657348,23335309474918⟩,⟨4765440681884,5203785087400⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12629362398,13521119684⟩,⟨-59740809046,-41859026508⟩,⟨102462946786,106027352970⟩,⟨-494987497861,-65707381361⟩,⟨-306515183279,-223679375370⟩,⟨-181358244382,-162247235930⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13521119684,-12629362398⟩,⟨41859026508,59740809046⟩,⟨-106027352970,-102462946786⟩,⟨65707381361,494987497861⟩,⟨223679375370,306515183279⟩,⟨162247235930,181358244382⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115259499686,-113938245668⟩,⟨-831737321500,-812996545500⟩,⟨-106027352970,-102462946786⟩,⟨2264730636913,2694010753413⟩,⟨223679375370,306515183279⟩,⟨162247235930,181358244382⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨83518954190,88516482156⟩,⟨-583395304097,-542576901637⟩,⟨600393659409,621461805587⟩,⟨3133566719342,3809940352066⟩,⟨-3683823909935,-3232989409015⟩,⟨-2519713139602,-2304317598093⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨110700950895,118768220745⟩,⟨-1381183241851,-1260492709118⟩,⟨683294939178,733046239066⟩,⟨18939772572067,21808228195723⟩,⟨-6852063442675,-5556558445827⟩,⟨-4598602084420,-4084716860462⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-118768220745,-110700950895⟩,⟨1260492709118,1381183241851⟩,⟨-733046239066,-683294939178⟩,⟨-21808228195723,-18939772572067⟩,⟨5556558445827,6852063442675⟩,⟨4084716860462,4598602084420⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨980743407031,988810676881⟩,⟨1260492709118,1381183241851⟩,⟨-733046239066,-683294939178⟩,⟨-21808228195723,-18939772572067⟩,⟨5556558445827,6852063442675⟩,⟨4084716860462,4598602084420⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122441402108,125258527362⟩,⟨767783374913,797089986556⟩,⟨180762461853,192389829437⟩,⟨-2758061260417,-2166096951852⟩,⟨-813494177165,-548658390924⟩,⟨-213884876776,-107691801983⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11806990938,12082411802⟩,⟨168495535268,174378560672⟩,⟨21235697936,22229250420⟩,⟨637470386949,788982172338⟩,⟨87262806312,114052947436⟩,⟨-18925866330,-13177424713⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨168451874103,179525132695⟩,⟨1464420064148,1882470148883⟩,⟨-4922262550,223356396783⟩,⟨-10991761956584,7219370280131⟩,⟨-5843789931520,6814970678303⟩,⟨-6062930903621,4962434475644⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-179525132695,-168451874103⟩,⟨-1882470148883,-1464420064148⟩,⟨-223356396783,4922262550⟩,⟨-7219370280131,10991761956584⟩,⟨-6814970678303,5843789931520⟩,⟨-4962434475644,6062930903621⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48722960409,64999271158⟩,⟨-369809932476,218974029688⟩,⟨-21416640478,287052669810⟩,⟨-14530678054396,10590254227531⟩,⟨-10170174051762,6578196834950⟩,⟨-6969615172106,7890702377734⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27403466311239,28776904284026⟩,⟨-268445961294720,-223616733630270⟩,⟨-101988083487025,-65936744458769⟩,⟨2532773407808372,4403464109481082⟩,⟨463196427081800,2169161540139016⟩,⟨-586811736794177,1196607131393171⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13635050845,14269697820⟩,⟨171000416120,181612118270⟩,⟨40259345546,43834855596⟩,⟨443870920094,673267093192⟩,⟨67101301044,156748690456⟩,⟨10703230008,43342718057⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339830563901,373472838263⟩,⟨777946655650,1980160060552⟩,⟨-320227184802,329583218028⟩,⟨-46209591659005,5214620521237⟩,⟨-20131707744421,13811720849221⟩,⟨-15481042630810,11835573845462⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-373472838263,-339830563901⟩,⟨-1980160060552,-777946655650⟩,⟨-329583218028,320227184802⟩,⟨-5214620521237,46209591659005⟩,⟨-13811720849221,20131707744421⟩,⟨-11835573845462,15481042630810⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57858009852,108069511862⟩,⟨-1286652882284,274267223942⟩,⟨-558323027087,386401316751⟩,⟨-29855015068943,32966634229342⟩,⟨-24708266870204,20367106307533⟩,⟨-19553127772832,20401099738474⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238577963413,241020054980⟩,⟨1557075448294,1565373054326⟩,⟨306757439846,308785219898⟩,⟨-3938729622245,-3925004181828⟩,⟨-1554140962494,-1546283521142⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1712570082409,-1625571757917⟩,⟨-5521069258035,-2636555419028⟩,⟨-543471466090,1475292533996⟩,⟨-20062216449419,101514333980022⟩,⟨-58855842435525,42737594997010⟩,⟨-48630956715649,52445352639887⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-195099352393,-181023356405⟩,⟨-1870497243263,-1428734788257⟩,⟨-361574622330,-99179835745⟩,⟨-7088052097567,12178409037899⟩,⟨-7253862169417,6771883508993⟩,⟨-5571108009350,6824105219194⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43478611020,59996698575⟩,⟨-313421794969,136638266069⟩,⟨-54817182484,209605384153⟩,⟨-11026781719812,8253404856071⟩,⟨-8808003131911,5225599987851⟩,⟨-5918157808540,6477737581610⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2563877863,6388690514⟩,⟨-112410524222,37736377780⟩,⟨-35111111824,51056709589⟩,⟨-3705613050573,3855279677137⟩,⟨-2926151203885,2109984167233⟩,⟨-2132472395437,2183365747639⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1719299340,3273820621⟩,⟨-34204773256,14911792938⟩,⟨-5982383254,22874939628⟩,⟨-1281288695662,1079406983861⟩,⟨-1080745286690,622383347208⟩,⟨-666768586146,786853499810⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3003451018,5766701913⟩,⟨-83865634663,14390475914⟩,⟨-21085277657,34973144814⟩,⟨-2419765086984,2525133794724⟩,⟨-2079783288794,1334213323795⟩,⟨-1311279711693,1450373148404⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5766701913,-3003451018⟩,⟨-14390475914,83865634663⟩,⟨-34973144814,21085277657⟩,⟨-2525133794724,2419765086984⟩,⟨-1334213323795,2079783288794⟩,⟨-1450373148404,1311279711693⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3202824050,3385239496⟩,⟨-126801000136,121602012443⟩,⟨-70084256638,72141987246⟩,⟨-6230746845297,6275044764121⟩,⟨-4260364527680,4189767456027⟩,⟨-3582845543841,3494645459332⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48722960409,64999271158⟩,⟨-369809932476,218974029688⟩,⟨-21416640478,287052669810⟩,⟨-14530678054396,10590254227531⟩,⟨-10170174051762,6578196834950⟩,⟨-6969615172106,7890702377734⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3202824050,3385239496⟩,⟨-126801000136,121602012443⟩,⟨-70084256638,72141987246⟩,⟨-6230746845297,6275044764121⟩,⟨-4260364527680,4189767456027⟩,⟨-3582845543841,3494645459332⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (527/5120) u, BivariateJet2.affineZ (115/1024) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000047

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000048Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2101538692608,-2101538653760⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2101538692544,-2101538653760⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-175955584064,-175955584000⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-175955584064,-175955584000⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨89742447168,89742447232⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-97723488768,-97723488704⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨89742570560,89742570624⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-97723635072,-97723635008⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7981064512,-7981064448⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7981041600,-7981041536⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨187465935872,187465935936⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨187466205568,187466205632⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1925583069696,1925583108288⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1925583069760,1925583108352⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2108382532672,-2108382493760⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2094732114432,-2094732075648⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-177141147200,-177141147136⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-174772182976,-174772182912⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨87171072960,87171073024⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-94681878208,-94681878144⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨92335877760,92335877824⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-100806979456,-100806979392⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8471101696,-8471101632⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7510805248,-7510805184⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨181852951104,181852951168⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨193142857152,193142857216⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1917590928512,1917590967104⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1933610310848,1933610349440⟩



end LaneCBRB2Cell000048Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000048
open Set LaneCBRB2Cell000048Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111883898060,111883898061⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨127345780326,127345780327⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111883898061,-111883898060⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437871915827,437871915828⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50714462125,50714462127⟩,⟨-127345780327,-127345780326⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨162598360185,162598360188⟩,⟨972165847449,972165847450⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨50714462124,50714462128⟩,⟨-127345780327,-127345780326⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2101538692608,-2101538653760⟩,⟨6573914104428,6573914104557⟩,⟨2960947837183,2960947837246⟩,⟨-39305038311881,-39305038310338⟩,⟨-25138372726609,-25138372725753⟩,⟨-7973732949622,-7973732949288⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310780474402,-310780468650⟩,⟨-885971977071,-885971942681⟩,⟨-399049450244,-399049434751⟩,⟨5812521318273,5812521318850⟩,⟨3620036959239,3620036998401⟩,⟨1179174343702,1179174343831⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨310780468650,310780474402⟩,⟨885971942681,885971977071⟩,⟨399049434751,399049450244⟩,⟨-5812521318850,-5812521318273⟩,⟨-3620036998401,-3620036959239⟩,⟨-1179174343831,-1179174343702⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-162598360188,-162598360185⟩,⟨-972165847450,-972165847449⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨936913267588,936913267591⟩,⟨-972165847450,-972165847449⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-175955584064,-175955584000⟩,⟨-1140882182350,-1140882182344⟩,⟨-513863214009,-513863214004⟩,⟨-1183809357830,-1183809357816⟩,⟨757130438035,757130438048⟩,⟨-240156989741,-240156989736⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149934859307,-149934859251⟩,⟨-816589494180,-816589494113⟩,⟨-367798979157,-367798979123⟩,⟨1008744851448,1008744851477⟩,⟨1377903459678,1377903459766⟩,⟨204642010416,204642010428⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149934859251,149934859307⟩,⟨816589494113,816589494180⟩,⟨367798979123,367798979157⟩,⟨-1008744851477,-1008744851448⟩,⟨-1377903459766,-1377903459678⟩,⟨-204642010428,-204642010416⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨460715327901,460715333709⟩,⟨1702561436794,1702561471251⟩,⟨766848413874,766848429401⟩,⟨-6821266170327,-6821266169721⟩,⟨-4997940458167,-4997940418917⟩,⟨-1383816354259,-1383816354118⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨822375713260,822375725016⟩,⟨4097126373038,4097126465439⟩,⟨766848413874,766848429401⟩,⟨-18850517967052,-18850517965941⟩,⟨-4997940458167,-4997940418917⟩,⟨-1383816354259,-1383816354118⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨101428924248,101428924256⟩,⟨-254691560654,-254691560652⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11918945492938,11918945493879⟩,⟨29928887161029,29928887165991⟩,⟨-102908939175849,-102908939159363⟩,⟨150304955623525,150304955661487⟩,⟨-258407929726705,-258407929558249⟩,⟨1777044750339768,1777044750768792⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8914731825881,8914731954024⟩,⟨66798944175431,66798945504299⟩,⟨-68657563150788,-68657561869179⟩,⟨131125229666385,131125236397342⟩,⟨-610051399272019,-610051386817536⟩,⟨1170586706938600,1170586729191898⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨93506557952,93506691840⟩,⟨-693364848613,-693362821211⟩,⟨712654988529,712657071467⟩,⟨8867924372359,8867974230250⟩,⟨-4181407211594,-4181341594977⟩,⟨-1344415251629,-1344331339127⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1193018185728,1193018319616⟩,⟨-693364848613,-693362821211⟩,⟨712654988529,712657071467⟩,⟨8867924372359,8867974230250⟩,⟨-4181407211594,-4181341594977⟩,⟨-1344415251629,-1344331339127⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨89742447168,89742570624⟩,⟨-639020194715,-639018254501⟩,⟨656798335445,656800328838⟩,⟨7801482691688,7801531814270⟩,⟨-3471955753437,-3471892529723⟩,⟨-1631386364348,-1631306508178⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨97374478630,97374623514⟩,⟨-749957637522,-749955211160⟩,⟨770822008415,770824501343⟩,⟨9994694629125,9994758748036⟩,⟨-4936884190002,-4936804405307⟩,⟨-1028441947059,-1028343028476⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-93506691840,-93506557952⟩,⟨693362821211,693364848613⟩,⟨-712657071467,-712654988529⟩,⟨-8867974230250,-8867924372359⟩,⟨4181341594977,4181407211594⟩,⟨1344331339127,1344415251629⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1006004935936,1006005069824⟩,⟨693362821211,693364848613⟩,⟨-712657071467,-712654988529⟩,⟨-8867974230250,-8867924372359⟩,⟨4181341594977,4181407211594⟩,⟨1344331339127,1344415251629⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-97723635072,-97723488704⟩,⟨757809783525,757812100229⟩,⟨-778897507065,-778895126857⟩,⟨-10214543374558,-10214484399059⟩,⟨5106823792512,5106899397973⟩,⟨917511329122,917606609006⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-89412853708,-89412707887⟩,⟨631737065567,631739550026⟩,⟨-649317107000,-649314554366⟩,⟨-7601923839157,-7601857306948⟩,⟨3318516360782,3318598421310⟩,⟨1729683186411,1729784148709⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7961624922,7961915627⟩,⟨-118220571955,-118215661134⟩,⟨121504901415,121509946977⟩,⟨2392770789968,2392901441088⟩,⟨-1618367829220,-1618205983997⟩,⟨701241239352,701441120233⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3980812461,3980957814⟩,⟨-59110285978,-59107830567⟩,⟨60752450707,60754973489⟩,⟨1196385394984,1196450720544⟩,⟨-809183914610,-809102991998⟩,⟨350620619676,350720560117⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3980957814,-3980812461⟩,⟨59107830567,59110285978⟩,⟨-60754973489,-60752450707⟩,⟨-1196450720544,-1196385394984⟩,⟨809102991998,809183914610⟩,⟨-350720560117,-350620619676⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758142425802,758142590419⟩,⟨59107830567,59110285978⟩,⟨-60754973489,-60752450707⟩,⟨-1196450720544,-1196385394984⟩,⟨809102991998,809183914610⟩,⟨-350720560117,-350620619676⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7952145442,7952168216⟩,⟨-117932819616,-117932305916⟩,⟨121213661230,121214189076⟩,⟨2382805334628,2382821088551⟩,⟨-1610025570814,-1610008136710⟩,⟨695154649357,695174649524⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7952168216,-7952145442⟩,⟨117932305916,117932819616⟩,⟨-121214189076,-121213661230⟩,⟨-2382821088551,-2382805334628⟩,⟨1610008136710,1610025570814⟩,⟨-695174649524,-695154649357⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091559459560,1091559482334⟩,⟨117932305916,117932819616⟩,⟨-121214189076,-121213661230⟩,⟨-2382821088551,-2382805334628⟩,⟨1610008136710,1610025570814⟩,⟨-695174649524,-695154649357⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7981064512,-7981041536⟩,⟨118791457308,118791977230⟩,⟨-122097251940,-122096717700⟩,⟨-2413014649389,-2412998618271⟩,⟨1634928598460,1634946308868⟩,⟨-713797606761,-713777327627⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3990532256,-3990520768⟩,⟨59395728654,59395988615⟩,⟨-61048625970,-61048358850⟩,⟨-1206507324695,-1206499309135⟩,⟨817464299230,817473154434⟩,⟨-356898803381,-356888663813⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3990520768,3990532256⟩,⟨-59395988615,-59395728654⟩,⟨61048358850,61048625970⟩,⟨1206499309135,1206507324695⟩,⟨-817473154434,-817464299230⟩,⟨356888663813,356898803381⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766113904384,766113935136⟩,⟨-59395988615,-59395728654⟩,⟨61048358850,61048625970⟩,⟨1206499309135,1206507324695⟩,⟨-817473154434,-817464299230⟩,⟨356888663813,356898803381⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272889864890,272889870584⟩,⟨29483076479,29483204904⟩,⟨-30303547269,-30303415307⟩,⟨-595705272138,-595701333657⟩,⟨402502034177,402506392704⟩,⟨-173793662381,-173788662339⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532227808768,1532227870272⟩,⟨-118791977230,-118791457308⟩,⟨122096717700,122097251940⟩,⟨2412998618270,2413014649390⟩,⟨-1634946308868,-1634928598460⟩,⟨713777327626,713797606762⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1201709470337,1201709630272⟩,⟨-828249629905,-828246987636⟩,⟨851292179817,851294894561⟩,⟨11734752031188,11734821540447⟩,⟨-6168312901845,-6168225861352⟩,⟨-399840661613,-399732465620⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1303907312898,1303907632768⟩,⟨-1656499259810,-1656493975271⟩,⟨1702584359633,1702589789121⟩,⟨23469504062381,23469643080880⟩,⟨-12336625803684,-12336451722706⟩,⟨-799681176356,-799465078110⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨187465935872,187466205632⟩,⟨-1396832565895,-1396827767074⟩,⟨1435693183812,1435698114394⟩,⟨18015954002617,18016088276975⟩,⟨-8578866674128,-8578704799541⟩,⟨-2549003037924,-2548807772768⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨64475251450,64475357770⟩,⟨-473066804852,-473065087078⟩,⟨486227677519,486229442405⟩,⟨5938366991979,5938411714040⟩,⟨-2737760476752,-2737704219435⟩,⟨-1035594417567,-1035524313868⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380286510076,380286533277⟩,⟨11603026337,11603336612⟩,⟨-11926188470,-11925869651⟩,⟨-237631038482,-237621469750⟩,⟨161675504334,161686061911⟩,⟨-71767184975,-71755111857⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178986668807,3178986862756⟩,⟨-96997536532,-96994930967⟩,⟨99693723855,99696401173⟩,⟨1992303928055,1992384477431⟩,⟨-1357690780056,-1357602033152⟩,⟨606086181220,606187514533⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨186415459054,186415777828⟩,⟨-1373452604369,-1373447392199⟩,⟨1411662272176,1411667627349⟩,⟨17369724109483,17369861921853⟩,⟨-8081013496681,-8080842407568⟩,⟨-2870470592851,-2870259032562⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨373881394926,373881983460⟩,⟨-2770285170264,-2770275159273⟩,⟨2847355455988,2847365741743⟩,⟨35385678112100,35385950198828⟩,⟨-16659880170809,-16659547207109⟩,⟨-5419473630775,-5419066805330⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522759308115,522759535131⟩,⟨81512833366,81516237210⟩,⟨-83784349012,-83780851768⟩,⟨-1643614292241,-1643523318558⟩,⟨1109263505382,1109375886856⟩,⟨-476948723543,-476810237765⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360456406237,360456641039⟩,⟨84307890422,84311429292⟩,⟨-86657314656,-86653678674⟩,⟨-1693400851002,-1693305840241⟩,⟨1140543473822,1140660521620⟩,⟨-486359452769,-486215532011⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720912812474,720913282078⟩,⟨168615780844,168622858584⟩,⟨-173314629312,-173307357348⟩,⟨-3386801702004,-3386611680482⟩,⟨2281086947644,2281321043240⟩,⟨-972718905538,-972431064022⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524275640552,1524275724830⟩,⟨-859671314,-858637692⟩,⟨882528624,883590710⟩,⟨30177529719,30209314762⟩,⟨-24938172158,-24903027646⟩,⟨18602678102,18642957405⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨999416296523,999417002804⟩,⟨233191875744,233202378766⟩,⟨-239691013145,-239680221834⟩,⟨-4675670581332,-4675385709598⟩,⟨3146237418346,3146585515664⟩,⟨-1336581757822,-1336155878380⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67729050315,67729053142⟩,⟨14634920728,14634984784⟩,⟨-15042189430,-15042123610⟩,⟨-294117276684,-294115301738⟩,⟨198170309940,198172491772⟩,⟨-84597983108,-84595484817⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50657696248,50657699087⟩,⟨263325893354,263325957649⟩,⟨35986507435,35986559756⟩,⟨-1272092415488,-1272090406806⟩,⟨-205493335284,-205491394586⟩,⟨-169498942131,-169496976834⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135240772951,2135240944371⟩,⟨-331085863358,-331084400988⟩,⟨340296512548,340298015192⟩,⟨6750951789874,6750996964957⟩,⟨-4583152030718,-4583102256106⟩,⟨2016489959950,2016546797215⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2975571342841,2975571701165⟩,⟨-692078611733,-692075527117⟩,⟨711331876690,711335046266⟩,⟨14165370066504,14165465535605⟩,⟨-9635447826303,-9635342911507⟩,⟨4271811685561,4271931161698⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137093219791,137093243984⟩,⟨680743934966,680744338688⟩,⟨130162201815,130162503007⟩,⟨-3121478316763,-3121466472618⟩,⟨-852344961660,-852333849452⟩,⟨-215331435402,-215320270724⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8818274223314,8818275779486⟩,⟨-43787660126641,-43787618703431⟩,⟨-8372469837778,-8372447509148⟩,⟨635642257196302,635643835931266⟩,⟨137972512648662,137973532504512⟩,⟨29748406845642,29749211875372⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8015492281618,8015499360621⟩,⟨-37931187886543,-37931037540832⟩,⟨-9532641494949,-9532528933470⟩,⟨521701717803964,521706706595645⟩,⟨158414794188527,158419129586563⟩,⟨19970790351542,19975132803215⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16030984563236,16030998721242⟩,⟨-75862375773086,-75862075081664⟩,⟨-19065282989898,-19065057866940⟩,⟨1043403435607928,1043413413191290⟩,⟨316829588377054,316838259173126⟩,⟨39941580703084,39950265606430⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10805181447606,10805181447704⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230896,2087019636287702⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9705669819830,9705669819928⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230908,2087019636287687⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2394564936256,2394564994112⟩,⟨-12029251796733,-12029251796224⟩,⟨0,0⟩,⟨104822536628670,104822536664337⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7435043122309,7435043122447⟩,⟨-44453677083443,-44453677081744⟩,⟨-20022321089744,-20022321088953⟩,⟨531571740359823,531571740390536⟩,⟨289701260272261,289701260288263⟩,⟨107838874689580,107838874696082⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6335531494533,6335531494671⟩,⟨-44453677083443,-44453677081744⟩,⟨-20022321089745,-20022321088952⟩,⟨531571740359829,531571740390537⟩,⟨289701260272264,289701260288265⟩,⟨107838874689580,107838874696084⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1925583069696,1925583108352⟩,⟨-7714796287081,-7714796286583⟩,⟨-3474811051333,-3474811051103⟩,⟨38121228945740,38121228960934⟩,⟨25895503160494,25895503167979⟩,⟨7733575958145,7733575961312⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100498837339,100498837341⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138552933044,138552933048⟩,⟨684633512850,684633512858⟩,⟨308364862535,308364862541⟩,⟨-1719138590394,-1719138590390⟩,⟨-1548629814810,-1548629814800⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4320148005952,4320148102464⟩,⟨-19744048083814,-19744048082807⟩,⟨-3474811051333,-3474811051103⟩,⟨142943765574410,142943765625271⟩,⟨25895503160494,25895503167979⟩,⟨7733575958145,7733575961312⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨747762789852,747763966920⟩,⟨-5540570340528,-5540550318546⟩,⟨5694710911976,5694731483486⟩,⟨70771356224200,70771900397656⟩,⟨-33319760341618,-33319094414218⟩,⟨-10838947261550,-10838133610660⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5067910795804,5067912069384⟩,⟨-25284618424342,-25284598401353⟩,⟨2219899860643,2219920432383⟩,⟨213715121798610,213715666022927⟩,⟨-7424257181124,-7423591246239⟩,⟨-3105371303405,-3104557649348⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463223061811,463223178231⟩,⟨1725417736943,1725420581551⟩,⟨202905862355,202907742682⟩,⟨-30879193652192,-30879109464731⟩,⟨1089514985346,1089592238987⟩,⟨-283840750403,-283766379844⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37255798059,37255800189⟩,⟨-756371293920,-756371283170⟩,⟨321668947845,321668966201⟩,⟨9399021074746,9399021103569⟩,⟨-6530558220472,-6530558128119⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨500478859870,500478978420⟩,⟨969046443023,969049298381⟩,⟨524574810200,524576708883⟩,⟨-21480172577446,-21480088361162⟩,⟨-5441043235126,-5440965889132⟩,⟨-283840750403,-283766379844⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504862395711,504862407910⟩,⟨2536208829314,2536208952001⟩,⟨0,0⟩,⟨3381169318170,3381172243620⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229804714942,229804774930⟩,⟨1599395556756,1599397207903⟩,⟨240868844600,240869722239⟩,⟨-3853455923280,-3853401930229⟩,⟨-1288341922158,-1288301908687⟩,⟨-130331067987,-130296916131⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-747763966920,-747762789852⟩,⟨5540550318546,5540570340528⟩,⟨-5694731483486,-5694710911976⟩,⟨-70771900397656,-70771356224200⟩,⟨33319094414218,33319760341618⟩,⟨10838133610660,10838947261550⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3572384039032,3572385312612⟩,⟨-14203497765268,-14203477742279⟩,⟨-9169542534819,-9169521963079⟩,⟨72171865176754,72172409401071⟩,⟨59214597574712,59215263509597⟩,⟨18571709568805,18572523222862⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450167396199,450167556701⟩,⟨434590728193,434594044454⟩,⟨-153585733451,-153582783903⟩,⟨-14179188826334,-14179093319670⟩,⟨-7262844505938,-7262740370196⟩,⟨-3936168530702,-3936054056492⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨325196720370,325196720376⟩,⟨1944331694898,1944331694900⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-325196720376,-325196720370⟩,⟨-1944331694900,-1944331694898⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨774314907400,774314907406⟩,⟨-1944331694900,-1944331694898⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1356063581900,1356063609134⟩,⟨-8838154864335,-8838154795579⟩,⟨-3980781481867,-3980781450891⟩,⟨54131380002639,54131380015338⟩,⟨34377123123190,34377123206742⟩,⟨10981522646247,10981522648901⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1356063609134,-1356063581900⟩,⟨8838154795579,8838154864335⟩,⟨3980781450891,3980781481867⟩,⟨-54131380015338,-54131380002639⟩,⟨-34377123206742,-34377123123190⟩,⟨-10981522648901,-10981522646247⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-256551981358,-256551954124⟩,⟨8838154795579,8838154864335⟩,⟨3980781450891,3980781481867⟩,⟨-54131380015338,-54131380002639⟩,⟨-34377123206742,-34377123123190⟩,⟨-10981522648901,-10981522646247⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11833340744,-11833339485⟩,⟨437369704212,437369710571⟩,⟨81441869522,81441881813⟩,⟨-4544060427565,-4544060410838⟩,⟨1729593889053,1729593951250⟩,⟨2664112604447,2664112629291⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438334055455,438334217216⟩,⟨871960432405,871963755025⟩,⟨-72143863929,-72140902090⟩,⟨-18723249253899,-18723153730508⟩,⟨-5533250616885,-5533146418946⟩,⟨-1272055926255,-1271941427201⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100498837341,-100498837339⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4635462100,4635462102⟩,⟨28753469921,28753469926⟩,⟨40022876823,40022876824⟩,⟨-304286772762,-304286772751⟩,⟨248259301866,248259301870⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10095313889,10095314139⟩,⟨11906113331,11906114881⟩,⟨87163587057,87163589166⟩,⟨-849921905683,-849921889168⟩,⟨102798145600,102798158703⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1470040740308,1470040761324⟩,⟨-7323833633928,-7323833259344⟩,⟨-1370782758782,-1370782691831⟩,⟨106671886723360,106671894110331⟩,⟨22592733838141,22592735334172⟩,⟨5030099208687,5030099492843⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13497376769,13497377298⟩,⟨-51326359955,-51326352549⟩,⟨103951189410,103951194824⟩,⟨-315531428826,-315531269658⟩,⟨-250560443625,-250560358865⟩,⟨-171152587465,-171152567836⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13497377298,-13497376769⟩,⟨51326352549,51326359955⟩,⟨-103951194824,-103951189410⟩,⟨315531269658,315531428826⟩,⟨250560358865,250560443625⟩,⟨171152567836,171152587465⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113996214639,-113996214108⟩,⟨-824417479107,-824417471699⟩,⟨-103951194824,-103951189410⟩,⟨2514554525210,2514554684378⟩,⟨250560358865,250560443625⟩,⟨171152567836,171152587465⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨88816622933,88816624724⟩,⟨-578863025699,-578863021167⟩,⟨606574371292,606574386713⟩,⟨3545384177260,3545384178231⟩,⟨-3401068724386,-3401068685053⟩,⟨-2410925116568,-2410925116202⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨118747315471,118747319564⟩,⟨-1365543017899,-1365542958585⟩,⟨700257023673,700257063528⟩,⟨21068525179843,21068526474166⟩,⟨-6040912757378,-6040912131864⟩,⟨-4329526920240,-4329526730196⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-118747319564,-118747315471⟩,⟨1365542958585,1365543017899⟩,⟨-700257063528,-700257023673⟩,⟨-21068526474166,-21068525179843⟩,⟨6040912131864,6040912757378⟩,⟨4329526730196,4329526920240⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨980764308212,980764312305⟩,⟨1365542958585,1365543017899⟩,⟨-700257063528,-700257023673⟩,⟨-21068526474166,-21068525179843⟩,⟨6040912131864,6040912757378⟩,⟨4329526730196,4329526920240⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123589208240,123589208760⟩,⟨782769435062,782769445098⟩,⟨186819835145,186819841325⟩,⟨-2487816318530,-2487816075060⟩,⟨-673197744441,-673197618354⟩,⟨-158297785383,-158297737753⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11819008096,11819008207⟩,⟨170949480194,170949482528⟩,⟨21555100910,21555102136⟩,⟨714889123847,714889181500⟩,⟨103930205370,103930232712⟩,⟨-15834115981,-15834109694⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172322267044,172322420852⟩,⟨1676990392496,1676995867669⟩,⟨109336500664,109339217942⟩,⟨-1950773004726,-1950561777483⟩,⟨469566174232,469702169827⟩,⟨-549039279164,-548936753471⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172322420852,-172322267044⟩,⟨-1676995867669,-1676990392496⟩,⟨-109339217942,-109336500664⟩,⟨1950561777483,1950773004726⟩,⟨-469702169827,-469566174232⟩,⟨548936753471,549039279164⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57482294090,57482507886⟩,⟨-77600310913,-77593184593⟩,⟨131529626658,131533221575⟩,⟨-1902894145797,-1902628925503⟩,⟨-1758044091985,-1757868082919⟩,⟨418605685484,418742363033⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28075185096463,28075210455096⟩,⟨-245340924048783,-245340295430633⟩,⟨-84052297462928,-84051857785878⟩,⟨3447714092085346,3447736313392540⟩,⟨1305944822224268,1305962882046994⟩,⟨303209722837265,303226456737791⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13891888005,13891888123⟩,⟨175972408602,175972411602⟩,⟨41998492650,41998494218⟩,⟨555266047957,555266133626⟩,⟨114663417188,114663458382⟩,⟨27899209744,27899224803⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354718692578,354719015988⟩,⟨1393536217157,1393548320977⟩,⟨10432215353,10438788191⟩,⟨-20792879717531,-20792381041899⟩,⟨-3395688502631,-3395361528121⟩,⟨-1877841776809,-1877595461395⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354719015988,-354718692578⟩,⟨-1393548320977,-1393536217157⟩,⟨-10438788191,-10432215353⟩,⟨20792381041899,20792879717531⟩,⟨3395361528121,3395688502631⟩,⟨1877595461395,1877841776809⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83615039467,83615524638⟩,⟨-521587888572,-521572462132⟩,⟨-82582652120,-82573117443⟩,⟨2069131788000,2069725987023⟩,⟨-2137889088764,-2137457916315⟩,⟨605539535140,605900349608⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239051770383,239051770389⟩,⟨1560377344504,1560377344514⟩,⟨308364862535,308364862541⟩,⟨-3918161845946,-3918161845942⟩,⟨-1548629814810,-1548629814800⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1662077166752,-1662075691122⟩,⟨-4154795714975,-4154753779234⟩,⟨461025544869,461050312069⟩,⟨42245706611556,42247228221646⟩,⟨-7728988942397,-7727887619912⟩,⟨1958356736265,1959302442687⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-186823674028,-186823507375⟩,⟨-1650288264957,-1650282483548⟩,⟨-230585292679,-230582248464⟩,⟨2593476693971,2593711241511⟩,⟨-228861428716,-228711752908⟩,⟨616084446796,616199454758⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52228096355,52228263014⟩,⟨-89910920453,-89905139034⟩,⟨77779569856,77782614077⟩,⟨-1324685151975,-1324450604431⟩,⟨-1777491243526,-1777341567708⟩,⟨267326307587,267441315551⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4371381045,4371422669⟩,⟨-33169972656,-33168488561⟩,⟨5685066727,5685912683⟩,⟨37078176575,37139591149⟩,⟨-302034122496,-301992245492⟩,⟨43732878107,43765259198⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2480896045,2480911879⟩,⟨-8541776336,-8541199830⟩,⟨7389242216,7389555006⟩,⟨-111145837772,-111121262612⟩,⟨-181587504996,-181571430758⟩,⟨36400898601,36412767117⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4344812097,4344839916⟩,⟨-32366760917,-32365639873⟩,⟨5100355059,5100953154⟩,⟨11224521409,11276203192⟩,⟨-284442318753,-284409771832⟩,⟨34492165720,34515040840⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4344839916,-4344812097⟩,⟨32365639873,32366760917⟩,⟨-5100953154,-5100355059⟩,⟨-11276203192,-11224521409⟩,⟨284409771832,284442318753⟩,⟨-34515040840,-34492165720⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨26541129,26610572⟩,⟨-804332783,-801727644⟩,⟨584113573,585557624⟩,⟨25801973383,25915069740⟩,⟨-17624350664,-17549926739⟩,⟨9217837267,9273093478⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57482294090,57482507886⟩,⟨-77600310913,-77593184593⟩,⟨131529626658,131533221575⟩,⟨-1902894145797,-1902628925503⟩,⟨-1758044091985,-1757868082919⟩,⟨418605685484,418742363033⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨26541129,26610572⟩,⟨-804332783,-801727644⟩,⟨584113573,585557624⟩,⟨25801973383,25915069740⟩,⟨-17624350664,-17549926739⟩,⟨9217837267,9273093478⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111669149696,112098646426⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨125413045043,129278515610⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112098646426,-111669149696⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437657167462,438086664192⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49920270663,51509408564⟩,⟨-129278515610,-125413045043⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨161589420359,163608054990⟩,⟨970233112166,974098582733⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49490773933,51938905294⟩,⟨-129278515610,-125413045043⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2108382532672,-2094732075648⟩,⟨6520354933288,6628111642060⟩,⟨2941231375395,2980896770238⟩,⟨-39955797492080,-38667193126509⟩,⟨-25451004958370,-24831331750826⟩,⟨-8081538503406,-7867894968156⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313728710667,-307851716489⟩,⟨-909633002021,-862170024352⟩,⟨-407801414884,-390242152311⟩,⟨5561958646874,6061472039830⟩,⟨3498419571195,3740829237760⟩,⟨1138957658751,1219099119589⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307851716489,313728710667⟩,⟨862170024352,909633002021⟩,⟨390242152311,407801414884⟩,⟨-6061472039830,-5561958646874⟩,⟨-3740829237760,-3498419571195⟩,⟨-1219099119589,-1138957658751⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-163608054990,-161589420359⟩,⟨-974098582733,-970233112166⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨935903572786,937922207417⟩,⟨-974098582733,-970233112166⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-177141147200,-174772182912⟩,⟨-1144383619701,-1137389199278⟩,⟨-514669881876,-513058695911⟩,⟨-1191086875261,-1176571632308⟩,⟨753266402528,760987201736⟩,⟨-240911583488,-239405585898⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151107647804,-148765966888⟩,⟨-821976802196,-811208951582⟩,⟨-369464044686,-366135547923⟩,⟨991275095519,1026207728312⟩,⟨1369507150953,1386307443470⟩,⟨202936741525,206345685216⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨148765966888,151107647804⟩,⟨811208951582,821976802196⟩,⟨366135547923,369464044686⟩,⟨-1026207728312,-991275095519⟩,⟨-1386307443470,-1369507150953⟩,⟨-206345685216,-202936741525⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨456617683377,464836358471⟩,⟨1673378975934,1731609804217⟩,⟨756377700234,777265459570⟩,⟨-7087679768142,-6553233742393⟩,⟨-5127136681230,-4867926722148⟩,⟨-1425444804805,-1341894400276⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨817335479527,827440715681⟩,⟨4060889506214,4133217208251⟩,⟨756377700234,777265459570⟩,⟨-19221840017109,-18477337896538⟩,⟨-5127136681230,-4867926722148⟩,⟨-1425444804805,-1341894400276⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98981547866,103877810588⟩,⟨-258557031220,-250826090086⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11637960145400,12213648358493⟩,⟨28101324270540,31904175354100⟩,⟨-108113816814224,-98065922711302⟩,⟨135708391486493,166678518186968⟩,⟨-318456440025379,-202240624490865⟩,⟨1652682270272317,1914022254949149⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8651220683674,9191417065111⟩,⟨63872611987059,69922384917899⟩,⟨-73355368321767,-64264450848085⟩,⟨94935998405323,169722482970904⟩,⟨-683692216843396,-541502265985289⟩,⟨1059852095981583,1291276272905942⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨90719764480,96323864832⟩,⟨-770413998139,-623858996205⟩,⟨627686179577,808239059067⟩,⟨6653154975735,11345970786625⟩,⟨-7586831464031,-1042456197661⟩,⟨-5599376682268,3156149898439⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1190231392256,1195835492608⟩,⟨-770413998139,-623858996205⟩,⟨627686179577,808239059067⟩,⟨6653154975735,11345970786625⟩,⟨-7586831464031,-1042456197661⟩,⟨-5599376682268,3156149898439⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨87171072960,92335877824⟩,⟨-711692831047,-573607510949⟩,⟨577126416890,746634855415⟩,⟨5656582001368,10181930750173⟩,⟨-6707478273356,-475204496625⟩,⟨-5679600846898,2612657426232⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨94363483670,100425058866⟩,⟨-838740015758,-670395933811⟩,⟨674508607005,879919683153⟩,⟨7301700443979,13024101086113⟩,⟨-8978543716268,-1251979801176⟩,⟨-5988461531426,4204278646053⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-96323864832,-90719764480⟩,⟨623858996205,770413998139⟩,⟨-808239059067,-627686179577⟩,⟨-11345970786625,-6653154975735⟩,⟨1042456197661,7586831464031⟩,⟨-3156149898439,5599376682268⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1003187762944,1008791863296⟩,⟨623858996205,770413998139⟩,⟨-808239059067,-627686179577⟩,⟨-11345970786625,-6653154975735⟩,⟨1042456197661,7586831464031⟩,⟨-3156149898439,5599376682268⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-100806979456,-94681878144⟩,⟨679962086706,844387442157⟩,⟨-885844381574,-684133445311⟩,⟨-13083846512519,-7671970803564⟩,⟨1559286481649,8995600482543⟩,⟨-4172895340647,5711337816390⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-92489481757,-86387173293⟩,⟨549759112405,720995594439⟩,⟨-758702388259,-550097104072⟩,⟨-10659772455273,-4776319086178⟩,⟨-514303128233,7387262715066⟩,⟨-3560850836030,6831815985215⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1874001913,14037885573⟩,⟨-288980903353,50599660628⟩,⟨-84193781254,329822579081⟩,⟨-3358072011294,8247781999935⟩,⟨-9492846844501,6135282913890⟩,⟨-9549312367456,11036094631268⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨937000956,7018942787⟩,⟨-144490451677,25299830314⟩,⟨-42096890627,164911289541⟩,⟨-1679036005647,4123890999968⟩,⟨-4746423422251,3067641456945⟩,⟨-4774656183728,5518047315634⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7018942787,-937000956⟩,⟨-25299830314,144490451677⟩,⟨-164911289541,42096890627⟩,⟨-4123890999968,1679036005647⟩,⟨-3067641456945,4746423422251⟩,⟨-5518047315634,4774656183728⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755104440829,761186401924⟩,⟨-25299830314,144490451677⟩,⟨-164911289541,42096890627⟩,⟨-4123890999968,1679036005647⟩,⟨-3067641456945,4746423422251⟩,⟨-5518047315634,4774656183728⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7485210214,8438552810⟩,⟨-134985846348,-102948144930⟩,⟨103579700186,141613254306⟩,⟨1805843020689,3067590087027⟩,⟨-2461950522764,-884318161578⟩,⟨-264414962031,1741251131187⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8438552810,-7485210214⟩,⟨102948144930,134985846348⟩,⟨-141613254306,-103579700186⟩,⟨-3067590087027,-1805843020689⟩,⟨884318161578,2461950522764⟩,⟨-1741251131187,264414962031⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091073074966,1092026417562⟩,⟨102948144930,134985846348⟩,⟨-141613254306,-103579700186⟩,⟨-3067590087027,-1805843020689⟩,⟨884318161578,2461950522764⟩,⟨-1741251131187,264414962031⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8471101696,-7510805184⟩,⟨103653794988,136029850842⟩,⟨-142708516350,-104289679191⟩,⟨-3108144772605,-1827992741740⟩,⟨900211308541,2498647358461⟩,⟨-1773240791501,256568023233⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4235550848,-3755402592⟩,⟨51826897494,68014925421⟩,⟨-71354258175,-52144839595⟩,⟨-1554072386303,-913996370870⟩,⟨450105654270,1249323679231⟩,⟨-886620395751,128284011617⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3755402592,4235550848⟩,⟨-68014925421,-51826897494⟩,⟨52144839595,71354258175⟩,⟨913996370870,1554072386303⟩,⟨-1249323679231,-450105654270⟩,⟨-128284011617,886620395751⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765878786208,766358953728⟩,⟨-68014925421,-51826897494⟩,⟨52144839595,71354258175⟩,⟨913996370870,1554072386303⟩,⟨-1249323679231,-450105654270⟩,⟨-128284011617,886620395751⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272768268741,273006604391⟩,⟨25737036232,33746461587⟩,⟨-35403313577,-25894925046⟩,⟨-766897521757,-451460755172⟩,⟨221079540394,615487630691⟩,⟨-435312782797,66103740508⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531757572416,1532717907456⟩,⟨-136029850842,-103653794988⟩,⟨104289679190,142708516350⟩,⟨1827992741740,3108144772606⟩,⟨-2498647358462,-900211308540⟩,⟨-256568023234,1773240791502⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1198389740837,1205084296550⟩,⟨-925463652264,-741110478763⟩,⟨745656963976,970901195089⟩,⟨8820223347907,15050852977633⟩,⟨-10604957111591,-2160642350486⟩,⟨-5798360121978,5355794214568⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1297267853898,1310656965324⟩,⟨-1850927304528,-1482220957526⟩,⟨1491313927952,1941802390178⟩,⟨17640446695825,30101705955260⟩,⟨-21209914223180,-4321284700974⟩,⟨-11591990733967,10711588429135⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨181852951104,193142857216⟩,⟨-1568770926823,-1243436857125⟩,⟨1251064960419,1645792964367⟩,⟨12560286055428,24106783532167⟩,⟨-16561834812734,-1276931634983⟩,⟨-12288389992184,7655200046903⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨62303021904,66684529967⟩,⟨-535570176609,-415785343418⟩,⟨416624724386,563227801166⟩,⟨4005380847318,8037307091865⟩,⟨-5569163813586,-78340839027⟩,⟨-4602283774637,2665165470287⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380000402545,380570883321⟩,⟨2078970705,21327959786⟩,⟨-23479858522,-640629932⟩,⟨-623913548787,137952280955⟩,⟨-307535407317,643423525779⟩,⟨-679721025396,527528470441⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176611434550,3181380365700⟩,⟨-178558633226,-17353093478⟩,⟨5347314932,196574425688⟩,⟨-1154753074228,5243475752549⟩,⟨-5408836466672,2574641762352⟩,⟨-4416473945658,5714947113774⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨180000362695,192948259004⟩,⟨-1560474213736,-1202233421629⟩,⟨1203978187986,1641592772310⟩,⟨11515080366003,23747498788524⟩,⟨-16629349114386,-78782879656⟩,⟨-13580274826353,8259517948021⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨361853313799,386091116220⟩,⟨-3129245140559,-2445670278754⟩,⟨2455043148405,3287385736677⟩,⟨24075366421431,47854282320691⟩,⟨-33191183927120,-1355714514639⟩,⟨-25868664818537,15914717994924⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518578159753,526965539825⟩,⟨-35029892036,200060034376⟩,⟨-228334522258,58286933762⟩,⟨-5716547704838,2362752395978⟩,⟨-4290768756106,6582914585184⟩,⟨-7652861012235,6660409952628⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356140545906,364815608189⟩,⟨-36376528641,207750842132⟩,⟨-237112271997,60527629180⟩,⟨-5943211177234,2493018327635⟩,⟨-4500725921214,6847467792785⟩,⟨-7960169448426,6967823211692⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712281091812,729631216378⟩,⟨-72753057282,415501684264⟩,⟨-474224543994,121055258360⟩,⟨-11886422354468,4986036655270⟩,⟨-9001451842428,13694935585570⟩,⟨-15920338896852,13935646423384⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523319019606,1525232697242⟩,⟨-33081705912,31332051360⟩,⟨-37323575116,39128816164⟩,⟨-1239597345287,1302301751917⟩,⟨-1614329196884,1561739214224⟩,⟨-1997819154421,2037655753533⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨986830249951,1012137898350⟩,⟨-122875269077,597172035983⟩,⟨-682607811401,193892486967⟩,⟨-17336333217986,7804467884700⟩,⟨-13585613564257,20062910580415⟩,⟨-23444048880631,20715779409275⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67668705407,67787010304⟩,⟨12769754566,16758361906⟩,⟨-17581148176,-12848093090⟩,⟨-379633444569,-221926429590⟩,⟨107518184314,304436488434⟩,⟨-214954920989,35106772605⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50302363690,51013314369⟩,⟨259417273952,267432359083⟩,⟨33320013193,38369125278⟩,⟨-1376431202285,-1176153073129⟩,⟨-293478285039,-106094506889⟩,⟨-274503266854,-73843244551⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133930375433,2136606948476⟩,⟨-379250902068,-288805468484⟩,⟨290577201346,397871005692⟩,⟨5112789647131,8699159065619⟩,⟨-7001534266104,-2527877786008⟩,⟨-695527099209,4980836158222⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2972832600406,2978427556740⟩,⟨-793012962758,-603513349195⟩,⟨607215718264,831947566369⟩,⟨10724975310472,18260306646864⟩,⟨-14714031680638,-5323566306991⟩,⟨-1413012300930,10492380653977⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136006298503,138188135022⟩,⟨664613171051,696827337265⟩,⟨117869792451,142536066777⟩,⟨-3623666697456,-2617626715707⟩,⟨-1362077730490,-346343358391⟩,⟨-772348051798,345216639160⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8748405349143,8888748777970⟩,⟨-45541443379804,-42075286853009⟩,⟨-9315504526821,-7462093056082⟩,⟨570437101461092,703488804805538⟩,⟨93703867879009,184475009377982⟩,⟨-9831953893474,70002629708881⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7851841507879,8182395965465⟩,⟨-42915806432677,-32935580417717⟩,⟨-14093624962035,-5129875307015⟩,⟨322355957706235,720857741726252⟩,⟨-38819414047170,361323973550467⟩,⟨-201864137733455,243478412572321⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15703683015758,16364791930930⟩,⟨-85831612865354,-65871160835434⟩,⟨-28187249924070,-10259750614030⟩,⟨644711915412470,1441715483452504⟩,⟨-77638828094340,722647947100934⟩,⟨-403728275466910,486956825144642⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10784481866270,10825960642718⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533866,2099083303790624⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9684970238494,9726449014942⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533869,2099083303790615⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2392217469760,2396916459264⟩,⟨-12101371604921,-11957606413725⟩,⟨0,0⟩,⟨101381360168522,108260423343400⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7389158313070,7481466403734⟩,⟨-45100018333202,-43819395486456⟩,⟨-20283077028156,-19766252324336⟩,⟨519718035382228,543746785426976⟩,⟨284094878485878,295448751352899⟩,⟨105750807979921,109979298583699⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6289646685294,6381954775958⟩,⟨-45100018333203,-43819395486456⟩,⟨-20283077028156,-19766252324336⟩,⟨519718035382231,543746785426971⟩,⟨284094878485878,295448751352898⟩,⟨105750807979920,109979298583699⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1917590928512,1933610349440⟩,⟨-7884066792864,-7549400857700⟩,⟨-3545744324833,-3405418093843⟩,⟨33006505923972,43218730283247⟩,⟨23520312649986,28266187135561⟩,⟨6784777970515,8678510510757⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100284130918,100713627649⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨137544808092,139563442724⟩,⟨680915274298,688350416341⟩,⟨307345908037,309383215712⟩,⟨-1725980926281,-1712309844048⟩,⟨-1552567595174,-1544692034432⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4309808398272,4330526808704⟩,⟨-19985438397785,-19507007271425⟩,⟨-3545744324833,-3405418093843⟩,⟨134387866092494,151479153626647⟩,⟨23520312649986,28266187135561⟩,⟨6784777970515,8678510510757⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨723706627598,772182232440⟩,⟨-6258490281118,-4891340557508⟩,⟨4910086296810,6574771473354⟩,⟨48150732842862,95708564641382⟩,⟨-66382367854240,-2711429029278⟩,⟨-51737329637074,31829435989848⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5033515025870,5102709041144⟩,⟨-26243928678903,-24398347828933⟩,⟨1364341971977,3169353379511⟩,⟨182538598935356,247187718268029⟩,⟨-42862055204254,25554758106283⟩,⟨-44952551666559,40507946500605⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459096263359,467400548925⟩,⟨1603245069586,1840899546092⟩,⟨124438746692,290308049582⟩,⟨-35382719739122,-26271747618247⟩,⟨-2839956307347,4866356259234⟩,⟨-4117586786759,3710467572717⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36230633056,38288000699⟩,⟨-777283397560,-735648287558⟩,⟨320394994437,322946015318⟩,⟨9048824618704,9756800690983⟩,⟨-6562818552468,-6498504886492⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨495326896415,505688549624⟩,⟨825961672026,1105251258534⟩,⟨444833741129,613254064900⟩,⟨-26333895120418,-16514946927264⟩,⟨-9402774859815,-1632148627258⟩,⟨-4117586786759,3710467572717⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504367106722,505357825907⟩,⟨2516159178967,2556424289217⟩,⟨0,0⟩,⟨2234856254543,4531068346710⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227215963265,232424705268⟩,⟨1512407121286,1683749236810⟩,⟨204053782895,281863995921⟩,⟨-7316478775589,-352251202337⟩,⟨-3303733464958,677151098081⟩,⟨-1892526330758,1705406089647⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-772182232440,-723706627598⟩,⟨4891340557508,6258490281118⟩,⟨-6574771473354,-4910086296810⟩,⟨-95708564641382,-48150732842862⟩,⟨2711429029278,66382367854240⟩,⟨-31829435989848,51737329637074⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3537626165832,3606820181106⟩,⟨-15094097840277,-13248516990307⟩,⟨-10120515798187,-8315504390653⟩,⟨38679301451112,103328420783785⟩,⟨26231741679264,94648554989801⟩,⟨-25044658019333,60415840147831⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442543852914,457821662860⟩,⟨274885161769,600713471064⟩,⟨-295748669219,-25342914772⟩,⟨-19722595249899,-8802887472019⟩,⟨-12394697524522,-1809072467536⟩,⟨-10019626811192,1898846778688⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨323178840718,327216109980⟩,⟨1940466224332,1948197165466⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-327216109980,-323178840718⟩,⟨-1948197165466,-1940466224332⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨772295517796,776332787058⟩,⟨-1948197165466,-1940466224332⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1346913340108,1365265335758⟩,⟨-8992823266955,-8686937574847⟩,⟨-4044391416355,-3918543332786⟩,⟨49830752086390,58454634645665⟩,⟨32375880132205,36390374634958⟩,⟨10187683222984,11778670764856⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1365265335758,-1346913340108⟩,⟨8686937574847,8992823266955⟩,⟨3918543332786,4044391416355⟩,⟨-58454634645665,-49830752086390⟩,⟨-36390374634958,-32375880132205⟩,⟨-11778670764856,-10187683222984⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-265753707982,-247401712332⟩,⟨8686937574847,8992823266955⟩,⟨3918543332786,4044391416355⟩,⟨-58454634645665,-49830752086390⟩,⟨-36390374634958,-32375880132205⟩,⟨-11778670764856,-10187683222984⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12553715961,-11135946093⟩,⟨419232188304,456051239667⟩,⟨70493649038,92572127053⟩,⟨-4876007932624,-4224669349367⟩,⟨1510663798158,1944582820887⟩,⟨2563125131803,2764310521585⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429990136953,446685716767⟩,⟨694117350073,1056764710731⟩,⟨-225255020181,67229212281⟩,⟨-24598603182523,-13027556821386⟩,⟨-10884033726364,135510353351⟩,⟨-7456501679389,4663157300273⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100713627649,-100284130918⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4513948854,4757526375⟩,⟨27557576309,29950156475⟩,⟨39917784923,40128086017⟩,⟨-309915444842,-298662630520⟩,⟨247702508009,248816179610⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9821039662,10371325765⟩,⟨7595300199,16199918942⟩,⟨86849488477,87478538129⟩,⟨-918668867993,-780764317193⟩,⟨97273538155,108293929972⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1461042219344,1479106009585⟩,⟨-7479751662300,-7170460558958⟩,⟨-1406592569503,-1335563663799⟩,⟨103008064783118,110434476312001⟩,⟨21704756674131,23504527069886⟩,⟨4811154977436,5254850333346⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13050297260,13951912721⟩,⟨-60461285896,-42255105729⟩,⟨102138564794,105750048300⟩,⟨-536151760570,-94861481809⟩,⟨-292693952704,-208222926478⟩,⟨-180846454527,-161422828936⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13951912721,-13050297260⟩,⟨42255105729,60461285896⟩,⟨-105750048300,-102138564794⟩,⟨94861481809,536151760570⟩,⟨208222926478,292693952704⟩,⟨161422828936,180846454527⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114665540370,-113334428178⟩,⟨-833918222655,-814853049028⟩,⟨-105750048300,-102138564794⟩,⟨2293884737361,2735175016122⟩,⟨208222926478,292693952704⟩,⟨161422828936,180846454527⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨86313829468,91340193481⟩,⟨-599779081523,-558535801855⟩,⟨595796641790,617139567843⟩,⟨3207882603083,3895560842478⟩,⟨-3627800884136,-3170461731250⟩,⟨-2520121319289,-2301075199682⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨114694693334,122874397762⟩,⟨-1428214825800,-1305083330787⟩,⟨674850171299,725355884451⟩,⟨19633980929261,22574978220469⟩,⟨-6696220234195,-5378535129810⟩,⟨-4591479627314,-4068567852332⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-122874397762,-114694693334⟩,⟨1305083330787,1428214825800⟩,⟨-725355884451,-674850171299⟩,⟨-22574978220469,-19633980929261⟩,⟨5378535129810,6696220234195⟩,⟨4068567852332,4591479627314⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨976637230014,984816934442⟩,⟨1305083330787,1428214825800⟩,⟨-725355884451,-674850171299⟩,⟨-22574978220469,-19633980929261⟩,⟨5378535129810,6696220234195⟩,⟨4068567852332,4591479627314⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122173678735,125004991627⟩,⟨768081593960,797832149039⟩,⟨180927865446,192688906067⟩,⟨-2794981425055,-2188820091837⟩,⟨-807078578002,-538153739922⟩,⟨-211926258366,-103953737387⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11682179875,11958205640⟩,⟨167985316438,173934829264⟩,⟨21056286342,22056858930⟩,⟨637292342215,792067088809⟩,⟨90341947170,117485007684⟩,⟨-18743903665,-12936091109⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166849758616,177982244319⟩,⟨1465738099420,1888919124207⟩,⟨-5827755391,219278858726⟩,⟨-11203825456014,7341048090019⟩,⟨-5734946217025,6779101554282⟩,⟨-5800802877792,4718386740198⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-177982244319,-166849758616⟩,⟨-1888919124207,-1465738099420⟩,⟨-219278858726,5827755391⟩,⟨-7341048090019,11203825456014⟩,⟨-6779101554282,5734946217025⟩,⟨-4718386740198,5800802877792⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49233718946,65574946652⟩,⟨-376512002921,218011137390⟩,⟨-15225075831,287691751312⟩,⟨-14657526865608,10851574253677⟩,⟨-10082835019240,6412097315106⟩,⟨-6610913070956,7506208967439⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27387832319841,28779260032096⟩,⟨-268288210991478,-222705547000073⟩,⟨-102344098460528,-66531002619827⟩,⟨2500376488754939,4409581238992694⟩,⟨473852292836517,2170469939289645⟩,⟨-549543700312322,1167333119620611⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13575488788,14211989703⟩,⟨170692790384,181413272204⟩,⟨40208074836,43814134352⟩,⟨437581011907,671425251008⟩,⟨69264410552,160044113532⟩,⟨11356046056,44435371833⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338153050129,371992925681⟩,⟨783981003401,1998708355776⟩,⟨-321325625894,325369442616⟩,⟨-46760629748057,5423846733817⟩,⟨-20001257292672,13771317574907⟩,⟨-14976947645808,11385760746745⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371992925681,-338153050129⟩,⟨-1998708355776,-783981003401⟩,⟨-325369442616,321325625894⟩,⟨-5423846733817,46760629748057⟩,⟨-13771317574907,20001257292672⟩,⟨-11385760746745,14976947645808⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57997211272,108532666638⟩,⟨-1304591005703,272783707330⟩,⟨-550624462797,388554838175⟩,⟨-30022449916340,33733072926671⟩,⟨-24655351301271,20136767646023⟩,⟨-18842262426134,19640104946081⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨237828939010,240277070373⟩,⟨1556229609222,1564523744725⟩,⟨307345908037,309383215712⟩,⟨-3925004181833,-3911333099600⟩,⟨-1552567595174,-1544692034432⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1706646535061,-1618689507158⟩,⟨-5621975883019,-2686889016626⟩,⟨-516406151315,1480797981348⟩,⟨-19956145188318,104451470049095⟩,⟨-58666751664007,42086805821752⟩,⟨-46571951451580,50217605849569⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-194030995614,-179862810745⟩,⟨-1877554060141,-1429318883581⟩,⟨-357799945510,-98006146880⟩,⟨-7205366134849,12459623127305⟩,⟨-7237604950942,6670010233673⟩,⟨-5322789593344,6557276082775⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43797943396,60414259628⟩,⟨-321324450919,135204861144⟩,⟨-50454037473,211377068832⟩,⟨-11130370316682,8548290027705⟩,⟨-8790172546116,5125318199241⟩,⟨-5671889903872,6208859947117⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2596987905,6472895462⟩,⟨-114971351014,37788692820⟩,⟨-34342145094,51571456175⟩,⟨-3754732248703,3976477358854⟩,⟨-2940128933661,2093823992547⟩,⟨-2064462578288,2115608143330⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1744647166,3319549039⟩,⟨-35311275138,14858054028⟩,⟨-5544540400,23228838684⟩,⟨-1302173968429,1127205934368⟩,⟨-1089524424892,615221345664⟩,⟨-642699625653,763582542400⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3042732331,5837786719⟩,⟨-85901586686,14150506314⟩,⟨-20455675319,35446891943⟩,⟨-2450720908969,2619196183044⟩,⟨-2093203541868,1320902479883⟩,⟨-1269309586823,1404804509710⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5837786719,-3042732331⟩,⟨-14150506314,85901586686⟩,⟨-35446891943,20455675319⟩,⟨-2619196183044,2450720908969⟩,⟨-1320902479883,2093203541868⟩,⟨-1404804509710,1269309586823⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3240798814,3430163131⟩,⟨-129121857328,123690279506⟩,⟨-69789037037,72027131494⟩,⟨-6373928431747,6427198267823⟩,⟨-4261031413544,4187027534415⟩,⟨-3469267087998,3384917730153⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49233718946,65574946652⟩,⟨-376512002921,218011137390⟩,⟨-15225075831,287691751312⟩,⟨-14657526865608,10851574253677⟩,⟨-10082835019240,6412097315106⟩,⟨-6610913070956,7506208967439⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3240798814,3430163131⟩,⟨-129121857328,123690279506⟩,⟨-69789037037,72027131494⟩,⟨-6373928431747,6427198267823⟩,⟨-4261031413544,4187027534415⟩,⟨-3469267087998,3384917730153⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (521/5120) u, BivariateJet2.affineZ (593/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000048

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000049Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2091178077632,-2091178038848⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2091178077632,-2091178038848⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-177763620224,-177763620160⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-177763620160,-177763620096⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨92041486784,92041486848⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-100456157952,-100456157888⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨92041609472,92041609536⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-100456304064,-100456304000⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8414694592,-8414694528⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8414671104,-8414671040⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨192497644672,192497644736⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨192497913472,192497913536⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1913414418688,1913414457280⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1913414418752,1913414457344⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2097962621952,-2097962583168⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2084430114368,-2084430075648⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-178952023936,-178952023872⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-176577386048,-176577385984⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨89471139136,89471139200⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-97401832192,-97401832128⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨94633625664,94633625728⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-103552265024,-103552264960⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8918639360,-8918639296⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7930693056,-7930692992⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨186872971328,186872971392⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨198185890688,198185890752⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1905478051776,1905478090368⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1921385197120,1921385235712⟩



end LaneCBRB2Cell000049Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000049
open Set LaneCBRB2Cell000049Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111883898060,111883898061⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨131211250892,131211250893⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111883898061,-111883898060⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437871915827,437871915828⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨52253855579,52253855581⟩,⟨-131211250893,-131211250892⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨164137753639,164137753642⟩,⟨968300376883,968300376884⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52253855578,52253855582⟩,⟨-131211250893,-131211250892⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2091178077632,-2091178038848⟩,⟨6486365872197,6486365872324⟩,⟨2933178091241,2933178091303⟩,⟨-38265118045861,-38265118044377⟩,⟨-24669054992650,-24669054991822⟩,⟨-7824868330586,-7824868330262⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312176118431,-312176112634⟩,⟨-873325004395,-873324970200⟩,⟨-394923416272,-394923400805⟩,⟨5712309319646,5712309320209⟩,⟨3574810944814,3574810983907⟩,⟨1168115259333,1168115259459⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨312176112634,312176118431⟩,⟨873324970200,873325004395⟩,⟨394923400805,394923416272⟩,⟨-5712309320209,-5712309319646⟩,⟨-3574810983907,-3574810944814⟩,⟨-1168115259459,-1168115259333⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164137753642,-164137753639⟩,⟨-968300376884,-968300376883⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨935373874134,935373874137⟩,⟨-968300376884,-968300376883⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-177763620224,-177763620096⟩,⟨-1138216015013,-1138216015007⟩,⟨-514708905437,-514708905433⟩,⟨-1178282852228,-1178282852213⟩,⟨759624586636,759624586649⟩,⟨-240948117914,-240948117909⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151226637290,-151226637180⟩,⟨-811750345050,-811750344927⟩,⟨-367078942906,-367078942847⟩,⟨1002385939766,1002385939797⟩,⟨1375033643205,1375033643357⟩,⟨204978800421,204978800431⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151226637180,151226637290⟩,⟨811750344927,811750345050⟩,⟨367078942847,367078942906⟩,⟨-1002385939797,-1002385939766⟩,⟨-1375033643357,-1375033643205⟩,⟨-204978800431,-204978800421⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨463402749814,463402755721⟩,⟨1685075315127,1685075349445⟩,⟨762002343652,762002359178⟩,⟨-6714695260006,-6714695259412⟩,⟨-4949844627264,-4949844588019⟩,⟨-1373094059890,-1373094059754⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨825063135173,825063147028⟩,⟨4079640251371,4079640343633⟩,⟨762002343652,762002359178⟩,⟨-18743947056731,-18743947055632⟩,⟨-4949844627264,-4949844588019⟩,⟨-1373094059890,-1373094059754⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨104507711156,104507711164⟩,⟨-262422501786,-262422501784⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11567814529183,11567814530069⟩,⟨29047185084339,29047185089011⟩,⟨-96934877899362,-96934877884290⟩,⟨145876986391040,145876986426785⟩,⟨-243406853832376,-243406853678403⟩,⟨1624571439443022,1624571439823746⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8680378707638,8680378833029⟩,⟨64718081709801,64718083000461⟩,⟨-64722092824244,-64722091603814⟩,⟨127816157642763,127816164178582⟩,⟨-574264345145450,-574264333385287⟩,⟨1070257982455891,1070258003018839⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨96003726336,96003859712⟩,⟨-707924545070,-707922535159⟩,⟨707966397620,707968406886⟩,⟨8984641022301,8984690274431⟩,⟨-4101834003304,-4101770934829⟩,⟨-1323056747719,-1322978295849⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1195515354112,1195515487488⟩,⟨-707924545070,-707922535159⟩,⟨707966397620,707968406886⟩,⟨8984641022301,8984690274431⟩,⟨-4101834003304,-4101770934829⟩,⟨-1323056747719,-1322978295849⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨92041486784,92041609536⟩,⟨-651075928232,-651074007085⟩,⟨651114347245,651116267803⟩,⟨7877609861398,7877658355511⟩,⟨-3386887253235,-3386826553562⟩,⟨-1602393493779,-1602318931445⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨100078078199,100078222835⟩,⟨-767185947818,-767183532658⟩,⟨767231066895,767233481370⟩,⟨10155948242991,10156011907197⟩,⟨-4864430543128,-4864353541548⟩,⟨-1014567127383,-1014474292270⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-96003859712,-96003726336⟩,⟨707922535159,707924545070⟩,⟨-707968406886,-707966397620⟩,⟨-8984690274431,-8984641022301⟩,⟨4101770934829,4101834003304⟩,⟨1322978295849,1323056747719⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1003507768064,1003507901440⟩,⟨707922535159,707924545070⟩,⟨-707968406886,-707966397620⟩,⟨-8984690274431,-8984641022301⟩,⟨4101770934829,4101834003304⟩,⟨1322978295849,1323056747719⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-100456304064,-100456157888⟩,⟨775648161668,775650466956⟩,⟨-775698524957,-775696220369⟩,⟨-10391422731859,-10391364206942⟩,⟨5041392962519,5041465914103⟩,⟨902294736646,902384138273⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-91684973884,-91684828285⟩,⟨643243285743,643245761587⟩,⟨-643285615944,-643283140786⟩,⟨-7664416148621,-7664349974594⟩,⟨3227569200235,3227648504727⟩,⟨1701559180153,1701654031601⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8393104315,8393394550⟩,⟨-123942662075,-123937771071⟩,⟨123945450951,123950340584⟩,⟨2491532094370,2491661932603⟩,⟨-1636861342893,-1636705036821⟩,⟨686992052770,687179739331⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4196552157,4196697275⟩,⟨-61971331038,-61968885535⟩,⟨61972725475,61975170292⟩,⟨1245766047185,1245830966302⟩,⟨-818430671447,-818352518410⟩,⟨343496026385,343589869666⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4196697275,-4196552157⟩,⟨61968885535,61971331038⟩,⟨-61975170292,-61972725475⟩,⟨-1245830966302,-1245766047185⟩,⟨818352518410,818430671447⟩,⟨-343589869666,-343496026385⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757926686341,757926850723⟩,⟨61968885535,61971331038⟩,⟨-61975170292,-61972725475⟩,⟨-1245830966302,-1245766047185⟩,⟨818352518410,818430671447⟩,⟨-343589869666,-343496026385⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8382553888,8382577180⟩,⟨-123624865796,-123624343054⟩,⟨123632002744,123632525384⟩,⟨2480580103505,2480596060515⟩,⟨-1627959333900,-1627942149444⟩,⟨680661952646,680681148671⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8382577180,-8382553888⟩,⟨123624343054,123624865796⟩,⟨-123632525384,-123632002744⟩,⟨-2480596060515,-2480580103505⟩,⟨1627942149444,1627959333900⟩,⟨-680681148671,-680661952646⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091129050596,1091129073888⟩,⟨123624343054,123624865796⟩,⟨-123632525384,-123632002744⟩,⟨-2480596060515,-2480580103505⟩,⟨1627942149444,1627959333900⟩,⟨-680681148671,-680661952646⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8414694592,-8414671040⟩,⟨124574081945,124574611364⟩,⟨-124582329796,-124581800481⟩,⟨-2513767487419,-2513751234488⟩,⟨1654563799190,1654581270646⟩,⟨-700026514194,-700007036101⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4207347296,-4207335520⟩,⟨62287040972,62287305682⟩,⟨-62291164898,-62290900240⟩,⟨-1256883743710,-1256875617244⟩,⟨827281899595,827290635323⟩,⟨-350013257097,-350003518050⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4207335520,4207347296⟩,⟨-62287305682,-62287040972⟩,⟨62290900240,62291164898⟩,⟨1256875617244,1256883743710⟩,⟨-827290635323,-827281899595⟩,⟨350003518050,350013257097⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766330719136,766330750176⟩,⟨-62287305682,-62287040972⟩,⟨62290900240,62291164898⟩,⟨1256875617244,1256883743710⟩,⟨-827290635323,-827281899595⟩,⟨350003518050,350013257097⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272782262649,272782268472⟩,⟨30906085763,30906216449⟩,⟨-30908131346,-30908000686⟩,⟨-620149015129,-620145025876⟩,⟨406985537361,406989833475⟩,⟨-170170287168,-170165488161⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532661438272,1532661500352⟩,⟨-124574611364,-124574081944⟩,⟨124581800480,124582329796⟩,⟨2513751234488,2513767487420⟩,⟨-1654581270646,-1654563799190⟩,⟨700007036100,700026514194⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1204699851271,1204700011388⟩,⟨-849855611136,-849852972351⟩,⟨849905628737,849908266763⟩,⟨11985013598215,11985082878738⟩,⟨-6123342052993,-6123257745151⟩,⟨-389112470106,-389010582275⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1309888074766,1309888395000⟩,⟨-1699711222273,-1699705944702⟩,⟨1699811257475,1699816533527⟩,⟨23970027196441,23970165757476⟩,⟨-12246684105987,-12246515490307⟩,⟨-778224794744,-778021310021⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨192497644672,192497913536⟩,⟨-1426726671351,-1426721892592⟩,⟨1426810291435,1426815068940⟩,⟨18268960763877,18269094391854⟩,⟨-8428364566029,-8428208117412⟩,⟨-2504787331471,-2504603968709⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨66178278010,66178384304⟩,⟨-482583142973,-482581430594⟩,⟨482611331094,482613042974⟩,⟨6004804676209,6004849165631⟩,⟨-2676262246955,-2676207860217⟩,⟨-1021834680550,-1021768792996⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380244141530,380244165050⟩,⟨12175242568,12175558489⟩,⟨-12176312833,-12175996973⟩,⟨-247811867936,-247802167165⟩,⟨163828443227,163838857465⟩,⟨-70545100694,-70533506045⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179340883391,3179341080050⟩,⟨-101803680975,-101801026865⟩,⟨101807334682,101809988283⟩,⟨2078470988102,2078552695164⟩,⟨-1376428299134,-1376340713432⟩,⟨596272847436,596370206400⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨191360691014,191361010211⟩,⟨-1401561907294,-1401556699883⟩,⟨1401643539640,1401648745584⟩,⟨17577917974535,17578055459594⟩,⟨-7910879387121,-7910713592634⟩,⟨-2829468867289,-2829269600385⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨383858335686,383858923747⟩,⟨-2828288578645,-2828278592475⟩,⟨2828453831075,2828463814524⟩,⟨35846878738412,35847149851448⟩,⟨-16339243953150,-16338921710046⟩,⟨-5334256198760,-5333873569094⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522461834287,522462060915⟩,⟨85434061602,85437451652⟩,⟨-85442744682,-85439355576⟩,⟨-1710593274854,-1710502849578⟩,⟨1121244220014,1121352762520⟩,⟨-466707877703,-466577845720⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360148775872,360149010205⟩,⟨88338431683,88341956140⟩,⟨-88347429111,-88343905629⟩,⟨-1761523418024,-1761428962401⟩,⟨1152137768153,1152250824704⟩,⟨-475350392586,-475215262883⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720297551744,720298020410⟩,⟨176676863366,176683912280⟩,⟨-176694858222,-176687811258⟩,⟨-3523046836048,-3522857924802⟩,⟨2304275536306,2304501649408⟩,⟨-950700785172,-950430525766⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524278861092,1524278946464⟩,⟨-950268310,-949216148⟩,⟨949275096,950327052⟩,⟨33155173973,33187383915⟩,⟨-26639121202,-26604465290⟩,⟨19325887429,19364561548⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨998565457684,998566163336⟩,⟨244308768460,244319243940⟩,⟨-244334379940,-244323907298⟩,⟨-4862668286661,-4862384655582⟩,⟨3177325028194,3177661738025⟩,⟨-1305623880064,-1305223445059⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67675648839,67675651729⟩,⟨15335230280,15335295454⟩,⟨-15336245602,-15336180442⟩,⟨-305973060679,-305971059994⟩,⟨200203762412,200205913100⟩,⟨-82698775176,-82696377469⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50783167358,50783170257⟩,⟨262611896882,262611962357⟩,⟨35393561086,35393613108⟩,⟨-1269501339230,-1269499299080⟩,⟨-200711021611,-200709101725⟩,⟨-167828382246,-167826487769⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136449515424,2136449688498⟩,⟨-347300939682,-347299449646⟩,⟨347320968114,347322457862⟩,⟨7036302639608,7036348474872⟩,⟨-4641029241686,-4640980106342⟩,⟨1979777909145,1979832530976⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2978098370572,2978098732456⟩,⟨-726178922315,-726175777352⟩,⟨726220770772,726223915134⟩,⟨14771377528409,14771474466331⟩,⟨-9763054187188,-9762950551957⟩,⟨4198590153339,4198705034964⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137549493921,137549518488⟩,⟨677761267386,677761678336⟩,⟨129407724252,129408023951⟩,⟨-3103168215333,-3103156166599⟩,⟨-844487625477,-844476617079⟩,⟨-213899245491,-213888470670⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8789022549141,8789024118904⟩,⟨-43307056739778,-43307015011535⟩,⟨-8268807185423,-8268785081810⟩,⟨625064669281871,625066256212128⟩,⟨135446846692765,135447851162521⟩,⟨29225546955309,29226320720160⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7982102328585,7982109394909⟩,⟨-37378164251157,-37378014474797⟩,⟨-9462757429795,-9462647986077⟩,⟨509561126809782,509566087120894⟩,⟨156195559774972,156199760458757⟩,⟨19780587225780,19784678818410⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15964204657170,15964218789818⟩,⟨-74756328502314,-74756028949594⟩,⟨-18925514859590,-18925295972154⟩,⟨1019122253619564,1019132174241788⟩,⟨312391119549944,312399520917514⟩,⟨39561174451560,39569357636820⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10805181447606,10805181447704⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230896,2087019636287702⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9705669819830,9705669819928⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230908,2087019636287687⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2394564936256,2394564994112⟩,⟨-12029251796733,-12029251796224⟩,⟨0,0⟩,⟨104822536628670,104822536664337⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7365312323278,7365312323413⟩,⟨-43450300375836,-43450300374197⟩,⟨-19648516847731,-19648516846965⟩,⟨512654051788453,512654051817709⟩,⟨281163705813335,281163705828664⟩,⟨104833087136120,104833087142365⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6265800695502,6265800695637⟩,⟨-43450300375837,-43450300374196⟩,⟨-19648516847732,-19648516846964⟩,⟨512654051788455,512654051817710⟩,⟨281163705813335,281163705828665⟩,⟨104833087136119,104833087142366⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1913414418688,1913414457344⟩,⟨-7624581887507,-7624581887020⟩,⟨-3447886996816,-3447886996591⟩,⟨37086835185007,37086835201189⟩,⟨25428679574989,25428679582931⟩,⟨7583920210852,7583920214243⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100498837339,100498837341⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139634873005,139634873009⟩,⟨679199935018,679199935026⟩,⟨307138759703,307138759708⟩,⟨-1705494687256,-1705494687251⟩,⟨-1542472240996,-1542472240984⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4307979354944,4307979451456⟩,⟨-19653833684240,-19653833683244⟩,⟨-3447886996816,-3447886996591⟩,⟨141909371813677,141909371865526⟩,⟨25428679574989,25428679582931⟩,⟨7583920210852,7583920214243⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨767716671372,767717847494⟩,⟨-5656577157290,-5656557184950⟩,⟨5656907662150,5656927629048⟩,⟨71693757476824,71694299702896⟩,⟨-32678487906300,-32677843420092⟩,⟨-10668512397520,-10667747138188⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5075696026316,5075697298950⟩,⟨-25310410841530,-25310390868194⟩,⟨2209020665334,2209040632457⟩,⟨213603129290501,213603671568422⟩,⟨-7249808331311,-7249163837161⟩,⟨-3084592186668,-3083826923945⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463934656482,463934772815⟩,⟨1729261042964,1729263882280⟩,⟨201911469524,201913294587⟩,⟨-30946087095040,-30946003166473⟩,⟨1096795052417,1096869864740⟩,⟨-281941473469,-281871526032⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38386665454,38386667648⟩,⟨-779330287662,-779330276588⟩,⟨321668947845,321668966201⟩,⟨9684320196733,9684320226415⟩,⟨-6530558220472,-6530558128119⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨502321321936,502321440463⟩,⟨949930755302,949933605692⟩,⟨523580417369,523582260788⟩,⟨-21261766898307,-21261682940058⟩,⟨-5433763168055,-5433688263379⟩,⟨-281941473469,-281871526032⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504862395711,504862407910⟩,⟨2536208829314,2536208952001⟩,⟨0,0⟩,⟨3381169318170,3381172243620⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨230650717648,230650777646⟩,⟨1594868161852,1594869810661⟩,⟨240412249568,240413101820⟩,⟨-3835691908026,-3835638058235⟩,⟨-1287292870667,-1287254105842⟩,⟨-129458977595,-129426856724⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-767717847494,-767716671372⟩,⟨5656557184950,5656577157290⟩,⟨-5656927629048,-5656907662150⟩,⟨-71694299702896,-71693757476824⟩,⟨32677843420092,32678487906300⟩,⟨10667747138188,10668512397520⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3540261507450,3540262780084⟩,⟨-13997276499290,-13997256525954⟩,⟨-9104814625864,-9104794658741⟩,⟨70215072110781,70215614388702⟩,⟨58106522995081,58107167489231⟩,⟨18251667349040,18252432611763⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449603217927,449603379562⟩,⟨409306684883,409310007662⟩,⟨-167345302209,-167342410890⟩,⟨-13867361543285,-13867266024804⟩,⟨-7121485169159,-7121383620858⟩,⟨-3891736150945,-3891627405635⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨328275507278,328275507284⟩,⟨1936600753766,1936600753768⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-328275507284,-328275507278⟩,⟨-1936600753768,-1936600753766⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨771236120492,771236120498⟩,⟨-1936600753768,-1936600753766⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1342136159257,1342136186383⟩,⟨-8718300555942,-8718300487468⟩,⟨-3942473904100,-3942473873129⟩,⟨52872791410225,52872791423523⟩,⟨33809119578880,33809119662708⟩,⟨10812004566603,10812004569395⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1342136186383,-1342136159257⟩,⟨8718300487468,8718300555942⟩,⟨3942473873129,3942473904100⟩,⟨-52872791423523,-52872791410225⟩,⟨-33809119662708,-33809119578880⟩,⟨-10812004569395,-10812004566603⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-242624558607,-242624531481⟩,⟨8718300487468,8718300555942⟩,⟨3942473873129,3942473904100⟩,⟨-52872791423523,-52872791410225⟩,⟨-33809119662708,-33809119578880⟩,⟨-10812004569395,-10812004566603⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11530636263,-11530634972⟩,⟨443287611078,443287617603⟩,⟨90741177774,90741190065⟩,⟨-4593571657529,-4593571640344⟩,⟨1637375718900,1637375781113⟩,⟨2626282594545,2626282619394⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438072581664,438072744590⟩,⟨852594295961,852597625265⟩,⟨-76604124435,-76601220825⟩,⟨-18460933200814,-18460837665148⟩,⟨-5484109450259,-5484007839745⟩,⟨-1265453556400,-1265344786241⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100498837341,-100498837339⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4776167526,4776167528⟩,⟨29626256529,29626256534⟩,⟨40022876823,40022876824⟩,⟨-313523133486,-313523133475⟩,⟨248259301866,248259301870⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10401748374,10401748631⟩,⟨12267513064,12267514660⟩,⟨87163587057,87163589166⟩,⟨-875720547025,-875720530019⟩,⟨102798145600,102798158703⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1465252476697,1465252497752⟩,⟨-7245146399844,-7245146027772⟩,⟨-1353261117218,-1353261050752⟩,⟨104937172241998,104937179530129⟩,⟨22173343475918,22173344950510⟩,⟨4938174333634,4938174613582⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13861779340,13861779883⟩,⟨-52193343206,-52193335628⟩,⟨103355323371,103355328797⟩,⟨-335950551262,-335950389014⟩,⟨-242696240050,-242696155384⟩,⟨-167842286161,-167842266627⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13861779883,-13861779340⟩,⟨52193335628,52193343206⟩,⟨-103355328797,-103355323371⟩,⟨335950389014,335950551262⟩,⟨242696155384,242696240050⟩,⟨167842266627,167842286161⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114360617224,-114360616679⟩,⟨-823550496028,-823550488448⟩,⟨-103355328797,-103355323371⟩,⟨2534973644566,2534973806814⟩,⟨242696155384,242696240050⟩,⟨167842266627,167842286161⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨90934264057,90934265903⟩,⟨-590694349056,-590694344388⟩,⟨598142876776,598142892197⟩,⟨3582310440334,3582310441370⟩,⟨-3329899852605,-3329899813245⟩,⟨-2385765308915,-2385765308539⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨121182579847,121182584049⟩,⟨-1386386829466,-1386386768996⟩,⟨685188320262,685188360038⟩,⟨21237344609093,21237345919315⟩,⟨-5818125444843,-5818124823959⟩,⟨-4243326080747,-4243325892837⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-121182584049,-121182579847⟩,⟨1386386768996,1386386829466⟩,⟨-685188360038,-685188320262⟩,⟨-21237345919315,-21237344609093⟩,⟨5818124823959,5818125444843⟩,⟨4243325892837,4243326080747⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨978329043727,978329047929⟩,⟨1386386768996,1386386829466⟩,⟨-685188360038,-685188320262⟩,⟨-21237345919315,-21237344609093⟩,⟨5818124823959,5818125444843⟩,⟨4243325892837,4243326080747⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124245026907,124245027445⟩,⟨780409175922,780409186211⟩,⟨186270498879,186270505114⟩,⟨-2501784808648,-2501784560921⟩,⟨-669569139965,-669569013711⟩,⟨-154231886211,-154231838766⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11894690621,11894690735⟩,⟨171315590204,171315592600⟩,⟨21500051876,21500053108⟩,⟨706375863644,706375922621⟩,⟨104343480844,104343508252⟩,⟨-15483646300,-15483640027⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172703289906,172703444451⟩,⟨1678666862936,1678672348102⟩,⟨107427769792,107430433955⟩,⟨-2014509547799,-2014298510710⟩,⟨483901727638,484034473990⟩,⟨-536979801517,-536882377578⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172703444451,-172703289906⟩,⟨-1678672348102,-1678666862936⟩,⟨-107430433955,-107427769792⟩,⟨2014298510710,2014509547799⟩,⟨-484034473990,-483901727638⟩,⟨536882377578,536979801517⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57947273197,57947487740⟩,⟨-83804186250,-83797052275⟩,⟨132981815613,132985332028⟩,⟨-1821393397316,-1821128510436⟩,⟨-1771327344657,-1771155833480⟩,⟨407423399983,407552944793⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27781551920193,27781577075658⟩,⟨-240798120255323,-240797498323216⟩,⟨-82996099194824,-82995673291798⟩,⟨3348788568483451,3348810500085984⟩,⟨1278504102012024,1278521517608178⟩,⟨297652822831501,297668535258402⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14039712105,14039712228⟩,⟨176372776078,176372779168⟩,⟨42097204904,42097206498⟩,⟨542430206498,542430294147⟩,⟨113098522628,113098564156⟩,⟨28256461185,28256476287⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354743852576,354744176896⟩,⟨1381679905980,1381691987665⟩,⟨3896579976,3903031045⟩,⟨-20786398662310,-20785902735475⟩,⟨-3349940809146,-3349621935238⟩,⟨-1840671365590,-1840436817662⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354744176896,-354743852576⟩,⟨-1381691987665,-1381679905980⟩,⟨-3903031045,-3896579976⟩,⟨20785902735475,20786398662310⟩,⟨3349621935238,3349940809146⟩,⟨1840436817662,1840671365590⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83328404768,83328892014⟩,⟨-529097691704,-529082280715⟩,⟨-80507155480,-80497800801⟩,⟨2324969534661,2325560997162⟩,⟨-2134487515021,-2134067030599⟩,⟨574983261262,575326579349⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨240133710344,240133710350⟩,⟨1554943766672,1554943766682⟩,⟨307138759703,307138759708⟩,⟨-3904517942808,-3904517942803⟩,⟨-1542472240996,-1542472240984⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1660444390203,-1660442912346⟩,⟨-4182033746389,-4181991857122⟩,⟨467772621231,467796804444⟩,⟨42792618746713,42794135808288⟩,⟨-7766521458183,-7765450517522⟩,⟨1879336470882,1880231405780⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187630538523,-187630370712⟩,⟨-1651117557143,-1651111757111⟩,⟨-228440870493,-228437877772⟩,⟨2677048000396,2677282728786⟩,⟨-242931529169,-242785128876⟩,⟨603773381013,603882987865⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52503171821,52503339638⟩,⟨-96173790471,-96167990429⟩,⟨78697889210,78700881936⟩,⟨-1227469942412,-1227235214017⟩,⟨-1785403770165,-1785257369860⟩,⟨255015241804,255124848658⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4391635080,4391677020⟩,⟨-34236283673,-34234790432⟩,⟨5835295408,5836129565⟩,⟨65139849674,65201572144⟩,⟨-304596767745,-304555615990⟩,⟨41705891366,41736873594⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2507097680,2507113708⟩,⟨-9184887286,-9184304008⟩,⟨7515861942,7516171780⟩,⟨-100404556905,-100379735762⟩,⟨-184279311118,-184263430656⟩,⟨35620299646,35631702117⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4362952358,4362980340⟩,⟨-33369533313,-33368406797⟩,⟨5217510856,5218100576⟩,⟨37214471061,37266299523⟩,⟨-286028570709,-285996580060⟩,⟨32141726309,32163624369⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4362980340,-4362952358⟩,⟨33368406797,33369533313⟩,⟨-5218100576,-5217510856⟩,⟨-37266299523,-37214471061⟩,⟨285996580060,286028570709⟩,⟨-32163624369,-32141726309⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨28654740,28724662⟩,⟨-867876876,-865257119⟩,⟨617194832,618618709⟩,⟨27873550151,27987101083⟩,⟨-18600187685,-18527045281⟩,⟨9542266997,9595147285⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57947273197,57947487740⟩,⟨-83804186250,-83797052275⟩,⟨132981815613,132985332028⟩,⟨-1821393397316,-1821128510436⟩,⟨-1771327344657,-1771155833480⟩,⟨407423399983,407552944793⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨28654740,28724662⟩,⟨-867876876,-865257119⟩,⟨617194832,618618709⟩,⟨27873550151,27987101083⟩,⟨-18600187685,-18527045281⟩,⟨9542266997,9595147285⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111669149696,112098646426⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨129278515609,133143986176⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112098646426,-111669149696⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437657167462,438086664192⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨51458909142,53049556992⟩,⟨-133143986176,-129278515609⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163128058838,165148203418⟩,⟨966367641600,970233112167⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨51029412412,53479053722⟩,⟨-133143986176,-129278515609⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2097962621952,-2084430075648⟩,⟨6433811792407,6539540751481⟩,⟨2913801873981,2952780684598⟩,⟨-38895080470205,-37647563822358⟩,⟨-24973088270635,-24370411432671⟩,⟨-7929805880242,-7721829534434⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-315116956566,-309254603074⟩,⟨-896741380787,-849770340208⟩,⟨-403603374352,-386189037754⟩,⟨5467338628659,5955720502775⟩,⟨3455354211712,3693464872150⟩,⟨1128591388667,1207354778475⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309254603074,315116956566⟩,⟨849770340208,896741380787⟩,⟨386189037754,403603374352⟩,⟨-5955720502775,-5467338628659⟩,⟨-3693464872150,-3455354211712⟩,⟨-1207354778475,-1128591388667⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-165148203418,-163128058838⟩,⟨-970233112167,-966367641600⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨934363424358,936383568938⟩,⟨-970233112167,-966367641600⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-178952023936,-176577385984⟩,⟨-1141721262490,-1134719247423⟩,⟨-515518232731,-513901739165⟩,⟨-1185551301406,-1171054255311⟩,⟨755749655185,763492221631⟩,⟨-241706446357,-240193001006⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152401967027,-150055212572⟩,⟨-817135840816,-806371629182⟩,⟨-368747754720,-365411773212⟩,⟨984965633733,1019799386418⟩,⟨1366625863761,1383449126388⟩,⟨203268076946,206687919571⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150055212572,152401967027⟩,⟨806371629182,817135840816⟩,⟨365411773212,368747754720⟩,⟨-1019799386418,-984965633733⟩,⟨-1383449126388,-1366625863761⟩,⟨-206687919571,-203268076946⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨459309815646,467518923593⟩,⟨1656141969390,1713877221603⟩,⟨751600810966,772351129072⟩,⟨-6975519889193,-6452304262392⟩,⟨-5076913998538,-4821980075473⟩,⟨-1414042698046,-1331859465613⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨820027611796,830123280803⟩,⟨4043652499670,4115484625637⟩,⟨751600810966,772351129072⟩,⟨-19109680138160,-18376408416537⟩,⟨-5076913998538,-4821980075473⟩,⟨-1414042698046,-1331859465613⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨102058824824,106958107444⟩,⟨-266287972352,-258557031218⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11302797408299,11845382520321⟩,⟨27323012833583,30906517868591⟩,⟨-101692413632138,-92498837466862⟩,⟨132099515427221,161280202665104⟩,⟨-298282122359956,-191979311109626⟩,⟨1513967670771273,1746055388686507⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8429748018299,8943177636080⟩,⟨61945875090100,67671598716008⟩,⟨-69050700711910,-60665848848654⟩,⟨93617306778262,164225846475324⟩,⟨-641854502279796,-511220306426682⟩,⟨971031946179955,1178107675056746⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨93212213248,98825522432⟩,⟨-784631563153,-638556278232⟩,⟨625361391702,800621830493⟩,⟨6783775488681,11440026190897⟩,⟨-7388058649340,-1066292795949⟩,⟨-5327213688123,2906144080892⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1192723841024,1198337150208⟩,⟨-784631563153,-638556278232⟩,⟨625361391702,800621830493⟩,⟨6783775488681,11440026190897⟩,⟨-7388058649340,-1066292795949⟩,⟨-5327213688123,2906144080892⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨89471139136,94633625728⟩,⟨-723312050564,-585895257259⟩,⟨573788538241,738052667182⟩,⟨5748495391755,10233774834177⟩,⟨-6504922717707,-492829999918⟩,⟨-5406309699996,2379590932078⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨97056145688,103139417997⟩,⟨-855856552395,-687526698394⟩,⟨673319905539,873298337457⟩,⟨7468382877228,13170566178169⟩,⟨-8778850465043,-1287849107503⟩,⟨-5698043339851,3918442709865⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-98825522432,-93212213248⟩,⟨638556278232,784631563153⟩,⟨-800621830493,-625361391702⟩,⟨-11440026190897,-6783775488681⟩,⟨1066292795949,7388058649340⟩,⟨-2906144080892,5327213688123⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1000686105344,1006299414528⟩,⟨638556278232,784631563153⟩,⟨-800621830493,-625361391702⟩,⟨-11440026190897,-6783775488681⟩,⟨1066292795949,7388058649340⟩,⟨-2906144080892,5327213688123⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-103552265024,-97401832128⟩,⟨697704920393,862120022053⟩,⟨-879689452445,-683287808590⟩,⟨-13245800385060,-7854882724943⟩,⟨1598648498199,8807445666268⟩,⟨-3896964060751,5428690487431⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-94773516746,-88647229900⟩,⟨561097516668,732465488936⟩,⟨-749714341209,-546470266300⟩,⟨-10711520459662,-4841002207192⟩,⟨-496374094033,7172669125354⟩,⟨-3291055751668,6523280736094⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2282628942,14492188097⟩,⟨-294759035727,44938790542⟩,⟨-76394435670,326828071157⟩,⟨-3243137582434,8329563970977⟩,⟨-9275224559076,5884820017851⟩,⟨-8989099091519,10441723445959⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1141314471,7246094049⟩,⟨-147379517864,22469395271⟩,⟨-38197217835,163414035579⟩,⟨-1621568791217,4164781985489⟩,⟨-4637612279538,2942410008926⟩,⟨-4494549545760,5220861722980⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7246094049,-1141314471⟩,⟨-22469395271,147379517864⟩,⟨-163414035579,38197217835⟩,⟨-4164781985489,1621568791217⟩,⟨-2942410008926,4637612279538⟩,⟨-5220861722980,4494549545760⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754877289567,760982088409⟩,⟨-22469395271,147379517864⟩,⟨-163414035579,38197217835⟩,⟨-4164781985489,1621568791217⟩,⟨-2942410008926,4637612279538⟩,⟨-5220861722980,4494549545760⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7902159903,8882565348⟩,⟨-141047392654,-108268512080⟩,⟨106031292308,143921844336⟩,⟨1891903317202,3176343406899⟩,⟨-2470773168416,-907166312234⟩,⟨-246268983766,1688379638870⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8882565348,-7902159903⟩,⟨108268512080,141047392654⟩,⟨-143921844336,-106031292308⟩,⟨-3176343406899,-1891903317202⟩,⟨907166312234,2470773168416⟩,⟨-1688379638870,246268983766⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090629062428,1091609467873⟩,⟨108268512080,141047392654⟩,⟨-143921844336,-106031292308⟩,⟨-3176343406899,-1891903317202⟩,⟨907166312234,2470773168416⟩,⟨-1688379638870,246268983766⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8918639360,-7930692992⟩,⟨109052267736,142196144990⟩,⟨-145094007477,-106798852732⟩,⟨-3220602701869,-1916414875673⟩,⟨924325861217,2509660758189⟩,⟨-1721277478173,237901015298⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4459319680,-3965346496⟩,⟨54526133868,71098072495⟩,⟨-72547003739,-53399426366⟩,⟨-1610301350935,-958207437836⟩,⟨462162930608,1254830379095⟩,⟨-860638739087,118950507649⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3965346496,4459319680⟩,⟨-71098072495,-54526133868⟩,⟨53399426366,72547003739⟩,⟨958207437836,1610301350935⟩,⟨-1254830379095,-462162930608⟩,⟨-118950507649,860638739087⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766088730112,766582722560⟩,⟨-71098072495,-54526133868⟩,⟨53399426366,72547003739⟩,⟨958207437836,1610301350935⟩,⟨-1254830379095,-462162930608⟩,⟨-118950507649,860638739087⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272657265607,272902366969⟩,⟨27067128020,35261848164⟩,⟨-35980461084,-26507823077⟩,⟨-794085851725,-472975829300⟩,⟨226791578058,617693292104⟩,⟨-422094909718,61567245942⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532177460224,1533165445120⟩,⟨-142196144990,-109052267736⟩,⟨106798852732,145094007478⟩,⟨1916414875672,3220602701870⟩,⟨-2509660758190,-924325861216⟩,⟨-237901015298,1721277478174⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1201357967779,1208096937850⟩,⟨-947261067906,-762332424777⟩,⟨746579874554,966565615962⟩,⟨9066215199091,15296667349799⟩,⟨-10435127214671,-2220478166174⟩,⟨-5503458829525,5055142470304⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1303204307782,1316682247924⟩,⟨-1894522135812,-1524664849553⟩,⟨1493159749108,1933131231923⟩,⟨18132430398184,30593334699585⟩,⟨-20870254429335,-4440956332349⟩,⟨-11002180376836,10110284940605⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨186872971328,198185890752⟩,⟨-1598405641362,-1273190045044⟩,⟨1246881325284,1630980081040⟩,⟨12818039397117,24337250498219⟩,⟨-16164365886871,-1337451576498⟩,⟨-11701867234067,7116029805602⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨63995487736,68398051052⟩,⟨-545070284068,-425158554843⟩,⟨414658311390,557550931811⟩,⟨4072766437673,8095564952441⟩,⟨-5421430376115,-91304800462⟩,⟨-4394254823361,2470972369137⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379949885181,380536656784⟩,⟨2424693705,22126509073⟩,⟨-23687349748,-926039287⟩,⟨-641165339679,134899648529⟩,⟨-301612036032,641406963961⟩,⟨-657115541709,507926835643⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176897147916,3181803355563⟩,⟨-185293386211,-20242471726⟩,⟨7731007032,198364289219⟩,⟨-1129428271643,5390873640792⟩,⟨-5394419444888,2525682446328⟩,⟨-4253479410596,5527597101904⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨184906714337,197932557377⟩,⟨-1588869204494,-1229619035387⟩,⟨1198551723409,1625799228819⟩,⟨11713129340422,23946283198411⟩,⟨-16216587136003,-117320101883⟩,⟨-12975008750257,7695617962764⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨371779685665,396118448129⟩,⟨-3187274845856,-2502809080431⟩,⟨2445433048693,3256779309859⟩,⟨24531168737539,48283533696630⟩,⟨-32380953022874,-1454771678381⟩,⟨-24676875984324,14811647768366⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518266208295,526682687341⟩,⟨-31102549364,204005433794⟩,⟨-226200707532,52873290042⟩,⟨-5770991304831,2284115048544⟩,⟨-4116746268346,6429708019392⟩,⟨-7238166688262,6270012539636⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355819238931,364521921567⟩,⟨-32289539791,211791049500⟩,⟨-234833378478,54891133929⟩,⟨-5997487588600,2412303086589⟩,⟨-4319337027419,6685720668138⟩,⟨-7526189766015,6559728181719⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711638477862,729043843134⟩,⟨-64579079582,423582099000⟩,⟨-469666756956,109782267858⟩,⟨-11994975177200,4824606173178⟩,⟨-8638674054838,13371441336276⟩,⟨-15052379532030,13119456363438⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523294894876,1525263285217⟩,⟨-33927632910,31995124918⟩,⟨-37122991604,39062715170⟩,⟨-1259928531227,1328699384668⟩,⟨-1602494445956,1546447307200⟩,⟨-1926280654168,1967546461940⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨985924325800,1011343381148⟩,⟨-112081425837,608815819498⟩,⟨-676145417984,178193017313⟩,⟨-17501207056992,7598446147031⟩,⟨-13074252601243,19604046771663⟩,⟨-22191559604773,19535876724573⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67613641011,67735256287⟩,⟨13424231134,17504211116⟩,⟨-17860935250,-13146837876⟩,⟨-392856744100,-232315684804⟩,⟨110171884406,305321865810⟩,⟨-208252522978,32917233922⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50426981545,51139625771⟩,⟨258673306855,266749392743⟩,⟨32734250678,37775527386⟩,⟨-1375113024058,-1172270035089⟩,⟨-288272372016,-102062301683⟩,⟨-269433839255,-75023175290⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135100448520,2137854864587⟩,⟨-396558272638,-303930258470⟩,⟨297649958034,404639865446⟩,⟨5362708314424,9018433990818⟩,⟨-7036500322932,-2597294783370⟩,⟨-642713750621,4838612625475⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2975278023347,2981037328088⟩,⟨-829444762419,-635293542711⟩,⟨622166076123,846348292843⟩,⟨11254676459023,18939963985922⟩,⟨-14796101884719,-5473306274623⟩,⟨-1300947595459,10200580390161⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136455391816,138651679088⟩,⟨661391377765,694084484402⟩,⟨117113317075,141783122849⟩,⟨-3614542644156,-2590162298933⟩,⟨-1351884540697,-340786757646⟩,⟨-753962035425,329584113705⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8719157442351,8859494692924⟩,⟨-45064088154851,-41591819094280⟩,⟨-9205402642652,-7364710307797⟩,⟨559682900813784,693117281029100⟩,⟨91692255531527,181419494518832⟩,⟨-8957228571263,68081326764697⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7818407014286,8149064631657⟩,⟨-42353578537821,-32389457990132⟩,⟨-13915386967458,-5168064448049⟩,⟨310939573033084,707950368770115⟩,⟨-35528634646768,353485106371720⟩,⟨-190034839142865,231357241319782⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15636814028572,16298129263314⟩,⟨-84707157075642,-64778915980264⟩,⟨-27830773934916,-10336128896098⟩,⟨621879146066168,1415900737540230⟩,⟨-71057269293536,706970212743440⟩,⟨-380069678285730,462714482639564⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10784481866270,10825960642718⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533866,2099083303790624⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9684970238494,9726449014942⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533869,2099083303790615⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2392217469760,2396916459264⟩,⟨-12101371604921,-11957606413725⟩,⟨0,0⟩,⟨101381360168522,108260423343400⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7320248083806,7410900541735⟩,⟨-44077647633316,-42834561504550⟩,⟨-19902257895509,-19399296965820⟩,⟨501294392835162,524319280752863⟩,⟨275766872777872,286695194470478⟩,⟨102819663612396,106896555178060⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6220736456030,6311388913959⟩,⟨-44077647633317,-42834561504549⟩,⟨-19902257895510,-19399296965820⟩,⟨501294392835161,524319280752859⟩,⟨275766872777870,286695194470477⟩,⟨102819663612395,106896555178060⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1905478051776,1921385235712⟩,⟨-7790699130337,-7462239942233⟩,⟨-3517712754732,-3379565556057⟩,⟨32129084262042,42027899267547⟩,⟨23116442345251,27736548155455⟩,⟨6657924928702,8506144881430⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100284130918,100713627649⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138625993408,140646137989⟩,⟨675487466125,682911074159⟩,⟨306119203879,308157714204⟩,⟨-1712309844053,-1698693120000⟩,⟨-1546410021360,-1538534460618⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4297695521536,4318301694976⟩,⟨-19892070735258,-19419846355958⟩,⟨-3517712754732,-3379565556057⟩,⟨133510444430564,150288322610947⟩,⟨23116442345251,27736548155455⟩,⟨6657924928702,8506144881430⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨743559371330,792236896258⟩,⟨-6374549691712,-5005618160862⟩,⟨4890866097386,6513558619718⟩,⟨49062337475078,96567067393260⟩,⟨-64761906045748,-2909543356762⟩,⟨-49353751968648,29623295536732⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5041254892866,5110538591234⟩,⟨-26266620426970,-24425464516820⟩,⟨1373153342654,3133993063661⟩,⟨182572781905642,246855390004207⟩,⟨-41645463700497,24827004798693⟩,⟨-42695827039946,38129440418162⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459802200263,468117724053⟩,⟨1607328198998,1844665463049⟩,⟨125242413182,287069097311⟩,⟨-35431426056336,-26360842977778⟩,⟨-2721503660295,4771517388378⟩,⟨-3910874171804,3492599957772⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37357021708,39423357784⟩,⟨-800355806522,-758494593794⟩,⟨320394994437,322946015318⟩,⟨9329274338597,10046959287629⟩,⟨-6562818552468,-6498504886492⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497159221971,507541081837⟩,⟨806972392476,1086170869255⟩,⟨445637407619,610015112629⟩,⟨-26102151717739,-16313883690149⟩,⟨-9284322212763,-1726987498114⟩,⟨-3910874171804,3492599957772⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504367106722,505357825907⟩,⟨2516159178967,2556424289217⟩,⟨0,0⟩,⟨2234856254543,4531068346710⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228056486199,233276166615⟩,⟨1507889529027,1679286741305⟩,⟨204422440154,280375307820⟩,⟨-7293151849666,-341111263720⟩,⟨-3247451090639,626115945985⟩,⟨-1797517023860,1605269718696⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-792236896258,-743559371330⟩,⟨5005618160862,6374549691712⟩,⟨-6513558619718,-4890866097386⟩,⟨-96567067393260,-49062337475078⟩,⟨2909543356762,64761906045748⟩,⟨-29623295536732,49353751968648⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3505458625278,3574742323646⟩,⟨-14886452574396,-13045296664246⟩,⟨-10031271374450,-8270431653443⟩,⟨36943377037304,101225985135869⟩,⟨26025985702013,92498454201203⟩,⟨-22965370608030,57859896850078⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441966844191,457270018275⟩,⟨249357346046,575540898991⟩,⟨-307201275369,-40847572152⟩,⟨-19401341674062,-8496065995925⟩,⟨-12149012707725,-1785981378339⟩,⟨-9695542442725,1685236185498⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨326256117676,330296406836⟩,⟨1932735283200,1940466224334⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-330296406836,-326256117676⟩,⟨-1940466224334,-1932735283200⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨769215220940,773255510100⟩,⟨-1940466224334,-1932735283200⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1333067048647,1351256033140⟩,⟨-8869923643850,-8570035068171⟩,⟨-4005012003861,-3881273659758⟩,⟨48711853656042,57055769265657⟩,⟨31864438859797,35765529067701⟩,⟨10038767458442,11588486435813⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1351256033140,-1333067048647⟩,⟨8570035068171,8869923643850⟩,⟨3881273659758,4005012003861⟩,⟨-57055769265657,-48711853656042⟩,⟨-35765529067701,-31864438859797⟩,⟨-11588486435813,-10038767458442⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-251744405364,-233555420871⟩,⟨8570035068171,8869923643850⟩,⟨3881273659758,4005012003861⟩,⟨-57055769265657,-48711853656042⟩,⟨-35765529067701,-31864438859797⟩,⟨-11588486435813,-10038767458442⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12244574990,-10839536019⟩,⟨425204736530,461908145270⟩,⟨79829303551,101833437083⟩,⟨-4923315402035,-4276062185660⟩,⟨1420252611458,1850641885939⟩,⟨2526206284066,2725584902597⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429722269201,446430482256⟩,⟨674562082576,1037449044261⟩,⟨-227371971818,60985864931⟩,⟨-24324657076097,-12772128181585⟩,⟨-10728760096267,64660507600⟩,⟨-7169336158659,4410821088095⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100713627649,-100284130918⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4654284816,4898601677⟩,⟨28428405438,30824900855⟩,⟨39917784923,40128086017⟩,⟨-319156335412,-307894461395⟩,⟨247702508009,248816179610⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10126369894,10678867500⟩,⟨7937277484,16580639794⟩,⟨86849488477,87478538129⟩,⟨-945129166242,-805900694506⟩,⟨97273538155,108293929972⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1456320823149,1474250137709⟩,⟨-7398840830252,-7093952757412⟩,⟨-1388537095601,-1318565491436⟩,⟨101349893175326,108620830156113⟩,⟨21305258739944,23064646882090⟩,⟨4724219341053,5157788553184⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13412539683,14318467841⟩,⟨-61347253360,-43102753927⟩,⟨101547552626,105149379114⟩,⟨-556979399220,-114883598879⟩,⟨-284541059281,-200648482208⟩,⟨-177438048936,-158210365367⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14318467841,-13412539683⟩,⟨43102753927,61347253360⟩,⟨-105149379114,-101547552626⟩,⟨114883598879,556979399220⟩,⟨200648482208,284541059281⟩,⟨158210365367,177438048936⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115032095490,-113696670601⟩,⟨-833070574457,-813967081564⟩,⟨-105149379114,-101547552626⟩,⟨2313906854431,2756002654772⟩,⟨200648482208,284541059281⟩,⟨158210365367,177438048936⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨88435104176,93454095115⟩,⟨-611598904094,-570372406935⟩,⟨587371848643,608702979669⟩,⟨3245934655685,3931001408432⟩,⟨-3555272190545,-3100750676078⟩,⟨-2494176529234,-2276721350381⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨117133716875,125305371142⟩,⟨-1448917594894,-1326042969858⟩,⟨659963349159,710108884053⟩,⟨19810977763606,22734263118120⟩,⟨-6465462162634,-5163894868742⟩,⟨-4501695545574,-3985948523729⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-125305371142,-117133716875⟩,⟨1326042969858,1448917594894⟩,⟨-710108884053,-659963349159⟩,⟨-22734263118120,-19810977763606⟩,⟨5163894868742,6465462162634⟩,⟨3985948523729,4501695545574⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨974206256634,982377910901⟩,⟨1326042969858,1448917594894⟩,⟨-710108884053,-659963349159⟩,⟨-22734263118120,-19810977763606⟩,⟨5163894868742,6465462162634⟩,⟨3985948523729,4501695545574⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨122827541517,125662754012⟩,⟨765692802609,795499925835⟩,⟨180397520671,192120984702⟩,⟨-2808675038652,-2203005529985⟩,⟨-802468087100,-535519075526⟩,⟨-207404283237,-100351823174⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11756976987,12034782224⟩,⟨168339005818,174313488736⟩,⟨21001357964,22001683500⟩,⟨628485666884,783844510073⟩,⟨90813065522,117841026212⟩,⟨-18370274383,-12608506709⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167203018176,178392325636⟩,⟨1466881748920,1891184681278⟩,⟨-5950800735,215609045088⟩,⟨-11270701943290,7281068561894⟩,⟨-5593493463885,6665142756493⟩,⟨-5546193891827,4490507917630⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178392325636,-167203018176⟩,⟨-1891184681278,-1466881748920⟩,⟨-215609045088,5950800735⟩,⟨-7281068561894,11270701943290⟩,⟨-6665142756493,5593493463885⟩,⟨-4490507917630,5546193891827⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49664160563,66073148439⟩,⟨-383295152251,212404992385⟩,⟨-11186604934,286326108555⟩,⟨-14574220411560,10929590679570⟩,⟨-9912593847132,6219609409870⟩,⟨-6288024941490,7151463610523⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27098945730492,28480812885625⟩,⟨-263506901721573,-218388286913535⟩,⟨-100777265583763,-65975568622227⟩,⟨2413949194019657,4297656102786823⟩,⟨473841636400197,2114768548528979⟩,⟨-505941247022992,1112756182004553⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13721187274,14361947020⟩,⟨171072614650,181834750942⟩,⟨40304774228,43914864440⟩,⟨424442309823,658893220693⟩,⟨67827810842,158353464214⟩,⟨11787546170,44718954152⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨338177150566,372019645284⟩,⟨774357739322,1984749300842⟩,⟨-322998730236,314201228721⟩,⟨-46570890491602,5245977523468⟩,⟨-19605928955441,13454633164922⟩,⟨-14368298456712,10856380597039⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-372019645284,-338177150566⟩,⟨-1984749300842,-774357739322⟩,⟨-314201228721,322998730236⟩,⟨-5245977523468,46570890491602⟩,⟨-13454633164922,19605928955441⟩,⟨-10856380597039,14368298456712⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57702623917,108253331690⟩,⟨-1310187218266,263091304939⟩,⟨-541573200539,383984595167⟩,⟨-29570634599565,33798762310017⟩,⟨-24183393261189,19670589463041⟩,⟨-18025716755698,18779119544807⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨238910124326,241359765638⟩,⟨1550801801049,1559084402543⟩,⟨306119203879,308157714204⟩,⟨-3911333099605,-3897716375552⟩,⟨-1546410021360,-1538534460618⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1705127908032,-1616948515089⟩,⟨-5650094713807,-2713759475576⟩,⟨-489812673885,1467517039940⟩,⟨-19314108893236,104906738765607⟩,⟨-57475838700796,40839274655879⟩,⟨-44250458181445,47716545834415⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-194878401877,-180630932725⟩,⟨-1879412217518,-1429189291998⟩,⟨-353922643885,-97571747005⟩,⟨-7143369153673,12565767705185⟩,⟨-7122992530771,6528480908923⟩,⟨-5080962452085,6287996284889⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44031722449,60728832913⟩,⟨-328610416469,129895110545⟩,⟨-47803440006,210585967199⟩,⟨-11054702253278,8668051329633⟩,⟨-8669402552131,4989946448305⟩,⟨-5430062762613,5939580149231⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2606386605,6505286778⟩,⟨-116470957263,36722502899⟩,⟨-33646241468,51265329927⟩,⟨-3718117530213,4020632389112⟩,⟨-2904257129466,2051732289872⟩,⟨-1984379744139,2032588731979⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1763321581,3354208409⟩,⟨-36299983686,14348876840⟩,⟨-5280611952,23262400676⟩,⟨-1298802185223,1153940405294⟩,⟨-1083541867826,600971746450⟩,⟨-618143727239,736782058153⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3055875432,5861444620⟩,⟨-87200425012,13107084103⟩,⟨-19959071818,35230889196⟩,⟨-2421457793189,2659125032941⟩,⟨-2067140683037,1288358342501⟩,⟨-1218370976387,1347257151062⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5861444620,-3055875432⟩,⟨-13107084103,87200425012⟩,⟨-35230889196,19959071818⟩,⟨-2659125032941,2421457793189⟩,⟨-1288358342501,2067140683037⟩,⟨-1347257151062,1218370976387⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3255058015,3449411346⟩,⟨-129578041366,123922927911⟩,⟨-68877130664,71224401745⟩,⟨-6377242563154,6442090182301⟩,⟨-4192615471967,4118872972909⟩,⟨-3331636895201,3250959708366⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49664160563,66073148439⟩,⟨-383295152251,212404992385⟩,⟨-11186604934,286326108555⟩,⟨-14574220411560,10929590679570⟩,⟨-9912593847132,6219609409870⟩,⟨-6288024941490,7151463610523⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3255058015,3449411346⟩,⟨-129578041366,123922927911⟩,⟨-68877130664,71224401745⟩,⟨-6377242563154,6442090182301⟩,⟨-4192615471967,4118872972909⟩,⟨-3331636895201,3250959708366⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (521/5120) u, BivariateJet2.affineZ (611/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000049

end


