-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000030_000033_data
-- name    : GeneralCK_RB2_cells000030_000033_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T02:16:25.025353+00:00
-- url     : https://prove2.me/theorems/cb29605d-d31e-4ed7-b5b7-61b0713cf2de
-- title:
--   Exact certificate data for RB2 cells 000030–000033
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000030 through 000033. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000030Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2083417199872,-2083417161152⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2083417199872,-2083417161152⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-179131153088,-179131153024⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-179131153088,-179131153024⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨94580247232,94580247296⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-103488347008,-103488346944⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨94580371520,94580371584⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-103488495744,-103488495680⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-8908124224,-8908124160⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-8908099712,-8908099648⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨198068594176,198068594240⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨198068867264,198068867328⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1904286008128,1904286046720⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1904286008128,1904286046720⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2518909148928,-2518909091072⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2090163983104,-2090163944320⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2076706572416,-2076706533696⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-180322815680,-180322815616⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-177941668224,-177941668160⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨92003550720,92003550784⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-100410964992,-100410964928⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨97178602688,97178602752⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-106607685824,-106607685760⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9429083072,-9429083008⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8407414272,-8407414208⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨192414515712,192414515776⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨203786288512,203786288576⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1896383718080,1896383756672⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1912222276160,1912222314752⟩



end LaneCBRB2Cell000030Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000030
open Set LaneCBRB2Cell000030Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111454401331,111454401332⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨135076721459,135076721460⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111454401332,-111454401331⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438301412556,438301412557⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨53846013378,53846013379⟩,⟨-135076721460,-135076721459⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨165300414709,165300414711⟩,⟨964434906316,964434906317⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨53846013377,53846013380⟩,⟨-135076721460,-135076721459⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2083417199872,-2083417161152⟩,⟨6415031659668,6415031659755⟩,⟨2915404056417,2915404056460⟩,⟨-37428100036458,-37428100035457⟩,⟨-24323249670979,-24323249670412⟩,⟨-7730323716190,-7730323715963⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-313220632193,-313220626367⟩,⟨-863031235225,-863031201234⟩,⟨-392217045447,-392217029996⟩,⟨5626934996635,5626934997020⟩,⟨3541147646055,3541147684988⟩,⟨1162175718546,1162175718636⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨313220626367,313220632193⟩,⟨863031201234,863031235225⟩,⟨392217029996,392217045447⟩,⟨-5626934997020,-5626934996635⟩,⟨-3541147684988,-3541147646055⟩,⟨-1162175718636,-1162175718546⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-165300414711,-165300414709⟩,⟨-964434906317,-964434906316⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨934211213065,934211213067⟩,⟨-964434906317,-964434906316⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-179131153088,-179131153024⟩,⟨-1135083136340,-1135083136334⟩,⟨-515854972450,-515854972446⟩,⟨-1171805457856,-1171805457844⟩,⟨761516526064,761516526075⟩,⟨-242022317799,-242022317795⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152200602156,-152200602100⟩,⟨-807310295339,-807310295274⟩,⟨-366893857223,-366893857192⟩,⟨995636399456,995636399483⟩,⟨1372861857737,1372861857822⟩,⟨205636718504,205636718514⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨152200602100,152200602156⟩,⟨807310295274,807310295339⟩,⟨366893857192,366893857223⟩,⟨-995636399483,-995636399456⟩,⟨-1372861857822,-1372861857737⟩,⟨-205636718514,-205636718504⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨465421228467,465421234349⟩,⟨1670341496508,1670341530564⟩,⟨759110887188,759110902670⟩,⟨-6622571396503,-6622571396091⟩,⟨-4914009542810,-4914009503792⟩,⟨-1367812437150,-1367812437050⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨826145318120,826145329928⟩,⟨4069613377328,4069613469328⟩,⟨759110887188,759110902670⟩,⟨-18692929568496,-18692929567578⟩,⟨-4914009542810,-4914009503792⟩,⟨-1367812437150,-1367812437050⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨107692026754,107692026760⟩,⟨-270153442920,-270153442918⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11225769037746,11225769038373⟩,⟨28160674900358,28160674903713⟩,⟨-91376689154474,-91376689144057⟩,⟨141286286610243,141286286636011⟩,⟨-229225207523805,-229225207416932⟩,⟨1487595066467934,1487595066723999⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8434759850233,8434759971263⟩,⟨62709068125363,62709069371933⟩,⟨-60907788352453,-60907787204800⟩,⟨123770053314061,123770059608217⟩,⟨-541174450459710,-541174439433309⟩,⟨977602095135385,977602113893036⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨98767347712,98767483136⟩,⟨-725775782501,-725773747773⟩,⟨704926325803,704928301355⟩,⟨9171726050577,9171775750102⟩,⟨-4036276417358,-4036214537163⟩,⟨-1310717133664,-1310642386910⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1198278975488,1198279110912⟩,⟨-725775782501,-725773747773⟩,⟨704926325803,704928301355⟩,⟨9171726050577,9171775750102⟩,⟨-4036276417358,-4036214537163⟩,⟨-1310717133664,-1310642386910⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨94580247232,94580371584⟩,⟨-665954196262,-665952253981⟩,⟨646823169065,646825054886⟩,⟨8012395333794,8012444240789⟩,⟨-3311821130538,-3311761647400⟩,⟨-1583198950505,-1583128009994⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨103076237569,103076384741⟩,⟨-788207349071,-788204893180⟩,⟨765564173456,765566558010⟩,⟨10400263195706,10400327824228⟩,⟨-4810443464406,-4810367567032⟩,⟨-1008772400679,-1008683572252⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-98767483136,-98767347712⟩,⟨725773747773,725775782501⟩,⟨-704928301355,-704926325803⟩,⟨-9171775750102,-9171726050577⟩,⟨4036214537163,4036276417358⟩,⟨1310642386910,1310717133664⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1000744144640,1000744280064⟩,⟨725773747773,725775782501⟩,⟨-704928301355,-704926325803⟩,⟨-9171775750102,-9171726050577⟩,⟨4036214537163,4036276417358⟩,⟨1310642386910,1310717133664⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-103488495744,-103488346944⟩,⟨797403183518,797405526970⟩,⟨-774500523676,-774498248339⟩,⟨-10655282633447,-10655223266117⟩,⟨4996256697894,4996328586288⟩,⟨894433422861,894518947050⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-94192291880,-94192143699⟩,⟨657462008206,657464529100⟩,⟨-638579248336,-638576800651⟩,⟨-7782162161962,-7782094850975⟩,⟨3145068161264,3145146448338⟩,⟨1683823279812,1683914145107⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8883945689,8884241042⟩,⟨-130745340865,-130740364080⟩,⟨126984925120,126989757359⟩,⟨2618101033744,2618232973253⟩,⟨-1665375303142,-1665221118694⟩,⟨675050879133,675230572855⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4441972844,4442120521⟩,⟨-65372670433,-65370182040⟩,⟨63492462560,63494878680⟩,⟨1309050516872,1309116486627⟩,⟨-832687651571,-832610559347⟩,⟨337525439566,337615286428⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4442120521,-4441972844⟩,⟨65370182040,65372670433⟩,⟨-63494878680,-63492462560⟩,⟨-1309116486627,-1309050516872⟩,⟨832610559347,832687651571⟩,⟨-337615286428,-337525439566⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757681263095,757681430036⟩,⟨65370182040,65372670433⟩,⟨-63494878680,-63492462560⟩,⟨-1309116486627,-1309050516872⟩,⟨832610559347,832687651571⟩,⟨-337615286428,-337525439566⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8872110787,8872135118⟩,⟨-130390703560,-130390159222⟩,⟨126644778960,126645307530⟩,⟨2605910756597,2605927317183⟩,⟨-1655776491148,-1655759162554⟩,⟨668414745477,668433563438⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8872135118,-8872110787⟩,⟨130390159222,130390703560⟩,⟨-126645307530,-126644778960⟩,⟨-2605927317183,-2605910756597⟩,⟨1655759162554,1655776491148⟩,⟨-668433563438,-668414745477⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090639492658,1090639516989⟩,⟨130390159222,130390703560⟩,⟨-126645307530,-126644778960⟩,⟨-2605927317183,-2605910756597⟩,⟨1655759162554,1655776491148⟩,⟨-668433563438,-668414745477⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8908124224,-8908099648⟩,⟨131450854273,131451405972⟩,⟨-127675541891,-127675006172⟩,⟨-2642841605403,-2642824719573⟩,⟨1684492435666,1684510070578⟩,⟨-688696850536,-688677740044⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4454062112,-4454049824⟩,⟨65725427136,65725702986⟩,⟨-63837770946,-63837503086⟩,⟨-1321420802702,-1321412359786⟩,⟨842246217833,842255035289⟩,⟨-344348425268,-344338870022⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4454049824,4454062112⟩,⟨-65725702986,-65725427136⟩,⟨63837503086,63837770946⟩,⟨1321412359786,1321420802702⟩,⟨-842255035289,-842246217833⟩,⟨344338870022,344348425268⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766577433440,766577464992⟩,⟨-65725702986,-65725427136⟩,⟨63837503086,63837770946⟩,⟨1321412359786,1321420802702⟩,⟨-842255035289,-842246217833⟩,⟨344338870022,344348425268⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272659873164,272659879248⟩,⟨32597539805,32597675890⟩,⟨-31661326883,-31661194740⟩,⟨-651481829296,-651477689149⟩,⟨413939790638,413944122787⟩,⟨-167108390860,-167103686369⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533154866880,1533154929984⟩,⟨-131451405972,-131450854272⟩,⟨127675006172,127675541892⟩,⟨2642824719572,2642841605404⟩,⟨-1684510070578,-1684492435666⟩,⟨688677740044,688696850536⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1208026709418,1208026872893⟩,⟨-876104700340,-876102007045⟩,⟨850936494672,850939109723⟩,⟨12342207655617,12342278286933⟩,⟨-6106568205039,-6106484768665⟩,⟨-383401303190,-383303440076⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1316541791060,1316542118010⟩,⟨-1752209400680,-1752204014090⟩,⟨1701872989344,1701878219446⟩,⟨24684415311241,24684556573859⟩,⟨-12213136410075,-12212969537332⟩,⟨-766802458725,-766607027807⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨198068594176,198068867328⟩,⟨-1463360011379,-1463355149350⟩,⟨1421321137533,1421325858432⟩,⟨18667604718486,18667740755658⟩,⟨-8308161263664,-8308006798472⟩,⟨-2477727454558,-2477551875883⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨68061280005,68061388323⟩,⟨-494265253357,-494263509434⟩,⟨480066082276,480067775532⟩,⟨6116401924527,6116447179659⟩,⟨-2622814123745,-2622760416008⟩,⟨-1014968909897,-1014905763738⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380195898782,380195922915⟩,⟨12856209942,12856539111⟩,⟨-12487242577,-12486922942⟩,⟨-260843395338,-260833317670⟩,⟨167037136967,167047647304⟩,⟨-69588188283,-69576814340⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179744302215,3179744504051⟩,⟨-107524856819,-107522090183⟩,⟨104433581961,104436268467⟩,⟨2188734435756,2188819370395⟩,⟨-1404155642080,-1404067199209⟩,⟨588761145644,588856697281⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨196830539878,196830865624⟩,⟨-1436051674264,-1436046358323⟩,⟨1394796775518,1394801937062⟩,⟨17920547841759,17920688142270⟩,⟨-7765889690810,-7765725528754⟩,⟨-2807610085018,-2807418642091⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨394899134054,394899732952⟩,⟨-2899411685643,-2899401507673⟩,⟨2816117913051,2816127795494⟩,⟨36588152560245,36588428897928⟩,⟨-16074050954474,-16073732327226⟩,⟨-5285337539576,-5284970517974⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522123533705,522123763787⟩,⟨90094112414,90097561806⟩,⟨-87509561998,-87506212784⟩,⟨-1796470298309,-1796378388532⟩,⟨1139965371280,1140072448436⟩,⟨-457973401757,-457848912916⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359799031238,359799269065⟩,⟨93126738043,93130324065⟩,⟨-90455209933,-90451728052⟩,⟨-1848906390311,-1848810362986⟩,⟨1170532870972,1170644408972⟩,⟨-465809476870,-465680113684⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨719598062476,719598538130⟩,⟨186253476086,186260648130⟩,⟨-180910419866,-180903456104⟩,⟨-3697812780622,-3697620725972⟩,⟨2341065741944,2341288817944⟩,⟨-931618953740,-931360227368⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524282731762,1524282819197⟩,⟨-1061246750,-1060150712⟩,⟨1029698642,1030762932⟩,⟨36897402389,36930848807⟩,⟨-28750908024,-28715944518⟩,⟨20244176606,20282105059⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨997598272480,997598989117⟩,⟨257513680223,257524355620⟩,⟨-250127118914,-250116753482⟩,⟨-5102589537143,-5102300701674⟩,⟨3227015024875,3227347736449⟩,⟨-1278618625723,-1278234677157⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67614934263,67614937281⟩,⟨16167252522,16167320378⟩,⟨-15702923638,-15702857748⟩,⟨-321179608923,-321177532202⟩,⟨203422469240,203424638092⟩,⟨-81056573293,-81054222955⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50804157014,50804160008⟩,⟨262410268043,262410336032⟩,⟨34883065113,34883117828⟩,⟨-1271176515799,-1271174395570⟩,⟨-196301715381,-196299775416⟩,⟨-166700904368,-166699042324⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137825363968,2137825539953⟩,⟨-366590704506,-366589150840⟩,⟨356059094140,356060602808⟩,⟨7401720555591,7401768213868⟩,⟨-4728277506376,-4728227876682⟩,⟨1950230464100,1950284087183⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2980975624547,2980975992637⟩,⟨-766759075169,-766755793968⟩,⟨744731186947,744734373123⟩,⟨15547137559406,15547238432939⟩,⟨-9953491784586,-9953387033803⟩,⟨4141109240592,4141222089234⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137739292480,137739317607⟩,⟨676012916231,676013342113⟩,⟨128985454435,128985758283⟩,⟨-3094008635760,-3093996097549⟩,⟨-838709935948,-838698796074⟩,⟨-213357286003,-213346682699⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8776911637270,8776913238394⟩,⟨-43076382525957,-43076339671879⟩,⟨-8219127520224,-8219105159930⟩,⟨619983138018580,619984773062017⟩,⟨134120221011120,134121235384428⟩,⟨28988200898097,28988962462176⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7963382710886,7963389884198⟩,⟨-37028058473886,-37027905923766⟩,⟨-9453958525116,-9453849773481⟩,⟨501606961270724,501612018479451⟩,⟨155322427620387,155326596857915⟩,⟨19834011430735,19837953193890⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15926765421772,15926779768396⟩,⟨-74056116947772,-74055811847532⟩,⟨-18907917050232,-18907699546962⟩,⟨1003213922541448,1003224036958902⟩,⟨310644855240774,310653193715830⟩,⟨39668022861470,39675906387780⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10846819911700,10846819911799⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738054,2111240126795878⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9747308283924,9747308284023⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738069,2111240126795861⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2399271880896,2399271938752⟩,⟨-12070358171930,-12070358171514⟩,⟨0,0⟩,⟨105643681588589,105643681622780⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7313507481080,7313507481170⟩,⟨-42670200887692,-42670200886596⟩,⟨-19392090850991,-19392090850469⟩,⟨497913223829407,497913223848831⟩,⟨274930375946195,274930375956503⟩,⟨102837985337595,102837985341864⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6213995853304,6213995853394⟩,⟨-42670200887692,-42670200886596⟩,⟨-19392090850991,-19392090850468⟩,⟨497913223829412,497913223848823⟩,⟨274930375946196,274930375956500⟩,⟨102837985337595,102837985341863⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1904286008128,1904286046720⟩,⟨-7550114796235,-7550114795885⟩,⟨-3431259028974,-3431259028810⟩,⟨36256294572813,36256294583778⟩,⟨25084766194137,25084766199591⟩,⟨7488301397141,7488301399495⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100156582133,100156582135⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨140449174928,140449174931⟩,⟨674448905352,674448905358⟩,⟨306513074108,306513074113⟩,⟨-1691905142294,-1691905142289⟩,⟨-1537821596716,-1537821596708⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4303557889024,4303557985472⟩,⟨-19620472968165,-19620472967399⟩,⟨-3431259028974,-3431259028810⟩,⟨141899976161402,141899976206558⟩,⟨25084766194137,25084766199591⟩,⟨7488301397141,7488301399495⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨789798268108,789799465904⟩,⟨-5798823371286,-5798803015346⟩,⟨5632235826102,5632255590988⟩,⟨73176305120490,73176857795856⟩,⟨-32148101908948,-32147464654452⟩,⟨-10570675079152,-10569941035948⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5093356157132,5093357451376⟩,⟨-25419296339451,-25419275982745⟩,⟨2200976797128,2200996562178⟩,⟨215076281281892,215076834002414⟩,⟨-7063335714811,-7062698454861⟩,⟨-3082373682011,-3081639636453⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨463963391925,463963509830⟩,⟨1745266267796,1745269154040⟩,⟨200491116042,200492916482⟩,⟨-31126874292105,-31126788895376⟩,⟨1111350606788,1111424414010⟩,⟨-280779216022,-280712350425⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨39831689318,39831691580⟩,⟨-806195969165,-806195957771⟩,⟨324226151534,324226169925⟩,⟨10032733248070,10032733278404⟩,⟨-6562358286202,-6562358193788⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨503795081243,503795201410⟩,⟨939070298631,939073196269⟩,⟨524717267576,524719086407⟩,⟨-21094141044035,-21094055616972⟩,⟨-5451007679414,-5450933779778⟩,⟨-280779216022,-280712350425⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503871945521,503871957673⟩,⟨2534900173993,2534900296365⟩,⟨0,0⟩,⟨3319096918590,3319099843609⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨230873599984,230873660622⟩,⟨1591835295995,1591836967387⟩,⟨240461586565,240462425879⟩,⟨-3815969207383,-3815914552777⟩,⟨-1288302899268,-1288264721443⟩,⟨-128672375696,-128641730171⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-789799465904,-789798268108⟩,⟨5798803015346,5798823371286⟩,⟨-5632255590988,-5632235826102⟩,⟨-73176857795856,-73176305120490⟩,⟨32147464654452,32148101908948⟩,⟨10569941035948,10570675079152⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3513758423120,3513759717364⟩,⟨-13821669952819,-13821649596113⟩,⟨-9063514619962,-9063494854912⟩,⟨68723118365546,68723671086068⟩,⟨57232230848589,57232868108539⟩,⟨18058242433089,18058976478647⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨448839702060,448839867395⟩,⟨389817051747,389820446026⟩,⟨-178215718194,-178212832608⟩,⟨-13584997942845,-13584900373720⟩,⟨-7016493362067,-7016392350501⟩,⟨-3863318590682,-3863213393972⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨330600829418,330600829422⟩,⟨1928869812632,1928869812634⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-330600829422,-330600829418⟩,⟨-1928869812634,-1928869812632⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨768910798354,768910798358⟩,⟨-1928869812634,-1928869812632⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1331705857232,1331705884228⟩,⟨-8620631584387,-8620631516408⟩,⟨-3917770889277,-3917770858377⟩,⟨51845048282044,51845048291102⟩,⟨33389752150412,33389752232090⟩,⟨10707970907135,10707970909084⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1331705884228,-1331705857232⟩,⟨8620631516408,8620631584387⟩,⟨3917770858377,3917770889277⟩,⟨-51845048291102,-51845048282044⟩,⟨-33389752232090,-33389752150412⟩,⟨-10707970909084,-10707970907135⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-232194256452,-232194229456⟩,⟨8620631516408,8620631584387⟩,⟨3917770858377,3917770889277⟩,⟨-51845048291102,-51845048282044⟩,⟨-33389752232090,-33389752150412⟩,⟨-10707970909084,-10707970907135⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11371171277,-11371169953⟩,⟨450700713560,450700720231⟩,⟨99303425902,99303438189⟩,⟨-4657106243611,-4657106226304⟩,⟨1552171427970,1552171489967⟩,⟨2599106171830,2599106196598⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437468530783,437468697442⟩,⟨840517765307,840521166257⟩,⟨-78912292292,-78909394419⟩,⟨-18242104186456,-18242006600024⟩,⟨-5464321934097,-5464220860534⟩,⟨-1264212418852,-1264107197374⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100156582135,-100156582133⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4904934631,4904934633⟩,⟨30625182897,30625182903⟩,⟨39925700025,39925700027⟩,⟨-323076080276,-323076080267⟩,⟨249286067484,249286067488⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10703180794,10703181058⟩,⟨12981965793,12981967444⟩,⟨87122870713,87122872820⟩,⟨-906116724363,-906116706841⟩,⟨105671963339,105671976504⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1463333115639,1463333136555⟩,⟨-7208417347436,-7208416978412⟩,⟨-1344596542320,-1344596476458⟩,⟨104128075385250,104128082589609⟩,⟨21951111742583,21951113198200⟩,⟨4893764737224,4893765013412⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14244796055,14244796611⟩,⟨-52892624409,-52892616640⟩,⟨102862324275,102862329702⟩,⟨-362531764425,-362531598370⟩,⟨-232733814641,-232733729816⟩,⟨-165447434808,-165447415352⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14244796611,-14244796055⟩,⟨52892616640,52892624409⟩,⟨-102862329702,-102862324275⟩,⟨362531598370,362531764425⟩,⟨232733729816,232733814641⟩,⟨165447415352,165447434808⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114401378746,-114401378188⟩,⟨-823710208474,-823710200703⟩,⟨-102862329702,-102862324275⟩,⟨2561554853922,2561555019977⟩,⟨232733729816,232733814641⟩,⟨165447415352,165447434808⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨93257958603,93257960499⟩,⟨-603693750465,-603693745684⟩,⟨591072992109,591073007513⟩,⟨3630654127029,3630654127767⟩,⟨-3264006186330,-3264006147230⟩,⟨-2368902806935,-2368902806661⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨124116431034,124116435333⟩,⟨-1414853040510,-1414852978931⟩,⟨672609850773,672609890425⟩,⟨21579563191607,21579564520191⟩,⟨-5619030141908,-5619029525083⟩,⟨-4183330847547,-4183330661765⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-124116435333,-124116431034⟩,⟨1414852978931,1414853040510⟩,⟨-672609890425,-672609850773⟩,⟨-21579564520191,-21579563191607⟩,⟨5619029525083,5619030141908⟩,⟨4183330661765,4183330847547⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨975395192443,975395196742⟩,⟨1414852978931,1414853040510⟩,⟨-672609890425,-672609850773⟩,⟨-21579564520191,-21579563191607⟩,⟨5619029525083,5619030141908⟩,⟨4183330661765,4183330847547⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124594816959,124594817512⟩,⟨779045106686,779045117200⟩,⟨185995190572,185995196844⟩,⟨-2521679649018,-2521679397065⟩,⟨-664627629284,-664627502953⟩,⟨-150636690222,-150636642994⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11903171372,11903171489⟩,⟨171409887458,171409889912⟩,⟨21405124536,21405125770⟩,⟨701135047569,701135108015⟩,⟨105689971854,105689999332⟩,⟨-15182662351,-15182656099⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172421112635,172421269646⟩,⟨1681203146905,1681208729898⟩,⟨105365159615,105367813464⟩,⟨-2073339630675,-2073124543800⟩,⟨504563885952,504695940293⟩,⟨-526677768424,-526583618407⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172421269646,-172421112635⟩,⟨-1681208729898,-1681203146905⟩,⟨-105367813464,-105365159615⟩,⟨2073124543800,2073339630675⟩,⟨-504695940293,-504563885952⟩,⟨526583618407,526677768424⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58452330338,58452547987⟩,⟨-89373433903,-89366179518⟩,⟨135093773101,135097266264⟩,⟨-1742844663583,-1742574922102⟩,⟨-1792998839561,-1792828607395⟩,⟨397911242711,398036038253⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27584170809329,27584196215811⟩,⟨-237626450838116,-237625821303776⟩,⟨-82450232634152,-82449810494254⟩,⟨3279739299688478,3279761515847927⟩,⟨1262320268605738,1262337494317208⟩,⟨295183881675321,295198992125505⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14118876072,14118876199⟩,⟨176560174568,176560177736⟩,⟨42153327238,42153328848⟩,⟨532460148965,532460238405⟩,⟨112940115100,112940156848⟩,⟨28786707820,28786722921⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354209522998,354209852431⟩,⟨1378109638987,1378121909578⟩,⟨-1218766944,-1212322272⟩,⟨-20842919521351,-20842415765158⟩,⟨-3307169019229,-3306851512041⟩,⟨-1809331870640,-1809104148921⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354209852431,-354209522998⟩,⟨-1378121909578,-1378109638987⟩,⟨1212322272,1218766944⟩,⟨20842415765158,20842919521351⟩,⟨3306851512041,3307169019229⟩,⟨1809104148921,1809331870640⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83258678352,83259174444⟩,⟨-537604144271,-537588472730⟩,⟨-77699970020,-77690627475⟩,⟨2600311578702,2600912921327⟩,⟨-2157470422056,-2157051841305⟩,⟨544891730069,545224673266⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨240605757061,240605757066⟩,⟨1551051730464,1551051730472⟩,⟨306513074108,306513074113⟩,⟨-3890928397846,-3890928397841⟩,⟨-1537821596716,-1537821596708⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1657140787292,-1657139286478⟩,⟨-4226389269349,-4226346626380⟩,⟨477303924442,477327985478⟩,⟨43681325709711,43682872611791⟩,⟨-7858434611134,-7857370604069⟩,⟨1806114254920,1806977859167⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187784420618,-187784249714⟩,⟨-1653073594392,-1653067680805⟩,⟨-226237381714,-226234391582⟩,⟨2761357728340,2761597373555⟩,⟨-265560354494,-265414391060⟩,⟨593182306021,593288591770⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52821336443,52821507352⟩,⟨-102021863928,-102015950333⟩,⟨80275692394,80278682531⟩,⟨-1129570669506,-1129331024286⟩,⟨-1803381951210,-1803235987768⟩,⟨243739656400,243845942151⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4426204914,4426247770⟩,⟨-35347957570,-35346428366⟩,⟨6099042162,6099879682⟩,⟨93651505654,93714842760⟩,⟨-310209709096,-310168424373⟩,⟨40004714261,40034941159⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2537575331,2537591753⟩,⟨-9802440466,-9801840560⟩,⟨7713005026,7713317282⟩,⟨-89600455436,-89574884022⟩,⟨-188169967844,-188153964416⟩,⟨35140767402,35151928560⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4394923232,4394951764⟩,⟨-34402327988,-34401175875⟩,⟨5439353969,5439946298⟩,⟨63108222558,63161294212⟩,⟨-290382319981,-290350205422⟩,⟨30001885024,30023277468⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4394951764,-4394923232⟩,⟨34401175875,34402327988⟩,⟨-5439946298,-5439353969⟩,⟨-63161294212,-63108222558⟩,⟨290350205422,290382319981⟩,⟨-30023277468,-30001885024⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨31253150,31324538⟩,⟨-946781695,-944100378⟩,⟨659095864,660525713⟩,⟨30490211442,30606620202⟩,⟨-19859503674,-19786104392⟩,⟨9981436793,10033056135⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58452330338,58452547987⟩,⟨-89373433903,-89366179518⟩,⟨135093773101,135097266264⟩,⟨-1742844663583,-1742574922102⟩,⟨-1792998839561,-1792828607395⟩,⟨397911242711,398036038253⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨31253150,31324538⟩,⟨-946781695,-944100378⟩,⟨659095864,660525713⟩,⟨30490211442,30606620202⟩,⟨-19859503674,-19786104392⟩,⟨9981436793,10033056135⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111239652966,111669149696⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨133143986176,137009456743⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111669149696,-111239652966⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438086664192,438516160922⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨53049556992,54643224741⟩,⟨-137009456743,-133143986176⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨164289209958,166312374437⟩,⟨962502171033,966367641600⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52620060262,55072721471⟩,⟨-137009456743,-133143986176⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2090163983104,-2076706533696⟩,⟨6363220610569,6467451264252⟩,⟨2896244990087,2934785662581⟩,⟨-38042276951700,-36825964833749⟩,⟨-24621262224091,-24030490358552⟩,⟨-7833447748717,-7629055328474⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-316158671006,-310301835029⟩,⟨-886264708253,-839661307479⟩,⟨-400858775086,-383521424596⟩,⟨5386324024621,5866024896313⟩,⟨3423180333588,3658327046808⟩,⟨1123056170092,1201015412451⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨310301835029,316158671006⟩,⟨839661307479,886264708253⟩,⟨383521424596,400858775086⟩,⟨-5866024896313,-5386324024621⟩,⟨-3658327046808,-3423180333588⟩,⟨-1201015412451,-1123056170092⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-166312374437,-164289209958⟩,⟨-966367641600,-962502171033⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨933199253339,935222417818⟩,⟨-966367641600,-962502171033⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-180322815680,-177941668160⟩,⟨-1138591201016,-1131583576962⟩,⟨-516667384995,-515044733825⟩,⟨-1179059766429,-1164591041424⟩,⟨757630172060,765395554863⟩,⟨-242785232984,-241262639829⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-153378950625,-151026171683⟩,⟨-812694246633,-801933142607⟩,⟨-368568225148,-365221141857⟩,⟨978270848963,1012995105196⟩,⟨1364438710197,1381292743517⟩,⟨203918049100,207353769781⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151026171683,153378950625⟩,⟨801933142607,812694246633⟩,⟨365221141857,368568225148⟩,⟨-1012995105196,-978270848963⟩,⟨-1381292743517,-1364438710197⟩,⟨-207353769781,-203918049100⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨461328006712,469537621631⟩,⟨1641594450086,1698958954886⟩,⟨748742566453,769427000234⟩,⟨-6879020001509,-6364594873584⟩,⟨-5039619790325,-4787619043785⟩,⟨-1408369182232,-1326974219192⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨821108776891,831206418011⟩,⟨4033787792071,4105297342559⟩,⟨748742566453,769427000234⟩,⟨-19055084836743,-18329004420786⟩,⟨-5039619790325,-4787619043785⟩,⟨-1408369182232,-1326974219192⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨105240120524,110145442942⟩,⟨-274018913486,-266287972352⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10975722529448,11487309341678⟩,⟨26534941613550,29910076204887⟩,⟨-95730996254180,-87308517567166⟩,⟨128301918082463,155756693229511⟩,⟨-279391811655491,-182123992613792⟩,⟨1389025136035327,1595573579718540⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8196604632439,8684151226117⟩,⟨60082865276510,65502052000961⟩,⟨-64896292163838,-57162782563149⟩,⟨91432251852879,158135125290108⟩,⟨-603231731222035,-483179609649645⟩,⟨888618461888385,1074061667172248⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨95962478592,101602457856⟩,⟨-802507922090,-656221005484⟩,⟨624328058877,795086367294⟩,⟨6971564539379,11619916537833⟩,⟨-7224582704049,-1085414046843⟩,⟨-5094968629345,2680790485902⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1195474106368,1201114085632⟩,⟨-802507922090,-656221005484⟩,⟨624328058877,795086367294⟩,⟨6971564539379,11619916537833⟩,⟨-7224582704049,-1085414046843⟩,⟨-5094968629345,2680790485902⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨92003550720,97178602752⟩,⟨-738089421612,-600711151880⟩,⟨571516035398,731263606021⟩,⟨5886367752954,10358973913680⟩,⟨-6332410607351,-502709886691⟩,⟨-5172337018620,2168530679034⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨100033378275,106158575898⟩,⟨-877222373057,-708050074572⟩,⟨673638187365,869109862600⟩,⟨7700516537712,13420651111816⟩,⟨-8623566921486,-1319604283400⟩,⟨-5451567437534,3663447992491⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-101602457856,-95962478592⟩,⟨656221005484,802507922090⟩,⟨-795086367294,-624328058877⟩,⟨-11619916537833,-6971564539379⟩,⟨1085414046843,7224582704049⟩,⟨-2680790485902,5094968629345⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨997909169920,1003549149184⟩,⟨656221005484,802507922090⟩,⟨-795086367294,-624328058877⟩,⟨-11619916537833,-6971564539379⟩,⟨1085414046843,7224582704049⟩,⟨-2680790485902,5094968629345⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-106607685824,-100410964928⟩,⟨718970890969,884215536162⟩,⟨-876038353267,-684028242005⟩,⟨-13514078962548,-8108342359154⟩,⟨1636490915803,8664656732419⟩,⟨-3651721592142,5188166882114⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-97303247827,-91132299223⟩,⟨574722555551,747115304553⟩,⟨-742564371877,-543728435816⟩,⟨-10839733768484,-4941682015007⟩,⟨-494021322864,6992808283491⟩,⟨-3050198631788,6262258133640⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2730130448,15026276675⟩,⟨-302499817506,39065229981⟩,⟨-68926184512,325381426784⟩,⟨-3139217230772,8478969096809⟩,⟨-9117588244350,5673204000091⟩,⟨-8501766069322,9925706126131⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1365065224,7513138338⟩,⟨-151249908753,19532614991⟩,⟨-34463092256,162690713392⟩,⟨-1569608615386,4239484548405⟩,⟨-4558794122175,2836602000046⟩,⟨-4250883034661,4962853063066⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7513138338,-1365065224⟩,⟨-19532614991,151249908753⟩,⟨-162690713392,34463092256⟩,⟨-4239484548405,1569608615386⟩,⟨-2836602000046,4558794122175⟩,⟨-4962853063066,4250883034661⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754610245278,760758337656⟩,⟨-19532614991,151249908753⟩,⟨-162690713392,34463092256⟩,⟨-4239484548405,1569608615386⟩,⟨-2836602000046,4558794122175⟩,⟨-4962853063066,4250883034661⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8375352351,9388767869⟩,⟨-148314533970,-114546481546⟩,⟨108979416808,146942928268⟩,⟨2000223723191,3318984536861⟩,⟨-2495832574306,-934698998718⟩,⟨-232604743978,1645343643435⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9388767869,-8375352351⟩,⟨114546481546,148314533970⟩,⟨-146942928268,-108979416808⟩,⟨-3318984536861,-2000223723191⟩,⟨934698998718,2495832574306⟩,⟨-1645343643435,232604743978⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090122859907,1091136275425⟩,⟨114546481546,148314533970⟩,⟨-146942928268,-108979416808⟩,⟨-3318984536861,-2000223723191⟩,⟨934698998718,2495832574306⟩,⟨-1645343643435,232604743978⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9429083072,-8407414208⟩,⟨115425718324,149591904423⟩,⟨-148208485661,-109815921867⟩,⟨-3367921983211,-2027694341711⟩,⟨953401942963,2537492342057⟩,⟨-1679492031458,223639985687⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4714541536,-4203707104⟩,⟨57712859162,74795952212⟩,⟨-74104242831,-54907960933⟩,⟨-1683960991606,-1013847170855⟩,⟨476700971481,1268746171029⟩,⟨-839746015729,111819992844⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4203707104,4714541536⟩,⟨-74795952212,-57712859162⟩,⟨54907960933,74104242831⟩,⟨1013847170855,1683960991606⟩,⟨-1268746171029,-476700971481⟩,⟨-111819992844,839746015729⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766327090720,766837944416⟩,⟨-74795952212,-57712859162⟩,⟨54907960933,74104242831⟩,⟨1013847170855,1683960991606⟩,⟨-1268746171029,-476700971481⟩,⟨-111819992844,839746015729⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272530714976,272784068857⟩,⟨28636620386,37078633493⟩,⟨-36735732067,-27244854202⟩,⟨-829746134216,-500055930797⟩,⟨233674749679,623958143577⟩,⟨-411335910859,58151185995⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532654181440,1533675888832⟩,⟨-149591904424,-115425718324⟩,⟨109815921866,148208485662⟩,⟨2027694341710,3367921983212⟩,⟨-2537492342058,-953401942962⟩,⟨-223639985688,1679492031458⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1204650335858,1211458774061⟩,⟨-974242238448,-787721114900⟩,⟨749437141591,965232492926⟩,⟨9398778182021,15673494686556⟩,⟨-10323081359247,-2283034355756⟩,⟨-5252797050471,4792574006253⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1309789043940,1323405920346⟩,⟨-1948484476896,-1575442229800⟩,⟨1498874283183,1930464985852⟩,⟨18797556364044,31346989373100⟩,⟨-20646162718487,-4566068711511⟩,⟨-10500810916851,9585148012503⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨192414515712,203786288576⟩,⟨-1635669002426,-1308908343178⟩,⟨1245294189482,1620542413896⟩,⟨13184104948855,24756267108101⟩,⟨-15849112052811,-1382808329592⟩,⟨-11203456129194,6635914096465⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨65860394450,70299317432⟩,⟨-557064735819,-436397141515⟩,⟨413451355863,553309398998⟩,⟨4172137302604,8213441686856⟩,⟨-5300129745419,-95553828569⟩,⟨-4219131615776,2297507442286⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379891698575,380498340077⟩,⟨2804652121,23109853499⟩,⟨-24022024107,-1207832571⟩,⟨-664882443741,132505960144⟩,⟨-298091790534,644021368782⟩,⟨-639147845860,492345774785⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177217065835,3182290700612⟩,⟨-193587467582,-23419257442⟩,⟨10085579496,201228571755⟩,⟨-1109635535666,5593164530098⟩,⟨-5419344371620,2496917552072⟩,⟨-4124236096557,5379486019480⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨190314284927,203465664639⟩,⟨-1624676765705,-1262443081064⟩,⟨1195338831152,1614296330659⟩,⟨12003710628133,24325742062343⟩,⟨-15885908321839,-129282577330⟩,⟨-12467439314629,7196098598504⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨382728800639,407251953215⟩,⟨-3260345768131,-2571351424242⟩,⟨2440633020634,3234838744555⟩,⟨25187815576988,49082009170444⟩,⟨-31735020374650,-1512090906922⟩,⟨-23670895443823,13832012694969⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517899590957,526373012975⟩,⟨-27029454416,209301341154⟩,⟨-225133256522,47690418388⟩,⟨-5872020708555,2213654399221⟩,⟨-3970081848280,6317992624938⟩,⟨-6877851176531,5930565710958⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355441750217,364200476123⟩,⟨-28052749453,217225179357⟩,⟨-233656467549,49495906863⟩,⟨-6099903997125,2340647619778⟩,⟨-4166837586713,6567022962513⟩,⟨-7148821281446,6205056345254⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨710883500434,728400952246⟩,⟨-56105498906,434450358714⟩,⟨-467312935098,98991813726⟩,⟨-12199807994250,4681295239556⟩,⟨-8333675173426,13134045925026⟩,⟨-14297642562892,12410112690508⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523265413571,1525300536481⟩,⟨-35045422878,32888815646⟩,⟨-37127006402,39229068854⟩,⟨-1291290195151,1367698260021⟩,⟨-1602793343340,1542430631344⟩,⟨-1868983629123,1912096775436⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨984859297468,1010476228871⟩,⟨-101049287858,624480535277⟩,⟨-672876938031,163315014737⟩,⟨-17807362091345,7426198836417⟩,⟨-12651375637370,19272461485085⟩,⟨-21105948534928,18514242144469⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67550891440,67676545061⟩,⟨14196045646,18398096494⟩,⟨-18227951780,-13506104724⟩,⟨-410221165263,-245392175723⟩,⟨113362031434,308183445040⟩,⟨-202751109740,31308866048⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50446605972,51161967898⟩,⟨258426060927,266595594875⟩,⟨32220702738,37273075508⟩,⟨-1378824073729,-1171952084230⟩,⟨-283929216682,-97833112701⟩,⟨-265473991583,-76251446491⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136429284187,2139278632954⟩,⟨-417322547910,-321793249594⟩,⟨306153800622,413463168990⟩,⟨5677206550816,9436332182284⟩,⟨-7119272800508,-2681028592884⟩,⟨-601961286764,4725301895371⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2978056068750,2984015790258⟩,⟨-873166113154,-672841137497⟩,⟨640140437126,865091114793⟩,⟨11921207591502,19828853357942⟩,⟨-14980070477145,-5654002560454⟩,⟨-1213630303648,9970372504363⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136635954788,138850846332⟩,⟨659323998130,692655624313⟩,⟨116640850798,141411155448⟩,⟨-3618527284416,-2567881190186⟩,⟨-1346757713344,-334355416495⟩,⟨-739436243705,316060330000⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8706650708660,8847786964203⟩,⟨-44852538359963,-41342951139302⟩,⟨-9157002486696,-7313971596765⟩,⟨553647646336898,689062294051670⟩,⟨90425590815089,180048684306798⟩,⟨-8178195710056,66835841095047⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7798758724884,8131317741065⟩,⟨-42033649505465,-32006682044888⟩,⟨-13830144909065,-5237103750952⟩,⟨301670489998650,701266915465348⟩,⟨-32672374234568,348844965885404⟩,⟨-180076095299835,221615819601226⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15597517449768,16262635482130⟩,⟨-84067299010930,-64013364089776⟩,⟨-27660289818130,-10474207501904⟩,⟨603340979997300,1402533830930696⟩,⟨-65344748469136,697689931770808⟩,⟨-360152190599670,443231639202452⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10825960642717,10867759718598⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790014,2123491006166466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9726449014941,9768248090822⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790024,2123491006166451⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2396916401408,2401631448192⟩,⟨-12142992897062,-11998203029636⟩,⟨0,0⟩,⟨102165241571294,109118793444233⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7269007033944,7358522327326⟩,⟨-43283657331711,-42068036579410⟩,⟨-19641161838097,-19147432981269⟩,⟨486921994539991,509198697421003⟩,⟨269680771117562,280310236816221⟩,⟨100873252167784,104851278881821⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6169495406168,6259010699550⟩,⟨-43283657331712,-42068036579410⟩,⟨-19641161838097,-19147432981269⟩,⟨486921994539999,509198697421001⟩,⟨269680771117565,280310236816221⟩,⟨100873252167784,104851278881821⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1896383718080,1912222314752⟩,⟨-7713902255519,-7390032961595⟩,⟨-3500397423508,-3363602686671⟩,⟨31418068919861,41078225528827⟩,⟨22816518146407,27348738225246⟩,⟨6576422253780,8396463554315⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99941875711,100371372442⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139438787359,141461951839⟩,⟨670740892283,678155593976⟩,⟨305491525040,307534021265⟩,⟨-1698693120000,-1685130754127⟩,⟨-1541762396982,-1533880796442⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4293300119488,4313853762944⟩,⟨-19856895152581,-19388235991231⟩,⟨-3500397423508,-3363602686671⟩,⟨133583310491155,150197018973060⟩,⟨22816518146407,27348738225246⟩,⟨6576422253780,8396463554315⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨765457601278,814503906430⟩,⟨-6520691536262,-5142702848484⟩,⟨4881266041268,6469677489110⟩,⟨50375631153976,98164018340888⟩,⟨-63470040749300,-3024181813844⟩,⟨-47341790887646,27664025389938⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5058757720766,5128357669374⟩,⟨-26377586688843,-24530938839715⟩,⟨1380868617760,3106074802439⟩,⟨183958941645131,248361037313948⟩,⟨-40653522602893,24324556411402⟩,⟨-40765368633866,36060488944253⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459823909642,468153573501⟩,⟨1623260697692,1860887453791⟩,⟨125516271299,283544969378⟩,⟨-35615965582686,-26541507721960⟩,⟨-2610767847156,4698101390078⟩,⟨-3721357641449,3291862200299⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38790128095,40880342192⟩,⟨-827441725004,-785142304155⟩,⟨322945996948,325509439814⟩,⟨9669634184997,10403523578417⟩,⟨-6594864009033,-6530061933853⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨498614037737,509033915693⟩,⟨795818972688,1075745149636⟩,⟨448462268247,609054409192⟩,⟨-25946331397689,-16137984143543⟩,⟨-9205631856189,-1831960543775⟩,⟨-3721357641449,3291862200299⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503376910943,504367118897⟩,⟨2514798172912,2555168940688⟩,⟨0,0⟩,⟨2165995870996,4475808627517⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨228274797399,233503641975⟩,⟨1504768594923,1676415316002⟩,⟨205314382824,279384964975⟩,⟨-7279443042601,-316257707321⟩,⟨-3197079353528,576683551174⟩,⟨-1707058283504,1510040468721⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-814503906430,-765457601278⟩,⟨5142702848484,6520691536262⟩,⟨-6469677489110,-4881266041268⟩,⟨-98164018340888,-50375631153976⟩,⟨3024181813844,63470040749300⟩,⟨-27664025389938,47341790887646⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3478796213058,3548396161666⟩,⟨-14714192304097,-12867544454969⟩,⟨-9970074912618,-8244868727939⟩,⟨35419292150267,99821387819084⟩,⟨25840699960251,90818778974546⟩,⟨-21087603136158,55738254441961⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441176894508,456532731667⟩,⟨229076716045,556728911387⟩,⟨-316179918345,-53116270209⟩,⟨-19141076922128,-8188066775102⟩,⟨-11963461209222,-1773290346111⟩,⟨-9419222138888,1485130618960⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨328578419916,332624748874⟩,⟨1925004342066,1932735283200⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-332624748874,-328578419916⟩,⟨-1932735283200,-1925004342066⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨766886878902,770933207860⟩,⟨-1932735283200,-1925004342066⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1322688868421,1340773163296⟩,⟨-8770005431879,-8474549944755⟩,⟨-3979633575982,-3857224874455⟩,⟨47790122965344,55921582589627⟩,⟨31484687351504,35306361534923⟩,⟨9947661837237,11471489362558⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1340773163296,-1322688868421⟩,⟨8474549944755,8770005431879⟩,⟨3857224874455,3979633575982⟩,⟨-55921582589627,-47790122965344⟩,⟨-35306361534923,-31484687351504⟩,⟨-11471489362558,-9947661837237⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-241261535520,-223177240645⟩,⟨8474549944755,8770005431879⟩,⟨3857224874455,3979633575982⟩,⟨-55921582589627,-47790122965344⟩,⟨-35306361534923,-31484687351504⟩,⟨-11471489362558,-9947661837237⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12084391845,-10680741844⟩,⟨432597549869,469338536608⟩,⟨88375893940,110411091200⟩,⟨-4986669502511,-4339553808448⟩,⟨1335418744675,1765116881656⟩,⟨2499138116085,2698307716756⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429092502663,445851989823⟩,⟨661674265914,1026067447995⟩,⟨-227804024405,57294820991⟩,⟨-24127746424639,-12527620583550⟩,⟨-10628042464547,-8173464455⟩,⟨-6920084022803,4183438335716⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100371372442,-99941875711⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4782984908,5027436272⟩,⟨29424396533,31826763975⟩,⟨39820591103,40030926275⟩,⟨-328718341903,-317438348492⟩,⟨248728938086,249843280775⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10426824677,10981283645⟩,⟨8621733022,17324903859⟩,⟨86808202403,87438394478⟩,⟨-976569787531,-835248257382⟩,⟨100123741306,111191132797⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1454423105282,1472308972500⟩,⟨-7361102794588,-7058215672380⟩,⟨-1379639711584,-1310130029027⟩,⟨100577683402043,107773788746802⟩,⟨21093192269551,22831980909507⟩,⟨4682209040756,5110916837184⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13792500544,14704567039⟩,⟨-62113676917,-43735022653⟩,⟨101049991191,104660863704⟩,⟨-585866824285,-139168990002⟩,⟨-274656335838,-190606847355⟩,⟨-175028971999,-155828854979⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14704567039,-13792500544⟩,⟨43735022653,62113676917⟩,⟨-104660863704,-101049991191⟩,⟨139168990002,585866824285⟩,⟨190606847355,274656335838⟩,⟨155828854979,175028971999⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115075939481,-113734376255⟩,⟨-833297299191,-814059651467⟩,⟨-104660863704,-101049991191⟩,⟨2338192245554,2784890079837⟩,⟨190606847355,274656335838⟩,⟨155828854979,175028971999⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨90756498616,95780057501⟩,⟨-624657451126,-583309945178⟩,⟨580261262019,601673866391⟩,⟨3293369057097,3979989549287⟩,⟨-3489486919837,-3034814512762⟩,⟨-2477381662552,-2259805899186⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨120051798641,128254976558⟩,⟨-1477688437234,-1354199778424⟩,⟨647381435258,697534249267⟩,⟨20147386048083,23081783570370⟩,⟨-6264626727348,-4966625793875⟩,⟨-4440804942302,-3926857437166⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-128254976558,-120051798641⟩,⟨1354199778424,1477688437234⟩,⟨-697534249267,-647381435258⟩,⟨-23081783570370,-20147386048083⟩,⟨4966625793875,6264626727348⟩,⟨3926857437166,4440804942302⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨971256651218,979459829135⟩,⟨1354199778424,1477688437234⟩,⟨-697534249267,-647381435258⟩,⟨-23081783570370,-20147386048083⟩,⟨4966625793875,6264626727348⟩,⟨3926857437166,4440804942302⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123173640222,126016220000⟩,⟨764238873506,794227937827⟩,⟨180112801180,191855304030⟩,⟨-2830676288286,-2220818871489⟩,⟨-797530677631,-530573138873⟩,⟨-203795294267,-96770370461⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11764776301,12043957984⟩,⟨168413983726,174427386032⟩,⟨20905386406,21907812366⟩,⟨622493232835,779348833434⟩,⟨92139789062,119207587272⟩,⟨-18063515509,-12313105310⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨166893463435,178139542601⟩,⟨1468230978238,1894974128254⟩,⟨-6427616549,211959612471⟩,⟨-11386653304811,7280353389711⟩,⟨-5471793065261,6584151050816⟩,⟨-5314515054423,4282150852809⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178139542601,-166893463435⟩,⟨-1894974128254,-1468230978238⟩,⟨-211959612471,6427616549⟩,⟨-7280353389711,11386653304811⟩,⟨-6584151050816,5471793065261⟩,⟨-4282150852809,5314515054423⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50135254798,66610178540⟩,⟨-390205533331,208184337764⟩,⟨-6645229647,285812581524⟩,⟨-14559796432312,11070395597490⟩,⟨-9781230404344,6048476616435⟩,⟨-5989209136313,6824555523144⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26901832947449,28283261113399⟩,⟨-260300790283433,-215241079306193⟩,⟨-99879171797360,-65780994342129⟩,⟨2346797946615795,4226395096011342⟩,⟨476254732236945,2079594692839992⟩,⟨-468983716675959,1071157450165253⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13798622281,14442855630⟩,⟨171228901396,182054650474⟩,⟨40354551622,43977488898⟩,⟨413547113355,649837006768⟩,⟨67570732330,158296129600⟩,⟨12294746758,45272643347⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337611919811,371520452069⟩,⟨770237026418,1981851586210⟩,⟨-324625081985,305717282953⟩,⟨-46629961608924,5192975423437⟩,⟨-19318947227547,13244836777035⟩,⟨-13849406265834,10406352283974⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371520452069,-337611919811⟩,⟨-1981851586210,-770237026418⟩,⟨-305717282953,324625081985⟩,⟨-5192975423437,46629961608924⟩,⟨-13244836777035,19318947227547⟩,⟨-10406352283974,13849406265834⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57572050594,108240070012⟩,⟨-1320177320296,255830421577⟩,⟨-533521307358,381919902976⟩,⟨-29320721848076,34102341025374⟩,⟨-23872879241582,19310773763092⟩,⟨-17326436306777,18032844601550⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239380663070,241833324281⟩,⟨1546914220667,1555187915820⟩,⟨305491525040,307534021265⟩,⟨-3897716375552,-3884154009679⟩,⟨-1541762396982,-1533880796442⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1702062997123,-1613419879755⟩,⟨-5703523300556,-2749571836461⟩,⟨-464555358730,1461471434813⟩,⟨-18832461298179,106206378977093⟩,⟨-56678937791300,39866831791063⟩,⟨-42253229232861,45548571238366⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-195075285865,-180744609493⟩,⟨-1883165560935,-1429464613051⟩,⟨-350238518950,-96796127917⟩,⟨-7139421875942,12732067643688⟩,⟨-7048258599385,6409048418853⟩,⟨-4862809701465,6045878122800⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44305377205,61088714788⟩,⟨-336251340268,125723302769⟩,⟨-44746993910,210737893348⟩,⟨-11037138251494,8847913634009⟩,⟨-8590020996367,4875167622411⟩,⟨-5212594857951,5696777812272⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2625155889,6557357109⟩,⟨-118391764097,35993068517⟩,⟨-32975758278,51273788595⟩,⟨-3709549114074,4092821117939⟩,⟨-2887871559988,2021155651201⟩,⟨-1916636062012,1962849994862⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1785307585,3394080591⟩,⟨-37364156420,13970338816⟩,⟨-4972273654,23417136730⟩,⟨-1303340868220,1188841699859⟩,⟨-1083415994352,589920797940⟩,⟨-596374971453,713806538766⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3079210942,5902835842⟩,⟨-88794131084,12297197582⟩,⟨-19452930786,35264480188⟩,⟨-2411723682051,2718660958751⟩,⟨-2055946406005,1264223615341⟩,⟨-1175612089349,1298999389840⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5902835842,-3079210942⟩,⟨-12297197582,88794131084⟩,⟨-35264480188,19452930786⟩,⟨-2718660958751,2411723682051⟩,⟨-1264223615341,2055946406005⟩,⟨-1298999389840,1175612089349⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3277679953,3478146167⟩,⟨-130688961679,124787199601⟩,⟨-68240238466,70726719381⟩,⟨-6428210072825,6504544799990⟩,⟨-4152095175329,4077102057206⟩,⟨-3215635451852,3138462084211⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50135254798,66610178540⟩,⟨-390205533331,208184337764⟩,⟨-6645229647,285812581524⟩,⟨-14559796432312,11070395597490⟩,⟨-9781230404344,6048476616435⟩,⟨-5989209136313,6824555523144⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3277679953,3478146167⟩,⟨-130688961679,124787199601⟩,⟨-68240238466,70726719381⟩,⟨-6428210072825,6504544799990⟩,⟨-4152095175329,4077102057206⟩,⟨-3215635451852,3138462084211⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (519/5120) u, BivariateJet2.affineZ (629/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000030

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000031Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2073215209536,-2073215170880⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2073215209536,-2073215170816⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-180946203008,-180946202944⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-180946203008,-180946202944⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨96844514112,96844514176⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-106205701120,-106205701056⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨96844636288,96844636352⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-106205848064,-106205848000⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-9361211776,-9361211712⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-9361186944,-9361186880⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨203050215232,203050215296⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨203050484288,203050484352⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2399271880896,2399271938752⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1892268967872,1892269006464⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1892268967936,1892269006528⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2518909148928,-2518909091072⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117277700736,-117277700672⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2079904497152,-2079904458496⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2066561427328,-2066561388608⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-182140726464,-182140726400⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-179753864960,-179753864896⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨94269086528,94269086592⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-103115882752,-103115882688⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨99441345728,99441345792⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-109337382720,-109337382656⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9896036928,-9896036864⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8846796160,-8846796096⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨197384969216,197384969280⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨208778728448,208778728512⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2401631390336,2401631448192⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1884420662208,1884420700800⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1900150593536,1900150632128⟩



end LaneCBRB2Cell000031Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000031
open Set LaneCBRB2Cell000031Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111454401331,111454401332⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨138942192025,138942192026⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111454401332,-111454401331⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438301412556,438301412557⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨55386916781,55386916783⟩,⟨-138942192026,-138942192025⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨166841318112,166841318115⟩,⟨960569435750,960569435751⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨55386916780,55386916784⟩,⟨-138942192026,-138942192025⟩,⟨438301412556,438301412557⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2073215209536,-2073215170816⟩,⟨6330309996504,6330309996626⟩,⟨2888478136115,2888478136175⟩,⟨-36446021707320,-36446021705923⟩,⟨-23876037891198,-23876037890409⟩,⟨-7588192550575,-7588192550264⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-314592360424,-314592354542⟩,⟨-850659398694,-850659364827⟩,⟨-388150197349,-388150181893⟩,⟨5530366526027,5530366526566⟩,⟨3497172820816,3497172859834⟩,⟨1151442163194,1151442163317⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨314592354542,314592360424⟩,⟨850659364827,850659398694⟩,⟨388150181893,388150197349⟩,⟨-5530366526566,-5530366526027⟩,⟨-3497172859834,-3497172820816⟩,⟨-1151442163317,-1151442163194⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-166841318115,-166841318112⟩,⟨-960569435751,-960569435750⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨932670309661,932670309664⟩,⟨-960569435751,-960569435750⟩,⟨-438301412557,-438301412556⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-180946203008,-180946202944⟩,⟨-1132401506679,-1132401506673⟩,⟨-516707237902,-516707237897⟩,⟨-1166275226142,-1166275226128⟩,⟨764034870917,764034870930⟩,⟨-242822688688,-242822688683⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-153489191864,-153489191808⟩,⟨-802488895566,-802488895500⟩,⟨-366170318770,-366170318736⟩,⟨989303113142,989303113171⟩,⟨1369977822241,1369977822329⟩,⟨205976459477,205976459489⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨153489191808,153489191864⟩,⟨802488895500,802488895566⟩,⟨366170318736,366170318770⟩,⟨-989303113171,-989303113142⟩,⟨-1369977822329,-1369977822241⟩,⟨-205976459489,-205976459477⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨468081546350,468081552288⟩,⟨1653148260327,1653148294260⟩,⟨754320500629,754320516119⟩,⟨-6519669639737,-6519669639169⟩,⟨-4867150682163,-4867150643057⟩,⟨-1357418622806,-1357418622671⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨828805636003,828805647867⟩,⟨4052420141147,4052420233024⟩,⟨754320500629,754320516119⟩,⟨-18590027811730,-18590027810656⟩,⟨-4867150682163,-4867150643057⟩,⟨-1357418622806,-1357418622671⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨110773833560,110773833568⟩,⟨-277884384052,-277884384050⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10913460161803,10913460162592⟩,⟨27377224902621,27377224906777⟩,⟨-86363085061200,-86363085048514⟩,⟨137355601661879,137355601693650⟩,⟨-216648209511644,-216648209382225⟩,⟨1366859336730247,1366859337032957⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8226504442424,8226504560779⟩,⟨60860042200792,60860043414189⟩,⟨-57612820394839,-57612819299105⟩,⟨120824192033378,120824198169438⟩,⟨-511140593528258,-511140583049422⟩,⟨898358570382160,898358587812190⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨101237552640,101237686016⟩,⟨-739830948232,-739828953267⟩,⟨700354949742,700356837621⟩,⟨9278062487389,9278111041010⟩,⟨-3959927465840,-3959868545851⟩,⟨-1290066124638,-1289996779548⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1200749180416,1200749313792⟩,⟨-739830948232,-739828953267⟩,⟨700354949742,700356837621⟩,⟨9278062487389,9278111041010⟩,⟨-3959927465840,-3959868545851⟩,⟨-1290066124638,-1289996779548⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨96844514112,96844636352⟩,⟨-677454328879,-677452426862⟩,⟨641306559134,641308359079⟩,⟨8078402163131,8078449910623⟩,⟨-3230923867743,-3230867294243⟩,⟨-1555351799865,-1555286070493⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨105761474467,105761619711⟩,⟨-804995106293,-804992688999⟩,⟨762041836504,762044124121⟩,⟨10551104487283,10551167937158⟩,⟨-4740238087225,-4740165533439⟩,⟨-995204704962,-995121988278⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-101237686016,-101237552640⟩,⟨739828953267,739830948232⟩,⟨-700356837621,-700354949742⟩,⟨-9278111041010,-9278062487389⟩,⟨3959868545851,3959927465840⟩,⟨1289996779548,1290066124638⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨998273941760,998274075136⟩,⟨739828953267,739830948232⟩,⟨-700356837621,-700354949742⟩,⟨-9278111041010,-9278062487389⟩,⟨3959868545851,3959927465840⟩,⟨1289996779548,1290066124638⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-106205848064,-106205701056⟩,⟨814856918498,814859224650⟩,⟨-771381936706,-771379754308⟩,⟨-10822930053840,-10822871792709⟩,⟨4933124789556,4933193502820⟩,⟨879641968881,879721598474⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-96426942719,-96426796363⟩,⟨668365878225,668368362505⟩,⟨-632707179664,-632704828639⟩,⟨-7833621454389,-7833555253846⟩,⟨3058319648260,3058394590054⟩,⟨1656726769311,1656811473678⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨9334531748,9334823348⟩,⟨-136629228068,-136624326494⟩,⟨129334656840,129339295482⟩,⟨2717483032894,2717612683312⟩,⟨-1681918438965,-1681770943385⟩,⟨661522064349,661689485400⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4667265874,4667411674⟩,⟨-68314614034,-68312163247⟩,⟨64667328420,64669647741⟩,⟨1358741516447,1358806341656⟩,⟨-840959219483,-840885471692⟩,⟨330761032174,330844742700⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4667411674,-4667265874⟩,⟨68312163247,68314614034⟩,⟨-64669647741,-64667328420⟩,⟨-1358806341656,-1358741516447⟩,⟨840885471692,840959219483⟩,⟨-330844742700,-330761032174⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757455971942,757456137006⟩,⟨68312163247,68314614034⟩,⟨-64669647741,-64667328420⟩,⟨-1358806341656,-1358741516447⟩,⟨840885471692,840959219483⟩,⟨-330844742700,-330761032174⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨9321449455,9321474018⟩,⟨-136240074866,-136239528002⟩,⟨128970388852,128970906420⟩,⟨2704173711309,2704190272842⟩,⟨-1671723215098,-1671706322196⟩,⟨654642911033,654660804009⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9321474018,-9321449455⟩,⟨136239528002,136240074866⟩,⟨-128970906420,-128970388852⟩,⟨-2704190272842,-2704173711309⟩,⟨1671706322196,1671723215098⟩,⟨-654660804009,-654642911033⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090190153758,1090190178321⟩,⟨136239528002,136240074866⟩,⟨-128970906420,-128970388852⟩,⟨-2704190272842,-2704173711309⟩,⟨1671706322196,1671723215098⟩,⟨-654660804009,-654642911033⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9361211776,-9361186880⟩,⟨137404416385,137404971021⟩,⟨-130073648863,-130073123938⟩,⟨-2744483338010,-2744466434793⟩,⟨1702254961927,1702272168473⟩,⟨-675646244020,-675628058977⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4680605888,-4680593440⟩,⟨68702208192,68702485511⟩,⟨-65036824432,-65036561969⟩,⟨-1372241669005,-1372233217396⟩,⟨851127480963,851136084237⟩,⟨-337823122010,-337814029488⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4680593440,4680605888⟩,⟨-68702485511,-68702208192⟩,⟨65036561969,65036824432⟩,⟨1372233217396,1372241669005⟩,⟨-851136084237,-851127480963⟩,⟨337814029488,337823122010⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766803977056,766804008768⟩,⟨-68702485511,-68702208192⟩,⟨65036561969,65036824432⟩,⟨1372233217396,1372241669005⟩,⟨-851136084237,-851127480963⟩,⟨337814029488,337823122010⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272547538439,272547544581⟩,⟨34059882000,34060018717⟩,⟨-32242726605,-32242597213⟩,⟨-676047568211,-676043427827⟩,⟨417926580549,417930803775⟩,⟨-163665201003,-163660727758⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533607954112,1533608017536⟩,⟨-137404971022,-137404416384⟩,⟨130073123938,130073648864⟩,⟨2744466434792,2744483338010⟩,⟨-1702272168474,-1702254961926⟩,⟨675628058976,675646244020⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1211015942139,1211016103940⟩,⟨-897496323427,-897493663490⟩,⟨849607367773,849609885007⟩,⟨12585586957080,12585656573038⟩,⟨-6063136632219,-6063056577066⟩,⟨-372881174997,-372789728849⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1322520256502,1322520580104⟩,⟨-1794992646855,-1794987326981⟩,⟨1699214735546,1699219770015⟩,⟨25171173914171,25171313146072⟩,⟨-12126273264436,-12126113154137⟩,⟨-745762205383,-745579602309⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨203050215232,203050484352⟩,⟨-1492313843428,-1492309055463⟩,⟨1412686039013,1412690570216⟩,⟨18901260024426,18901393895907⟩,⟨-8164128667368,-8163980787019⟩,⟨-2435082522459,-2434918915290⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨69742772058,69742879141⟩,⟨-503381430338,-503379710991⟩,⟨476521594162,476523221265⟩,⟨6174631287642,6174675808854⟩,⟨-2563553289605,-2563501856353⟩,⟨-1001577510940,-1001518620752⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380151571174,380151595464⟩,⟨13446986927,13447317840⟩,⟨-12729828343,-12729515159⟩,⟨-271169875745,-271159787860⟩,⟨169025933193,169036187443⟩,⟨-68435254685,-68424433028⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3180115075247,3180115278444⟩,⟨-112492027286,-112489244694⟩,⟨106487315956,106489949471⟩,⟨2276314560571,2276399632729⟩,⟨-1421587102806,-1421500769149⟩,⟨579528370842,579619323635⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨201716867023,201717189629⟩,⟨-1463064559509,-1463059306158⟩,⟨1384996927188,1385001898739⟩,⟨18106260664733,18106399092023⟩,⟨-7602239463421,-7602081870091⟩,⟨-2767798849986,-2767619913400⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨404767082255,404767673981⟩,⟨-2955378402937,-2955368361621⟩,⟨2797682966201,2797692468955⟩,⟨37007520689159,37007792987930⟩,⟨-15766368130789,-15766062657110⟩,⟨-5202881372445,-5202538828690⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨521813080404,521813307831⟩,⟨94120798180,94124195398⟩,⟨-89102143756,-89098928766⟩,⟨-1863681338079,-1863591004562⟩,⟨1150539610948,1150642049968⟩,⟨-448232671971,-448116690252⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359478175586,359478410599⟩,⟨97260036453,97263568176⟩,⟨-92074013459,-92070671172⟩,⟨-1917070138128,-1916975739433⟩,⟨1180609779473,1180716493021⟩,⟨-455322331966,-455201814233⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨718956351172,718956821198⟩,⟨194520072906,194527136352⟩,⟨-184148026918,-184141342344⟩,⟨-3834140276256,-3833951478866⟩,⟨2361219558946,2361432986042⟩,⟨-910644663932,-910403628466⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524286480094,1524286568081⟩,⟨-1165443020,-1164341518⟩,⟨1102217518,1103260012⟩,⟨40276161950,40309626701⟩,⟨-30565846278,-30531746828⟩,⟨20967254967,21003332987⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨996711101715,996711810861⟩,⟨268907037050,268917565645⟩,⟨-254569311151,-254559347240⟩,⟨-5289462152531,-5289177806015⟩,⟨3253834014137,3254152776934⟩,⟨-1249113861115,-1248755670899⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67559231601,67559234647⟩,⟨16885564034,16885632194⟩,⟨-15984689466,-15984624956⟩,⟨-333047917910,-333045840773⟩,⟨205194142662,205196257080⟩,⟨-79247845119,-79245610450⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50925766040,50925769066⟩,⟨261728238454,261728306889⟩,⟨34299876000,34299927844⟩,⟨-1268840830408,-1268838704260⟩,⟨-191716449064,-191714551028⟩,⟨-165075455957,-165073677886⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2139089116931,2139089293861⟩,⟨-383307206374,-383305643292⟩,⟨362854148056,362855627406⟩,⟨7690351645271,7690399392648⟩,⟨-4781197297334,-4781148838842⟩,⟨1915518774398,1915569830048⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2983619273690,2983619643866⟩,⟨-801960147612,-801956844146⟩,⟨759167970920,759171097431⟩,⟨16161701307262,16161802453377⟩,⟨-10071299596688,-10071197245661⟩,⟨4072061166750,4072168674129⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨138191441769,138191467126⟩,⟨673077901813,673078330848⟩,⟨128237826711,128238125843⟩,⟨-3076350140162,-3076337541707⟩,⟨-831013603979,-831002688309⟩,⟨-211976661654,-211966523871⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8748194405609,8748196010832⟩,⟨-42609159391687,-42609116594807⟩,⟨-8118102297621,-8118080381892⟩,⟨609812676688370,609814303329615⟩,⟨131686669718216,131687658443917⟩,⟨28485219895621,28485945175597⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7930268551746,7930275649163⟩,⟨-36485836407706,-36485685968085⟩,⟨-9384558028714,-9384453277258⟩,⟨489869408087574,489874383018191⟩,⟨153142706744427,153146708062679⟩,⟨19642455748533,19646140613481⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15860537103492,15860551298326⟩,⟨-72971672815412,-72971371936170⟩,⟨-18769116057428,-18768906554516⟩,⟨979738816175148,979748766036382⟩,⟨306285413488854,306293416125358⟩,⟨39284911497066,39292281226962⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10846819911700,10846819911799⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738054,2111240126795878⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9747308283924,9747308284023⟩,⟨-107005236895020,-107005236893066⟩,⟨0,0⟩,⟨2111240126738069,2111240126795861⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2399271880896,2399271938752⟩,⟨-12070358171930,-12070358171514⟩,⟨0,0⟩,⟨105643681588589,105643681622780⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7245961811338,7245961811469⟩,⟨-41717780268580,-41717780267026⟩,⟨-19035544271889,-19035544271155⟩,⟨480370511388756,480370511415826⟩,⟨266941929065578,266941929079931⟩,⟨100014864867810,100014864873696⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6146450183562,6146450183693⟩,⟨-41717780268581,-41717780267026⟩,⟨-19035544271889,-19035544271154⟩,⟨480370511388757,480370511415823⟩,⟨266941929065578,266941929079931⟩,⟨100014864867809,100014864873696⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1892268967872,1892269006528⟩,⟨-7462711503474,-7462711503006⟩,⟨-3405185374154,-3405185373935⟩,⟨35279746472733,35279746487871⟩,⟨24640072757885,24640072765401⟩,⟨7345369860070,7345369863321⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100156582133,100156582135⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨141524600465,141524600469⟩,⟨669053335777,669053335785⟩,⟨305284564792,305284564797⟩,⟨-1678369955515,-1678369955510⟩,⟨-1531657983104,-1531657983092⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4291540848768,4291540945280⟩,⟨-19533069675404,-19533069674520⟩,⟨-3405185374154,-3405185373935⟩,⟨140923428061322,140923428110651⟩,⟨24640072757885,24640072765401⟩,⟨7345369860070,7345369863321⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨809534164510,809535347962⟩,⟨-5910756805874,-5910736723242⟩,⟨5595365932402,5595384937910⟩,⟨74015041378318,74015585975860⟩,⟨-31532736261578,-31532125314220⟩,⟨-10405762744890,-10405077657380⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5101075013278,5101076293242⟩,⟨-25443826481278,-25443806397762⟩,⟨2190180558248,2190199563975⟩,⟨214938469439640,214939014086511⟩,⟨-6892663503693,-6892052548819⟩,⟨-3060392884820,-3059707794059⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨464666517049,464666633653⟩,⟨1749185749710,1749188599684⟩,⟨199507666337,199509397609⟩,⟨-31193979593454,-31193895396339⟩,⟨1118289989361,1118360795021⟩,⟨-278776943864,-278714537652⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨40971546881,40971549209⟩,⟨-829266760020,-829266748289⟩,⟨324226151534,324226169925⟩,⟨10319838491985,10319838523297⟩,⟨-6562358286202,-6562358193788⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨505638063930,505638182862⟩,⟨919918989690,919921851395⟩,⟨523733817871,523735567534⟩,⟨-20874141101469,-20874056873042⟩,⟨-5444068296841,-5443997398767⟩,⟨-278776943864,-278714537652⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503871945521,503871957673⟩,⟨2534900173993,2534900296365⟩,⟨0,0⟩,⟨3319096918590,3319099843609⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨231718181568,231718241660⟩,⟨1587307803938,1587309456009⟩,⟨240010902185,240011709790⟩,⟨-3797892520724,-3797838586621⟩,⟨-1287390118149,-1287353475498⟩,⟨-127754796685,-127726194779⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-809535347962,-809534164510⟩,⟨5910736723242,5910756805874⟩,⟨-5595384937910,-5595365932402⟩,⟨-74015585975860,-74015041378318⟩,⟨31532125314220,31532736261578⟩,⟨10405077657380,10405762744890⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3482005500806,3482006780770⟩,⟨-13622332952162,-13622312868646⟩,⟨-9000570312064,-9000551306337⟩,⟨66907842085462,66908386732333⟩,⟨56172198072105,56172809026979⟩,⟨17750447517450,17751132608211⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨448189382330,448189547096⟩,⟨365391467309,365394831312⟩,⟨-191721104322,-191718302545⟩,⟨-13281464409611,-13281367908971⟩,⟨-6879459007606,-6879361443330⟩,⟨-3819975121384,-3819875978320⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨333682636224,333682636230⟩,⟨1921138871500,1921138871502⟩,⟨876602825112,876602825114⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-333682636230,-333682636224⟩,⟨-1921138871502,-1921138871500⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨765828991546,765828991552⟩,⟨-1921138871502,-1921138871500⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1317998281046,1317998307982⟩,⟨-8504205078434,-8504205010519⟩,⟨-3880411930491,-3880411899495⟩,⟨50651636205331,50651636217731⟩,⟨32846304303311,32846304386771⟩,⟨10545852483221,10545852485888⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1317998307982,-1317998281046⟩,⟨8504205010519,8504205078434⟩,⟨3880411899495,3880411930491⟩,⟨-50651636217731,-50651636205331⟩,⟨-32846304386771,-32846304303311⟩,⟨-10545852485888,-10545852483221⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-218486680206,-218486653270⟩,⟨8504205010519,8504205078434⟩,⟨3880411899495,3880411930491⟩,⟨-50651636217731,-50651636205331⟩,⟨-32846304386771,-32846304303311⟩,⟨-10545852485888,-10545852483221⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11006071486,-11006070128⟩,⟨456001280081,456001286939⟩,⟨108376325797,108376338112⟩,⟨-4700835916300,-4700835898309⟩,⟨1463581809039,1463581871304⟩,⟨2562481112947,2562481137841⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437183310844,437183476968⟩,⟨821392747390,821396118251⟩,⟨-83344778525,-83341964433⟩,⟨-17982300325911,-17982203807280⟩,⟨-5415877198567,-5415779572026⟩,⟨-1257494008437,-1257394840479⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100156582135,-100156582133⟩,⟨-876602825114,-876602825112⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨5045298421,5045298422⟩,⟨31501579228,31501579234⟩,⟨39925700025,39925700027⟩,⟨-332321500698,-332321500686⟩,⟨249286067484,249286067488⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨11009472138,11009472407⟩,⟨13353468791,13353470477⟩,⟨87122870713,87122872820⟩,⟨-932046932607,-932046914682⟩,⟨105671963339,105671976504⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1458636077982,1458636098863⟩,⟨-7131957340641,-7131956974744⟩,⟨-1327547843704,-1327547778432⟩,⟨102460037107952,102460044204347⟩,⟨21547831246311,21547832678856⟩,⟨4805436347918,4805436619586⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14605405576,14605406143⟩,⟨-53697691516,-53697683614⟩,⟨102286286241,102286291671⟩,⟨-383769603578,-383769435211⟩,⟨-225297114765,-225297030184⟩,⟨-162266811746,-162266792416⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14605406143,-14605405576⟩,⟨53697683614,53697691516⟩,⟨-102286291671,-102286286241⟩,⟨383769435211,383769603578⟩,⟨225297030184,225297114765⟩,⟨162266792416,162266811746⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114761988278,-114761987709⟩,⟨-822905141500,-822905133596⟩,⟨-102286291671,-102286286241⟩,⟨2582792690763,2582792859130⟩,⟨225297030184,225297114765⟩,⟨162266792416,162266811746⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨95321360139,95321362094⟩,⟨-615048142843,-615048137903⟩,⟨582787327039,582787342477⟩,⟨3663269463922,3663269464947⟩,⟨-3195625312981,-3195625273628⟩,⟨-2344820795645,-2344820795273⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨126455392911,126455397316⟩,⟨-1434236138991,-1434236076352⟩,⟨658047567688,658047607257⟩,⟨21721462703051,21721464044822⟩,⟨-5408941918743,-5408941306781⟩,⟨-4101398816452,-4101398632855⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-126455397316,-126455392911⟩,⟨1434236076352,1434236138991⟩,⟨-658047607257,-658047567688⟩,⟨-21721464044822,-21721462703051⟩,⟨5408941306781,5408941918743⟩,⟨4101398632855,4101398816452⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨973056230460,973056234865⟩,⟨1434236076352,1434236138991⟩,⟨-658047607257,-658047567688⟩,⟨-21721464044822,-21721462703051⟩,⟨5408941306781,5408941918743⟩,⟨4101398632855,4101398816452⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨125247783440,125247784011⟩,⟨776714118333,776714129090⟩,⟨185472457020,185472463346⟩,⟨-2535770370578,-2535770114808⟩,⟨-661484503438,-661484377018⟩,⟨-146757975813,-146757928782⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11978330642,11978330762⟩,⟨171782137526,171782140030⟩,⟨21352348128,21352349370⟩,⟨692610074245,692610135730⟩,⟨106076850352,106076877842⟩,⟨-14842185184,-14842178956⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨172788311452,172788467825⟩,⟨1683000057444,1683005597108⟩,⟨103534175181,103536753181⟩,⟨-2137000566871,-2136787887200⟩,⟨517418993271,517546675141⟩,⟨-515107810485,-515019057788⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-172788467825,-172788311452⟩,⟨-1683005597108,-1683000057444⟩,⟨-103536753181,-103534175181⟩,⟨2136787887200,2137000566871⟩,⟨-517546675141,-517418993271⟩,⟨515019057788,515107810485⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58929713743,58929930208⟩,⟨-95697793170,-95690601435⟩,⟨136474149004,136477534609⟩,⟨-1661104633524,-1660838019750⟩,⟨-1804936793290,-1804772468769⟩,⟨387264261103,387381615706⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27296120765386,27296145752435⟩,⟨-233235144558933,-233234527826373⟩,⟨-81421907364055,-81421502183333⟩,⟨3185608584205351,3185630282507325⟩,⟨1235937047333415,1235953502726376⟩,⟨289821711980392,289835789274593⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14267249986,14267250117⟩,⟨176954420908,176954424168⟩,⟨42255149548,42255151184⟩,⟨519658355080,519658446385⟩,⟨111339627830,111339669888⟩,⟨29138247657,29138262796⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354194142899,354194470384⟩,⟨1366556807239,1366568940069⟩,⟨-7517021318,-7510753107⟩,⟨-20836023538253,-20835527629698⟩,⟨-3265804733514,-3265497987467⟩,⟨-1774124091376,-1773908966849⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354194470384,-354194142899⟩,⟨-1366568940069,-1366556807239⟩,⟨7510753107,7517021318⟩,⟨20835527629698,20836023538253⟩,⟨3265497987467,3265804733514⟩,⟨1773908966849,1774124091376⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨82988840460,82989334069⟩,⟨-545176192679,-545160688988⟩,⟨-75834025418,-75824943115⟩,⟨2853227303787,2853819730973⟩,⟨-2150379211100,-2149974838512⟩,⟨516414958412,516729250897⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨241681182598,241681182604⟩,⟨1545656160889,1545656160899⟩,⟨305284564792,305284564797⟩,⟨-3877393211067,-3877393211062⟩,⟨-1531657983104,-1531657983092⟩,⟨-349442649621,-349442649619⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1655451708013,-1655450218212⟩,⟨-4254060987633,-4254018807646⟩,⟨483523806139,483547081666⟩,⟨44222902982124,44224429204930⟩,⟨-7883963309280,-7882938459962⟩,⟨1731661232701,1732472010420⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-188576139377,-188575968810⟩,⟨-1654029295777,-1654023420134⟩,⟨-224172637242,-224169724790⟩,⟨2845157010120,2845394386048⟩,⟨-278165208563,-278023788373⟩,⟨581347078873,581447564993⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨53105043221,53105213794⟩,⟨-108373134888,-108367259235⟩,⟨81111927550,81114840007⟩,⟨-1032236200947,-1031998825014⟩,⟨-1809823191667,-1809681771465⟩,⟨231904429252,232004915374⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4447891671,4447934466⟩,⟨-36442626073,-36441102021⟩,⟨6236348375,6237166891⟩,⟨122435639528,122498652835⟩,⟨-312557647375,-312517448476⟩,⟨38081921951,38110621827⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2564907495,2564923973⟩,⟨-10468608704,-10468007504⟩,⟨7835210304,7835516810⟩,⟨-78350533412,-78324966743⟩,⟨-190815111676,-190799448262⟩,⟨34368785288,34379423419⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4414227858,4414256308⟩,⟨-35425465678,-35424318795⟩,⟨5540899760,5541478570⟩,⟨89556524613,89609217642⟩,⟨-291677415496,-291646140355⟩,⟨27750871222,27771189338⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4414256308,-4414227858⟩,⟨35424318795,35425465678⟩,⟨-5541478570,-5540899760⟩,⟨-89609217642,-89556524613⟩,⟨291646140355,291677415496⟩,⟨-27771189338,-27750871222⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨33635363,33706608⟩,⟨-1018307278,-1015636343⟩,⟨694869805,696267131⟩,⟨32826421886,32942128222⟩,⟨-20911507020,-20840032980⟩,⟨10310732613,10359750605⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58929713743,58929930208⟩,⟨-95697793170,-95690601435⟩,⟨136474149004,136477534609⟩,⟨-1661104633524,-1660838019750⟩,⟨-1804936793290,-1804772468769⟩,⟨387264261103,387381615706⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨33635363,33706608⟩,⟨-1018307278,-1015636343⟩,⟨694869805,696267131⟩,⟨32826421886,32942128222⟩,⟨-20911507020,-20840032980⟩,⟨10310732613,10359750605⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111239652966,111669149696⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨137009456742,140874927309⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111669149696,-111239652966⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438086664192,438516160922⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨54589705420,56184883119⟩,⟨-140874927309,-137009456742⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨165829358386,167854032815⟩,⟨958636700467,962502171034⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨54160208690,56614379849⟩,⟨-140874927309,-137009456742⟩,⟨438086664192,438516160922⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2079904497152,-2066561388608⟩,⟨6279457105078,6381754950461⟩,⟨2869644375977,2907528694522⟩,⟨-37040805407499,-35862814488170⟩,⟨-24165977239736,-23591165307771⟩,⟨-7688616378318,-7489560488990⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-317523115625,-311680695757⟩,⟨-873655382116,-827529480389⟩,⟨-396721997742,-379525379850⟩,⟨5295066797322,5764194132246⟩,⟨3381268808772,3612309896526⟩,⟨1112985590506,1189626010549⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨311680695757,317523115625⟩,⟨827529480389,873655382116⟩,⟨379525379850,396721997742⟩,⟨-5764194132246,-5295066797322⟩,⟨-3612309896526,-3381268808772⟩,⟨-1189626010549,-1112985590506⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-167854032815,-165829358386⟩,⟨-962502171034,-958636700467⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨931657594961,933682269390⟩,⟨-962502171034,-958636700467⟩,⟨-438516160922,-438086664192⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-182140726464,-179753864896⟩,⟨-1135913381200,-1128898163252⟩,⟨-517522339226,-515894321916⟩,⟨-1173520294823,-1159070109673⟩,⟨760137536475,767924855337⟩,⟨-243589394448,-242059242177⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-154670094011,-152312216827⟩,⟨-807870975814,-797113628391⟩,⟨-367848461885,-364493836144⟩,⟨971987291195,1006612110591⟩,⟨1361543148536,1378420263054⟩,⟨204252270595,207699019824⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨152312216827,154670094011⟩,⟨797113628391,807870975814⟩,⟨364493836144,367848461885⟩,⟨-1006612110591,-971987291195⟩,⟨-1378420263054,-1361543148536⟩,⟨-207699019824,-204252270595⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨463992912584,472193209636⟩,⟨1624643108780,1681526357930⟩,⟨744019215994,764570459627⟩,⟨-6770806242837,-6267054088517⟩,⟨-4990730159580,-4742811957308⟩,⟨-1397325030373,-1317237861101⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨823773682763,833862006016⟩,⟨4016836450765,4087864745603⟩,⟨744019215994,764570459627⟩,⟨-18946871078071,-18231463635719⟩,⟨-4990730159580,-4742811957308⟩,⟨-1397325030373,-1317237861101⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨108320417380,113228759698⟩,⟨-281749854618,-274018913484⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨10676844141356,11160645876886⟩,⟨25838463998506,29029710458228⟩,⟨-90363824322668,-82618286139665⟩,⟨125060591493717,151017082449290⟩,⟨-262731012369993,-173306911286100⟩,⟨1278614001344559,1463288206846370⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨7999281677813,8464156562090⟩,⟨58364260777237,63509999940874⟩,⟨-61306475448543,-54138281201643⟩,⟨90167371570613,153351694753823⟩,⟨-568390495568989,-457542065138131⟩,⟨818103665996175,985144025653062⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨98428283904,104076839168⟩,⟨-816228602802,-670426521944⟩,⟨621882965477,787908972519⟩,⟨7092001132050,11704278840221⟩,⟨-7042245060774,-1101719805720⟩,⟨-4863084613117,2473809184525⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1197939911680,1203588466944⟩,⟨-816228602802,-670426521944⟩,⟨621882965477,787908972519⟩,⟨7092001132050,11704278840221⟩,⟨-7042245060774,-1101719805720⟩,⟨-4863084613117,2473809184525⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨94269086528,99441345792⟩,⟨-749163485543,-612453323284⟩,⟨568107430768,723170727069⟩,⟨5968290603429,10401450535897⟩,⟨-6147172699213,-513711998723⟩,⟨-4939154899022,1977013754840⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨102708055409,108854198455⟩,⟨-893898142561,-724760662533⟩,⟨672282935302,862883712508⟩,⟨7857506615882,13556866610126⟩,⟨-8439657681824,-1346964203433⟩,⟨-5203863915115,3424334206920⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-104076839168,-98428283904⟩,⟨670426521944,816228602802⟩,⟨-787908972519,-621882965477⟩,⟨-11704278840221,-7092001132050⟩,⟨1101719805720,7042245060774⟩,⟨-2473809184525,4863084613117⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨995434788608,1001083343872⟩,⟨670426521944,816228602802⟩,⟨-787908972519,-621882965477⟩,⟨-11704278840221,-7092001132050⟩,⟨1101719805720,7042245060774⟩,⟨-2473809184525,4863084613117⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-109337382720,-103115882688⟩,⟨736344042640,901568691365⟩,⟨-870288126182,-683027597895⟩,⟨-13667270813257,-8282429565033⟩,⟨1667467113508,8492152864240⟩,⟨-3421308784421,4947236734517⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-99549499923,-93355208160⟩,⟨585476461579,757985415198⟩,⟨-734057663593,-540022963511⟩,⟨-10880694444188,-4995973542142⟩,⟨-482790703528,6795661049245⟩,⟨-2825987144851,5997655317782⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨3158555486,15498990295⟩,⟨-308421680982,33224752665⟩,⟨-61774728291,322860748997⟩,⟨-3023187828306,8560893067984⟩,⟨-8922448385352,5448696845812⟩,⟨-8029851059966,9421989524702⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1579277743,7749495148⟩,⟨-154210840491,16612376333⟩,⟨-30887364146,161430374499⟩,⟨-1511593914153,4280446533992⟩,⟨-4461224192676,2724348422906⟩,⟨-4014925529983,4710994762351⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7749495148,-1579277743⟩,⟨-16612376333,154210840491⟩,⟨-161430374499,30887364146⟩,⟨-4280446533992,1511593914153⟩,⟨-2724348422906,4461224192676⟩,⟨-4710994762351,4014925529983⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754373888468,760544125137⟩,⟨-16612376333,154210840491⟩,⟨-161430374499,30887364146⟩,⟨-4280446533992,1511593914153⟩,⟨-2724348422906,4461224192676⟩,⟨-4710994762351,4014925529983⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8811300242,9851636107⟩,⟨-154524046628,-120033168128⟩,⟨111341929516,149162725234⟩,⟨2087336219479,3427655389648⟩,⟨-2503017542672,-955637412372⟩,⟨-217180154123,1597557983781⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9851636107,-8811300242⟩,⟨120033168128,154524046628⟩,⟨-149162725234,-111341929516⟩,⟨-3427655389648,-2087336219479⟩,⟨955637412372,2503017542672⟩,⟨-1597557983781,217180154123⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1089659991669,1090700327534⟩,⟨120033168128,154524046628⟩,⟨-149162725234,-111341929516⟩,⟨-3427655389648,-2087336219479⟩,⟨955637412372,2503017542672⟩,⟨-1597557983781,217180154123⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9896036928,-8846796096⟩,⟨121002864621,155921101388⟩,⟨-150511308188,-112241413219⟩,⟨-3480755965593,-2117515456155⟩,⟨975709929114,2546991291155⟩,⟨-1632604913205,207685747018⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4948018464,-4423398048⟩,⟨60501432310,77960550694⟩,⟨-75255654094,-56120706609⟩,⟨-1740377982797,-1058757728077⟩,⟨487854964557,1273495645578⟩,⟨-816302456603,103842873509⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4423398048,4948018464⟩,⟨-77960550694,-60501432310⟩,⟨56120706609,75255654094⟩,⟨1058757728077,1740377982797⟩,⟨-1273495645578,-487854964557⟩,⟨-103842873509,816302456603⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766546781664,767071421344⟩,⟨-77960550694,-60501432310⟩,⟨56120706609,75255654094⟩,⟨1058757728077,1740377982797⟩,⟨-1273495645578,-487854964557⟩,⟨-103842873509,816302456603⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272414997917,272675081884⟩,⟨30008292032,38631011657⟩,⟨-37290681309,-27835482379⟩,⟨-856913847412,-521834054869⟩,⟨238909353093,625754385668⟩,⟨-399389495946,54295038531⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533093563328,1534142842688⟩,⟨-155921101388,-121002864620⟩,⟨112241413218,150511308188⟩,⟨2117515456154,3480755965594⟩,⟨-2546991291156,-975709929114⟩,⟨-207685747018,1632604913206⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1207617554537,1214470132499⟩,⟨-995831440432,-808742690488⟩,⟨750184078652,961280362315⟩,⟨9638388473031,15912794555387⟩,⟨-10168265628208,-2333814459311⟩,⟨-5001113455810,4539895797272⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1315723481298,1329428637222⟩,⟨-1991662880864,-1617485380976⟩,⟨1500368157304,1922560724629⟩,⟨19276776946063,31825589110762⟩,⟨-20336531256409,-4667628918622⟩,⟨-9997438694671,9079791594543⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨197384969216,208778728512⟩,⟨-1664374412442,-1337750620339⟩,⟨1240888144509,1606627761748⟩,⟨13423539997109,24968103358819⟩,⟨-15484884126735,-1428373196387⟩,⟨-10702202800794,6187273224879⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨67531552543,71991079124⟩,⟨-566166665749,-445381815958⟩,⟨411392745913,547928902437⟩,⟨4231681057513,8263724722414⟩,⟨-5163910711277,-103255249212⟩,⟨-4041140307676,2135470516218⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379839257093,380462120349⟩,⟨3173882097,23921979779⟩,⟨-24222561008,-1485855666⟩,⟨-681968283062,128996188048⟩,⟨-292397381798,641946282440⟩,⟨-618980814743,474954900156⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177519534679,3182730054990⟩,⟨-200445853334,-26507428268⟩,⟨12409475613,202964468494⟩,⟨-1080436130757,5739562284946⟩,⟨-5404529185175,2449834434457⟩,⟨-3979621353660,5212419316896⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨195161944623,208390857751⟩,⟨-1651993422002,-1288753545288⟩,⟨1189661377536,1599365911621⟩,⟨12180025182603,24503036769308⟩,⟨-15506114780759,-152941779835⟩,⟨-11949073826083,6725071290835⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨392546913839,417169586263⟩,⟨-3316367834444,-2626504165627⟩,⟨2430549522045,3205993673369⟩,⟨25603565179712,49471140128127⟩,⟨-30990998907494,-1581314976222⟩,⟨-22651276626877,12912344515714⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨517575211781,526076624993⟩,⟨-22981921984,213338623814⟩,⟨-223326283858,42730249958⟩,⟨-5926322542853,2134429185984⟩,⟨-3814205231902,6180418526212⟩,⟨-6526362174226,5601737558213⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355107863548,363892910637⟩,⟨-23845267265,221352961953⟩,⟨-231715821216,44335466425⟩,⟨-6153787383220,2259494121623⟩,⟨-4004474315201,6421583478315⟩,⟨-6780943800158,5861357161984⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨710215727096,727785821274⟩,⟨-47690534530,442705923906⟩,⟨-463431642432,88670932850⟩,⟨-12307574766440,4518988243246⟩,⟨-8008948630402,12843166956630⟩,⟨-13561887600316,11722714323968⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523241927221,1525331542446⟩,⟨-35887933260,33521182008⟩,⟨-36921312016,39169378672⟩,⟨-1310139933494,1393419746115⟩,⟨-1591353878784,1527307613558⟩,⟨-1805243730799,1849785067329⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨983918992355,1009643410120⟩,⟨-89915015976,636345749390⟩,⟨-667348749046,148938387793⟩,⟨-17970168183682,7218428885039⟩,⟨-12193001400532,18858929806401⟩,⟨-20042089438059,17518226990775⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67493539145,67622477473⟩,⟨14869708704,19160714632⟩,⟨-18495920048,-13793038076⟩,⟨-423385346805,-255864629994⟩,⟨115763967514,308850454654⟩,⟨-196685049437,29459441049⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50567360907,51284418731⟩,⟨257714221269,265944375872⟩,⟨31644453960,36688840657⟩,⟨-1377721620336,-1168362117292⟩,⟨-278912646929,-93973691525⟩,⟨-260826380738,-77183819742⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137654404503,2140581511204⟩,⟨-435111799960,-337438383018⟩,⟨313005490430,420015287456⟩,⟨5931708091016,9757583469070⟩,⟨-7150295184440,-2745648352224⟩,⟨-556649806596,4597137006250⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2980618053846,2986742224134⟩,⟨-910663839491,-705755991963⟩,⟨654654335446,879067711690⟩,⟨12461934381719,20514612450028⟩,⟨-15054497580244,-5794223002712⟩,⟨-1117117999183,9707785309777⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137080850304,139310340150⟩,⟨656150218654,689960032770⟩,⟨115891610063,140664802679⟩,⟨-3609879109651,-2541244572955⟩,⟨-1336774226146,-328917300392⟩,⟨-722938742735,302231083508⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8677933154946,8819071496374⟩,⟨-44388452837472,-40872972752424⟩,⟨-9049644418593,-7219131359975⟩,⟨543321985073394,679075877509884⟩,⟨88493011887779,177099086708856⟩,⟨-7432859464927,65082623377425⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7765614323524,8098247617174⟩,⟨-41481576633730,-31471895913303⟩,⟨-13662711518933,-5265557922833⟩,⟨290685252815570,688730053316272⟩,⟨-29859478109848,341571152182284⟩,⟨-170032613975934,211260408734063⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15531228647048,16196495234348⟩,⟨-82963153267460,-62943791826606⟩,⟨-27325423037866,-10531115845666⟩,⟨581370505631140,1377460106632544⟩,⟨-59718956219696,683142304364568⟩,⟨-340065227951868,422520817468126⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10825960642717,10867759718598⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790014,2123491006166466⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9726449014941,9768248090822⟩,⟨-107418783319355,-106594074020592⟩,⟨0,0⟩,⟨2099083303790024,2123491006166451⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2396916401408,2401631448192⟩,⟨-12142992897062,-11998203029636⟩,⟨0,0⟩,⟨102165241571294,109118793444233⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7202244708335,7290179684593⟩,⟨-42313459100025,-41132977190742⟩,⟨-19278019518584,-18797328286095⟩,⟨469831804136315,491189215759193⟩,⟨261885690782913,272122554478538⟩,⟨98119285029664,101956893420425⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6102733080559,6190668056817⟩,⟨-42313459100025,-41132977190742⟩,⟨-19278019518584,-18797328286095⟩,⟨469831804136320,491189215759190⟩,⟨261885690782915,272122554478537⟩,⟨98119285029663,101956893420425⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1884420662208,1900150632128⟩,⟨-7623492569311,-7305542195285⟩,⟨-3473264575311,-3338554229028⟩,⟨30588161038875,39955535723034⟩,⟨22431000147921,26844998117437⟩,⟨6455011247697,8232098928346⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99941875711,100371372442⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨140513458252,142538132682⟩,⟨665351118911,672754233512⟩,⟨304262413810,306306113866⟩,⟨-1685130754132,-1671622746438⟩,⟨-1535598783370,-1527717182830⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4281337063616,4301782080320⟩,⟨-19766485466373,-19303745224921⟩,⟨-3473264575311,-3338554229028⟩,⟨132753402610169,149074329167267⟩,⟨22431000147921,26844998117437⟩,⟨6455011247697,8232098928346⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨785093827678,834339172526⟩,⟨-6632735668888,-5253008331254⟩,⟨4861099044090,6411987346738⟩,⟨51207130359424,98942280256254⟩,⟨-61981997814988,-3162629952444⟩,⟨-45302553253754,25824689031428⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5066430891294,5136121252846⟩,⟨-26399221135261,-24556753556175⟩,⟨1387834468779,3073433117710⟩,⟨183960532969593,248016609423521⟩,⟨-39550997667067,23682368164993⟩,⟨-38847542006057,34056787959774⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨460521374803,468862289542⟩,⟨1627400306738,1864733654548⟩,⟨126149443518,280565200350⟩,⟨-35665861806438,-26629438135924⟩,⟨-2504570485633,4613440959161⟩,⟨-3546284558203,3108949884781⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨39925485115,42024711316⟩,⟨-850626793782,-808099553130⟩,⟨322945996948,325509439814⟩,⟨9951833054946,10695545377345⟩,⟨-6594864009033,-6530061933853⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨500446859918,510887000858⟩,⟨776773512956,1056634101418⟩,⟨449095440466,606074640164⟩,⟨-25714028751492,-15933892758579⟩,⟨-9099434494666,-1916620974692⟩,⟨-3546284558203,3108949884781⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨503376910943,504367118897⟩,⟨2514798172912,2555168940688⟩,⟨0,0⟩,⟨2165995870996,4475808627517⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229113897545,234353687761⟩,⟨1500241251428,1671955118814⟩,⟨205604260864,278018087644⟩,⟨-7256392147697,-304102281691⟩,⟨-3146916393708,530999705550⟩,⟨-1626748894896,1426135073582⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-834339172526,-785093827678⟩,⟨5253008331254,6632735668888⟩,⟨-6411987346738,-4861099044090⟩,⟨-98942280256254,-51207130359424⟩,⟨3162629952444,61981997814988⟩,⟨-25824689031428,45302553253754⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3446997891090,3516688252642⟩,⟨-14513477135119,-12671009556033⟩,⟨-9885251922049,-8199653273118⟩,⟨33811122353915,97867198807843⟩,⟨25593630100365,88826995932425⟩,⟨-19369677783731,53534652182100⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨440513389789,455895293960⟩,⟨204399815772,532435967803⟩,⟨-327630415377,-68192571713⟩,⟨-18829421759761,-7888605145543⟩,⟨-11732376685776,-1742377397309⟩,⟨-9137537976466,1307570280079⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨331658716772,335708065630⟩,⟨1917273400934,1925004342068⟩,⟨876173328384,877032321844⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-335708065630,-331658716772⟩,⟨-1925004342068,-1917273400934⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨763803562146,767852911004⟩,⟨-1925004342068,-1917273400934⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1309060475592,1326985688344⟩,⟨-8650676298924,-8360938194516⟩,⟨-3941249665867,-3820858852333⟩,⟨46726918137055,54597409881309⟩,⟨30994310797450,34709577591204⟩,⟨9804957632112,11289895806413⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1326985688344,-1309060475592⟩,⟨8360938194516,8650676298924⟩,⟨3820858852333,3941249665867⟩,⟨-54597409881309,-46726918137055⟩,⟨-34709577591204,-30994310797450⟩,⟨-11289895806413,-9804957632112⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-227474060568,-209548847816⟩,⟨8360938194516,8650676298924⟩,⟨3820858852333,3941249665867⟩,⟨-54597409881309,-46726918137055⟩,⟨-34709577591204,-30994310797450⟩,⟨-11289895806413,-9804957632112⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11712748229,-10322045753⟩,⟨437958379970,474572576137⟩,⟨97486427937,119444712199⟩,⟨-5027982562171,-4385396857752⟩,⟨1248674786965,1674761368083⟩,⟨2463424760474,2660785679720⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428800641560,445573248207⟩,⟨642358195742,1007008543940⟩,⟨-230143987440,51252140486⟩,⟨-23857404321932,-12274002003295⟩,⟨-10483701898811,-67616029226⟩,⟨-6674113215992,3968355959799⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100371372442,-99941875711⟩,⟨-877032321844,-876173328384⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4922979174,5168169997⟩,⟨30298834204,32705119259⟩,⟨39820591103,40030926275⟩,⟨-337968292171,-326679239062⟩,⟨248728938086,249843280775⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10732009764,11288684250⟩,⟨8973730548,17715810181⟩,⟨86808202403,87438394478⟩,⟨-1003167184651,-860510663551⟩,⟨100123741306,111191132797⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1449791225517,1467546056534⟩,⟨-7282497502150,-6983858478544⟩,⟨-1362076000299,-1293586376619⟩,⟨98982625445290,106030500075378⟩,⟨20708866521107,22409178244096⟩,⟨4598633957154,5017694873852⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14150985942,15067293184⟩,⟨-62936832406,-44521648316⟩,⟨100478904873,104079926480⟩,⟨-607489919202,-160033324938⟩,⟨-266931137900,-183459860622⟩,⟨-171751610394,-152744762927⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-15067293184,-14150985942⟩,⟨44521648316,62936832406⟩,⟨-104079926480,-100478904873⟩,⟨160033324938,607489919202⟩,⟨183459860622,266931137900⟩,⟨152744762927,171751610394⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115438665626,-114092861653⟩,⟨-832510673528,-813236495978⟩,⟨-104079926480,-100478904873⟩,⟨2359056580490,2806513174754⟩,⟨183459860622,266931137900⟩,⟨152744762927,171751610394⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨92823589807,97839665303⟩,⟨-635994080106,-594675967561⟩,⟨571983802599,593381597908⟩,⟨3327402664646,4010849624665⟩,⟨-3419683033375,-2967948808077⟩,⟨-2452507522860,-2236535688237⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨122395091260,130589082790⟩,⟨-1496907973360,-1373721547203⟩,⟨633001071181,682793591139⟩,⟨20298309578168,23213347766452⟩,⟨-6046599349568,-4764643833496⟩,⟨-4355358850027,-3848436916712⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-130589082790,-122395091260⟩,⟨1373721547203,1496907973360⟩,⟨-682793591139,-633001071181⟩,⟨-23213347766452,-20298309578168⟩,⟨4764643833496,6046599349568⟩,⟨3848436916712,4355358850027⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨968922544986,977116536516⟩,⟨1373721547203,1496907973360⟩,⟨-682793591139,-633001071181⟩,⟨-23213347766452,-20298309578168⟩,⟨4764643833496,6046599349568⟩,⟨3848436916712,4355358850027⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123824663727,126671117440⟩,⟨761883770535,791920459866⟩,⟨179609368245,191313665261⟩,⟨-2844301009624,-2235316322841⟩,⟨-793391179743,-528438747358⟩,⟨-199462541376,-93353547902⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11839057224,12120004178⟩,⟨168773984162,174812014434⟩,⟨20852759538,21854880892⟩,⟨613678753205,771110545373⟩,⟨92584629138,119537051794⟩,⟨-17700160968,-11995245601⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨167233433522,178535255973⟩,⟨1469519314442,1897339466593⟩,⟨-6653194831,208541670041⟩,⟨-11452219202136,7219170102895⟩,⟨-5344011728214,6480912578322⟩,⟨-5095589847741,4088585699818⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-178535255973,-167233433522⟩,⟨-1897339466593,-1469519314442⟩,⟨-208541670041,6653194831⟩,⟨-7219170102895,11452219202136⟩,⟨-6480912578322,5344011728214⟩,⟨-4088585699818,5095589847741⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨50578641572,67120254239⟩,⟨-397098215165,202435804372⟩,⟨-2937409177,284671282475⟩,⟨-14475562250592,11148116920445⟩,⟨-9627828972030,5875011433764⟩,⟨-5715334594714,6521724921323⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26618516287248,27990409451199⟩,⟨-255673830172264,-211072463663552⟩,⟨-98386529316687,-65207951936173⟩,⟨2264910445263135,4119519236333013⟩,⟨474740548485140,2027569559076510⟩,⟨-432558862998470,1024092122994763⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13944870576,14593362716⟩,⟨171603463396,182469101810⟩,⟨40454450982,44081235976⟩,⟨400497979315,637284252217⟩,⟨66105195212,156563065650⟩,⟨12720888039,45550126450⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337596943200,371505118611⟩,⟨760963889352,1968152613617⟩,⟨-326465711925,295163221207⟩,⟨-46439348156929,5014911951839⟩,⟨-18956691159569,12953561319473⟩,⟨-13322166386972,9953519752230⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371505118611,-337596943200⟩,⟨-1968152613617,-760963889352⟩,⟨-295163221207,326465711925⟩,⟨-5014911951839,46439348156929⟩,⟨-12953561319473,18956691159569⟩,⟨-9953519752230,13322166386972⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57295522949,107976305007⟩,⟨-1325794417875,246044654588⟩,⟨-525307208647,377717852411⟩,⟨-28872316273771,34165346153634⟩,⟨-23437263218284,18889075130343⟩,⟨-16627632968222,17290522346771⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨240455333963,242909505124⟩,⟨1541524447295,1549786555356⟩,⟨304262413810,306306113866⟩,⟨-3884154009684,-3870646001990⟩,⟨-1535598783370,-1527717182830⟩,⟨-349785156486,-349100310528⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1700483878878,-1611626722777⟩,⟨-5731924669410,-2777056810225⟩,⟨-440381782023,1449597700567⟩,⟨-18186921900016,106648143447574⟩,⟨-55590924589782,38745138910414⟩,⟨-40278442207223,43407004633478⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-195907153399,-181497977793⟩,⟨-1885125382899,-1429489539005⟩,⟨-346617031041,-96261916910⟩,⟨-7075613248483,12836916075522⟩,⟨-6944411681216,6281170144883⟩,⟨-4656764136902,5813719613976⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44548180564,61411527331⟩,⟨-343600935604,120297016351⟩,⟨-42354617231,210044196956⟩,⟨-10959767258167,8966270073532⟩,⟨-8480010464586,4753452962053⟩,⟨-5006549293388,5464619303448⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2635651725,6591469214⟩,⟨-119930388242,34899903701⟩,⟨-32356114378,51013804758⟩,⟨-3672277173165,4138073915674⟩,⟨-2855903536130,1983464202493⟩,⟨-1848321896610,1891555135478⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1804928971,3430046208⟩,⟨-38382601358,13438008878⟩,⟨-4731303732,23463389776⟩,⟨-1299468229054,1216347195852⟩,⟨-1078554809294,576955238452⟩,⟨-575448539765,690686979184⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3093414713,5927726735⟩,⟨-90114241187,11230673688⟩,⟨-19011756889,35068407366⟩,⟨-2381843878989,2758962345406⟩,⟨-2032244973141,1234878649031⟩,⟨-1132118259952,1249201813251⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5927726735,-3093414713⟩,⟨-11230673688,90114241187⟩,⟨-35068407366,19011756889⟩,⟨-2758962345406,2381843878989⟩,⟨-1234878649031,2032244973141⟩,⟨-1249201813251,1132118259952⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3292075010,3498054501⟩,⟨-131161061930,125014144888⟩,⟨-67424521744,70025561647⟩,⟨-6431239518571,6519917794663⟩,⟨-4090782185161,4015709175634⟩,⟨-3097523709861,3023673395430⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨50578641572,67120254239⟩,⟨-397098215165,202435804372⟩,⟨-2937409177,284671282475⟩,⟨-14475562250592,11148116920445⟩,⟨-9627828972030,5875011433764⟩,⟨-5715334594714,6521724921323⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3292075010,3498054501⟩,⟨-131161061930,125014144888⟩,⟨-67424521744,70025561647⟩,⟨-6431239518571,6519917794663⟩,⟨-4090782185161,4015709175634⟩,⟨-3097523709861,3023673395430⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (519/5120) u, BivariateJet2.affineZ (647/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000031

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000032Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2143985928320,-2143985889024⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2143985928256,-2143985889024⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-168753025088,-168753025024⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-168753025088,-168753025024⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨80340934208,80340934272⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-86677467648,-86677467584⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨80341073408,80341073472⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-86677629696,-86677629632⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6336556224,-6336556160⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6336533376,-6336533312⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨167018401792,167018401856⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨167018703040,167018703104⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1975232864000,1975232902592⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1975232864000,1975232902592⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2151078655808,-2151078616384⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2136933389184,-2136933350016⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-169927318592,-169927318528⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-167580863744,-167580863680⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨77766510208,77766510272⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-83688290752,-83688290688⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨82938473600,82938473664⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-89708873856,-89708873792⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-6770400256,-6770400192⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-5921780544,-5921780480⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨161454800896,161454800960⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨172647347456,172647347520⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1967006031488,1967006070080⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1983497752768,1983497791360⟩



end LaneCBRB2Cell000032Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000032
open Set LaneCBRB2Cell000032Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111883898060,111883898061⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111883898061,-111883898060⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437871915827,437871915828⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨44556888309,44556888310⟩,⟨-111883898061,-111883898060⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156440786369,156440786371⟩,⟨987627729715,987627729716⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44556888308,44556888311⟩,⟨-111883898061,-111883898060⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2143985928320,-2143985889024⟩,⟨6941336705892,6941336705989⟩,⟨3077491964190,3077491964237⟩,⟨-43821414934336,-43821414933121⟩,⟨-27156231569001,-27156231568338⟩,⟨-8613785021172,-8613785020911⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-305050748098,-305050742502⟩,⟨-938190880523,-938190845196⟩,⟨-415953730244,-415953714579⟩,⟨6235001466700,6235001467141⟩,⟨3808807375080,3808807414613⟩,⟨1225587131794,1225587131892⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305050742502,305050748098⟩,⟨938190845196,938190880523⟩,⟨415953714579,415953730244⟩,⟨-6235001467141,-6235001466700⟩,⟨-3808807414613,-3808807375080⟩,⟨-1225587131892,-1225587131794⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-156440786371,-156440786369⟩,⟨-987627729716,-987627729715⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨943070841405,943070841407⟩,⟨-987627729716,-987627729715⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-168753025088,-168753025024⟩,⟨-1151459810930,-1151459810924⟩,⟨-510508057075,-510508057072⟩,⟨-1205862368976,-1205862368964⟩,⟨747275682016,747275682026⟩,⟨-237031123414,-237031123411⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-144742495977,-144742495921⟩,⟨-836046643376,-836046643308⟩,⟨-370667341998,-370667341966⟩,⟨1034289779373,1034289779399⟩,⟨1389318476600,1389318476683⟩,⟨203305845382,203305845390⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144742495921,144742495977⟩,⟨836046643308,836046643376⟩,⟨370667341966,370667341998⟩,⟨-1034289779399,-1034289779373⟩,⟨-1389318476683,-1389318476600⟩,⟨-203305845390,-203305845382⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨449793238423,449793244075⟩,⟨1774237488504,1774237523899⟩,⟨786621056545,786621072242⟩,⟨-7269291246540,-7269291246073⟩,⟨-5198125891296,-5198125851680⟩,⟨-1428892977282,-1428892977176⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨811453623782,811453635382⟩,⟨4168802424748,4168802518087⟩,⟨786621056545,786621072242⟩,⟨-19298543043265,-19298543042293⟩,⟨-5198125891296,-5198125851680⟩,⟨-1428892977282,-1428892977176⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89113776616,89113776622⟩,⟨-223767796122,-223767796120⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13566093430678,13566093431592⟩,⟨34064932988053,34064932992949⟩,⟨-133317463287188,-133317463268917⟩,⟨171076465809446,171076465847086⟩,⟨-334764792633666,-334764792445706⟩,⟨2620289489126843,2620289489668457⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨10011950212073,10011950355872⟩,⟨76576249289441,76576250807555⟩,⟨-88684433191400,-88684431577068⟩,⟨146460234268765,146460241950224⟩,⟨-792299354151869,-792299338111621⟩,⟨1725419000501646,1725419032380994⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨83348994048,83349143808⟩,⟨-632221970099,-632219660162⟩,⟨732185784935,732188458930⟩,⟨8342025019193,8342082750359⟩,⟨-4520223333271,-4520137751288⟩,⟨-1434772786615,-1434649347019⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1182860621824,1182860771584⟩,⟨-632221970099,-632219660162⟩,⟨732185784935,732188458930⟩,⟨8342025019193,8342082750359⟩,⟨-4520223333271,-4520137751288⟩,⟨-1434772786615,-1434649347019⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨80340934208,80341073472⟩,⟨-587673132942,-587670911366⟩,⟨680593019539,680595591285⟩,⟨7440109441691,7440166461452⟩,⟨-3837944892474,-3837862059255⟩,⟨-1754960441612,-1754842347404⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨86431216364,86431377129⟩,⟨-678418370829,-678415651934⟩,⟨785686254199,785689401727⟩,⟨9289481360253,9289554014894⟩,⟨-5241862730023,-5241760451658⟩,⟨-1086395040571,-1086251818175⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-83349143808,-83348994048⟩,⟨632219660162,632221970099⟩,⟨-732188458930,-732185784935⟩,⟨-8342082750359,-8342025019193⟩,⟨4520137751288,4520223333271⟩,⟨1434649347019,1434772786615⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1016162483968,1016162633728⟩,⟨632219660162,632221970099⟩,⟨-732188458930,-732185784935⟩,⟨-8342082750359,-8342025019193⟩,⟨4520137751288,4520223333271⟩,⟨1434649347019,1434772786615⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-86677629696,-86677467584⟩,⟨684076391498,684078991723⟩,⟨-792245075978,-792242065893⟩,⟨-9451939924252,-9451872891957⟩,⟨5383798660536,5383895729403⟩,⟨981477589273,981615720374⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-80106991370,-80106829740⟩,⟨582379710429,582382482033⟩,⟨-674468386319,-674465177753⟩,⟨-7291118414803,-7291043530867⟩,⟨3708248632734,3708353280097⟩,⟨1849107100975,1849252699690⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6324224994,6324547389⟩,⟨-96038660400,-96033169901⟩,⟨111217867880,111224223974⟩,⟨1998362945450,1998510484027⟩,⟨-1533614097289,-1533407171561⟩,⟨762712060404,763000881515⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3162112497,3162273695⟩,⟨-48019330200,-48016584950⟩,⟨55608933940,55612111987⟩,⟨999181472725,999255242014⟩,⟨-766807048645,-766703585780⟩,⟨381356030202,381500440758⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3162273695,-3162112497⟩,⟨48016584950,48019330200⟩,⟨-55612111987,-55608933940⟩,⟨-999255242014,-999181472725⟩,⟨766703585780,766807048645⟩,⟨-381500440758,-381356030202⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758961109921,758961290383⟩,⟨48016584950,48019330200⟩,⟨-55612111987,-55608933940⟩,⟨-999255242014,-999181472725⟩,⟨766703585780,766807048645⟩,⟨-381500440758,-381356030202⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6318309541,6318332247⟩,⟨-95851937486,-95851415046⟩,⟨111007372888,111007977754⟩,⟨1991795383888,1991811721917⟩,⟨-1527336962024,-1527316603924⟩,⟨757625348954,757651577269⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6318332247,-6318309541⟩,⟨95851415046,95851937486⟩,⟨-111007977754,-111007372888⟩,⟨-1991811721917,-1991795383888⟩,⟨1527316603924,1527336962024⟩,⟨-757651577269,-757625348954⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1093193295529,1093193318235⟩,⟨95851415046,95851937486⟩,⟨-111007977754,-111007372888⟩,⟨-1991811721917,-1991795383888⟩,⟨1527316603924,1527336962024⟩,⟨-757651577269,-757625348954⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6336556224,-6336533312⟩,⟨96405405726,96405933189⟩,⟨-111649570864,-111648960182⟩,⟨-2011776739818,-2011760173251⟩,⟨1545933411721,1545954026500⟩,⟨-773367999555,-773341479795⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3168278112,-3168266656⟩,⟨48202702863,48202966595⟩,⟨-55824785432,-55824480091⟩,⟨-1005888369909,-1005880086625⟩,⟨772966705860,772977013250⟩,⟨-386683999778,-386670739897⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3168266656,3168278112⟩,⟨-48202966595,-48202702863⟩,⟨55824480091,55824785432⟩,⟨1005880086625,1005888369909⟩,⟨-772977013250,-772966705860⟩,⟨386670739897,386683999778⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765291650272,765291680992⟩,⟨-48202966595,-48202702863⟩,⟨55824480091,55824785432⟩,⟨1005880086625,1005888369909⟩,⟨-772977013250,-772966705860⟩,⟨386670739897,386683999778⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273298323882,273298329559⟩,⟨23962853761,23962984372⟩,⟨-27751994439,-27751843222⟩,⟨-497952930480,-497948845972⟩,⟨381829150981,381834240506⟩,⟨-189412894318,-189406337238⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530583300544,1530583361984⟩,⟨-96405933190,-96405405726⟩,⟨111648960182,111649570864⟩,⟨2011760173250,2011776739818⟩,⟨-1545954026500,-1545933411720⟩,⟨773341479794,773367999556⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1189697179849,1189697355185⟩,⟨-740189504715,-740186582121⟩,⟨857224360106,857227743427⟩,⟨10687663861954,10687741468543⟩,⟨-6358839528064,-6358729506499⟩,⟨-444466903393,-444312319115⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1279882731922,1279883082594⟩,⟨-1480379009429,-1480373164242⟩,⟨1714448720213,1714455486854⟩,⟨21375327723917,21375482937078⟩,⟨-12717679056123,-12717459013002⟩,⟨-888933638526,-888624806492⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨167018401792,167018703104⟩,⟨-1271752398705,-1271747028824⟩,⟨1472834768062,1472840984635⟩,⟨16891968963350,16892119756030⟩,⟨-9221853875782,-9221647465922⟩,⟨-2736589135782,-2736306962941⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57533402499,57533519555⟩,⟨-432764744057,-432762831161⟩,⟨501190983488,501193197933⟩,⟨5627287234894,5627337541258⟩,⟨-2998109665872,-2998038012594⟩,⟨-1093368913448,-1093267968957⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380446954841,380446978017⟩,⟨9394683092,9394997857⟩,⟨-10880528198,-10880163773⟩,⟨-197331369040,-197321481218⟩,⟨152127108362,152139399820⟩,⟨-77085397528,-77069601736⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177646004486,3177646198062⟩,⟨-78470806091,-78468167486⟩,⟨90875498923,90878553821⟩,⟨1651983639874,1652066688144⟩,⟨-1275217968964,-1275114849420⟩,⟨648914058755,649046419150⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨166274536764,166274885192⟩,⟨-1254818876319,-1254813125335⟩,⟨1453223287918,1453229945546⟩,⟨16411365550415,16411518800785⟩,⟨-8802960680824,-8802744818341⟩,⟨-3043090487890,-3042788414416⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨333292938556,333293588296⟩,⟨-2526571275024,-2526560154159⟩,⟨2926058055980,2926070930181⟩,⟨33303334513765,33303638556815⟩,⟨-18024814556606,-18024392284263⟩,⟨-5779679623672,-5779095377357⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523888926520,523889175657⟩,⟨66288922622,66292728320⟩,⟨-76774886612,-76770480926⟩,⟨-1375320526625,-1375217877427⟩,⟨1053609135986,1053752777834⟩,⟨-521052631058,-520852498005⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361625389948,361625647906⟩,⟨68635992131,68639948898⟩,⟨-79493248012,-79488667433⟩,⟨-1419674036897,-1419566916371⟩,⟨1085884396634,1086033960725⟩,⟨-533677375136,-533469359733⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨723250779896,723251295812⟩,⟨137271984262,137279897796⟩,⟨-158986496024,-158977334866⟩,⟨-2839348073794,-2839133832742⟩,⟨2171768793268,2172067921450⟩,⟨-1067354750272,-1066938719466⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524264968297,1524265052443⟩,⟨-554518144,-553468240⟩,⟨640982428,642197976⟩,⟨19948451333,19981355930⟩,⟨-18637422576,-18596449696⟩,⟨15689902525,15742650602⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002650448835,1002651219406⟩,⟨189936891522,189948563528⟩,⟨-219983092993,-219969580730⟩,⟨-3923235959529,-3922916813602⟩,⟨2998647258777,2999089382888⟩,⟨-1469550635897,-1468938739262⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67931954469,67931957292⟩,⟨11912575734,11912640912⟩,⟨-13796259232,-13796183770⟩,⟨-246501232578,-246499185526⟩,⟨188607821406,188610368676⟩,⟨-92761297878,-92758020952⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50134649995,50134652796⟩,⟨266355890976,266355955676⟩,⟨38418585144,38418643972⟩,⟨-1283924369915,-1283922310684⟩,⟨-225750739638,-225748507847⟩,⟨-176481849444,-176479318004⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130659813614,2130659984671⟩,⟨-268405196652,-268403717356⟩,⟨310843522998,310845235686⟩,⟨5617876973935,5617923506993⟩,⟨-4323692687510,-4323634906606⟩,⟨2175746057945,2175820226487⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966000765680,2966001122862⟩,⟨-560453183789,-560450072393⟩,⟨649068040797,649071643093⟩,⟨11765911381305,11766009404927⟩,⟨-9069125664873,-9069004202027⟩,⟨4590491615050,4590647187568⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135241325799,135241349642⟩,⟨692956428611,692956832971⟩,⟨133232199005,133232536088⟩,⟨-3198512204676,-3198500159678⟩,⟨-884850277223,-884837572468⟩,⟨-221398405859,-221384093248⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8939025104487,8939026680435⟩,⟨-45802269252551,-45802226375779⟩,⟨-8806251992552,-8806226607352⟩,⟨680778237509197,680779904216565⟩,⟨148728536099853,148729725175778⟩,⟨31983589711249,31984637862866⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8151544109897,8151551811753⟩,⟨-40223176689369,-40223010324580⟩,⟨-9818935756119,-9818796265583⟩,⟨573084020268774,573089604790797⟩,⟨167647229515866,167652686166999⟩,⟨20742129150739,20748310808122⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16303088219794,16303103623506⟩,⟨-80446353378738,-80446020649160⟩,⟨-19637871512238,-19637592531166⟩,⟨1146168040537548,1146179209581594⟩,⟨335294459031732,335305372333998⟩,⟨41484258301478,41496621616244⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10805181447606,10805181447704⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230896,2087019636287702⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9705669819830,9705669819928⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230908,2087019636287687⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2394564936256,2394564994112⟩,⟨-12029251796733,-12029251796224⟩,⟨0,0⟩,⟨104822536628670,104822536664337⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7727689483404,7727689483503⟩,⟨-48785745697677,-48785745696375⟩,⟨-21629514128651,-21629514128046⟩,⟨615979456281952,615979456306893⟩,⟨327411421901299,327411421914098⟩,⟨121080403766244,121080403771456⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6628177855628,6628177855727⟩,⟨-48785745697678,-48785745696375⟩,⟨-21629514128652,-21629514128045⟩,⟨615979456281950,615979456306893⟩,⟨327411421901298,327411421914099⟩,⟨121080403766243,121080403771457⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1975232864000,1975232902592⟩,⟨-8092796517061,-8092796516666⟩,⟨-3588000021375,-3588000021195⟩,⟨42615552557921,42615552571438⟩,⟨27903507247392,27903507253909⟩,⟨8376753896236,8376753898993⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100498837339,100498837341⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134182068023,134182068026⟩,⟨706584301385,706584301392⟩,⟨313269273869,313269273874⟩,⟨-1774257784753,-1774257784749⟩,⟨-1573260110076,-1573260110068⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4369797800256,4369797896704⟩,⟨-20122048313794,-20122048312890⟩,⟨-3588000021375,-3588000021195⟩,⟨147438089186591,147438089235775⟩,⟨27903507247392,27903507253909⟩,⟨8376753896236,8376753898993⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨666585877112,666587176592⟩,⟨-5053142550048,-5053120308318⟩,⟨5852116111960,5852141860362⟩,⟨66606669027530,66607277113630⟩,⟨-36049629113212,-36048784568526⟩,⟨-11559359247344,-11558190754714⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5036383677368,5036385073296⟩,⟨-25175190863842,-25175168621208⟩,⟨2264116090585,2264141839167⟩,⟨214044758214121,214045366349405⟩,⟨-8146121865820,-8145277314617⟩,⟨-3182605351108,-3181436855721⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨460341383558,460341511160⟩,⟨1710308904551,1710312049490⟩,⟨206947365499,206949719006⟩,⟨-30611695165691,-30611601356044⟩,⟨1058751808273,1058849511285⟩,⟨-290900186430,-290793382252⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32732328480,32732330351⟩,⟨-664535318936,-664535309497⟩,⟨321668947845,321668966201⟩,⟨8257824586746,8257824612011⟩,⟨-6530558220472,-6530558128119⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨493073712038,493073841511⟩,⟨1045773585615,1045776739993⟩,⟨528616313344,528618685207⟩,⟨-22353870578945,-22353776744033⟩,⟨-5471806412199,-5471708616834⟩,⟨-290900186430,-290793382252⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504862395711,504862407910⟩,⟨2536208829314,2536208952001⟩,⟨0,0⟩,⟨3381169318170,3381172243620⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226404495626,226404560547⟩,⟨1617545112620,1617546926289⟩,⟨242724580281,242725675235⟩,⟨-3923435376471,-3923375546654⟩,⟨-1293145032522,-1293094537058⟩,⟨-133572547004,-133523502536⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-666587176592,-666585877112⟩,⟨5053120308318,5053142550048⟩,⟨-5852141860362,-5852116111960⟩,⟨-66607277113630,-66606669027530⟩,⟨36048784568526,36049629113212⟩,⟨11558190754714,11559359247344⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3703210623664,3703212019592⟩,⟨-15068928005476,-15068905762842⟩,⟨-9440141881737,-9440116133155⟩,⟨80830812072961,80831420208245⟩,⟨63952291815918,63953136367121⟩,⟨19934944650950,19936113146337⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451931973482,451932143849⟩,⟨540831541632,540835153214⟩,⟨-96948185358,-96944645287⟩,⟨-15479002436566,-15478897380241⟩,⟨-7854171753746,-7854043804549⟩,⟨-4121126056798,-4120968340765⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨312881572738,312881572742⟩,⟨1975255459430,1975255459432⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-312881572742,-312881572738⟩,⟨-1975255459432,-1975255459430⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨786630055034,786630055038⟩,⟨-1975255459432,-1975255459430⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1413152437192,1413152464810⟩,⟨-9338351941663,-9338351872015⟩,⟨-4140226051114,-4140226020228⟩,⟨59565859789601,59565859800878⟩,⟨36805207587644,36805207670255⟩,⟨11708602097745,11708602100050⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1413152464810,-1413152437192⟩,⟨9338351872015,9338351941663⟩,⟨4140226020228,4140226051114⟩,⟨-59565859800878,-59565859789601⟩,⟨-36805207670255,-36805207587644⟩,⟨-11708602100050,-11708602097745⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-313640837034,-313640809416⟩,⟨9338351872015,9338351941663⟩,⟨4140226020228,4140226051114⟩,⟨-59565859800878,-59565859789601⟩,⟨-36805207670255,-36805207587644⟩,⟨-11708602100050,-11708602097745⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12710060897,-12710059776⟩,⟨410345144418,410345150079⟩,⟨42874557183,42874569446⟩,⟨-4314362555028,-4314362540215⟩,⟨2119762561855,2119762623816⟩,⟨2823142970389,2823142995125⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439221912585,439222084073⟩,⟨951176686050,951180303293⟩,⟨-54073628175,-54070075841⟩,⟨-19793364991594,-19793259920456⟩,⟨-5734409191891,-5734281180733⟩,⟨-1297983086409,-1297825345640⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100498837341,-100498837339⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4072640395,4072640396⟩,⟨25262323488,25262323493⟩,⟨40022876823,40022876824⟩,⟨-267341329862,-267341329853⟩,⟨248259301866,248259301870⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8869575947,8869576165⟩,⟨10460514413,10460515769⟩,⟨87163587057,87163589166⟩,⟨-746727340379,-746727325928⟩,⟨102798145600,102798158703⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1489827350450,1489827371749⟩,⟨-7653913812008,-7653913421787⟩,⟨-1444234852462,-1444234782346⟩,⟨114075282770458,114075290679969⟩,⟨24383117071982,24383118682432⟩,⟨5423519751643,5423520058697⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12018187437,12018187906⟩,⟨-47568947634,-47568940926⟩,⟨106455395267,106455400667⟩,⟨-237217335756,-237217188981⟩,⟨-284517812258,-284517726619⟩,⟨-185232298774,-185232278563⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12018187906,-12018187437⟩,⟨47568940926,47568947634⟩,⟨-106455400667,-106455395267⟩,⟨237217188981,237217335756⟩,⟨284517726619,284517812258⟩,⟨185232278563,185232298774⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112517025247,-112517024776⟩,⟨-828174890730,-828174884020⟩,⟨-106455400667,-106455395267⟩,⟨2436240444533,2436240591308⟩,⟨284517726619,284517812258⟩,⟨185232278563,185232298774⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨80044837980,80044839551⟩,⟨-528949919732,-528949915763⟩,⟨641220032913,641220048303⟩,⟨3373974010618,3373974011379⟩,⟨-3702250046321,-3702250007200⟩,⟨-2518324253255,-2518324252968⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨108459961561,108459965241⟩,⟨-1273929566852,-1273929511881⟩,⟨763705971303,763706011748⟩,⟨20240668170146,20240669406057⟩,⟨-7010281404633,-7010280754172⟩,⟨-4701986042484,-4701985840995⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-108459965241,-108459961561⟩,⟨1273929511881,1273929566852⟩,⟨-763706011748,-763705971303⟩,⟨-20240669406057,-20240668170146⟩,⟨7010280754172,7010281404633⟩,⟨4701985840995,4701986042484⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨991051662535,991051666215⟩,⟨1273929511881,1273929566852⟩,⟨-763706011748,-763705971303⟩,⟨-20240669406057,-20240668170146⟩,⟨7010280754172,7010281404633⟩,⟨4701985840995,4701986042484⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120945843806,120945844259⟩,⟨792351823317,792351832403⟩,⟨189166151056,189166157049⟩,⟨-2432024143381,-2432023915884⟩,⟨-690368133380,-690368007040⟩,⟨-175720203077,-175720154249⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11514276470,11514276567⟩,⟨169500297386,169500299470⟩,⟨21787935742,21787936940⟩,⟨748978153572,748978205917⟩,⟨102137322324,102137349534⟩,⟨-17296835826,-17296829436⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨170728767513,170728930263⟩,⟨1670829751633,1670835648666⟩,⟨117410995471,117414241747⟩,⟨-1694760945358,-1694529719155⟩,⟨404217371201,404383247005⟩,⟨-600328621553,-600187710664⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-170728930263,-170728767513⟩,⟨-1670835648666,-1670829751633⟩,⟨-117414241747,-117410995471⟩,⟨1694529719155,1694760945358⟩,⟨-404383247005,-404217371201⟩,⟨600187710664,600328621553⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨55675565363,55675793034⟩,⟨-53290536046,-53282825344⟩,⟨125310338534,125314679764⟩,⟨-2228905657316,-2228614601296⟩,⟨-1697528279527,-1697311908259⟩,⟨466615163660,466805119017⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29287908215727,29287936460165⟩,⟨-264515605803191,-264514891860281⟩,⟨-88480106658122,-88479554520348⟩,⟨3875157240692377,3875182841006788⟩,⟨1423142147467511,1423165294808213⟩,⟨326897309548864,326921459434787⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13303994941,13303995042⟩,⟨174316773812,174316776466⟩,⟨41616403466,41616404942⟩,⟨606957107508,606957185756⟩,⟨120760865604,120760905736⟩,⟨26432106807,26432121820⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354381138763,354381483209⟩,⟨1442694486949,1442707698471⟩,⟨37942758976,37950556291⟩,⟨-20816004576591,-20815449128865⟩,⟨-3602914567186,-3602515057162⟩,⟨-2038420121077,-2038084766358⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354381483209,-354381138763⟩,⟨-1442707698471,-1442694486949⟩,⟨-37950556291,-37942758976⟩,⟨20815449128865,20816004576591⟩,⟨3602515057162,3602914567186⟩,⟨2038084766358,2038420121077⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84840429376,84840945310⟩,⟨-491531012421,-491514183656⟩,⟨-92024184466,-92012834817⟩,⟨1022084137271,1022744656135⟩,⟨-2131894134729,-2131366613547⟩,⟨740101679949,740594775437⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234680905362,234680905367⟩,⟨1582328133039,1582328133048⟩,⟨313269273869,313269273874⟩,⟨-3973281040305,-3973281040301⟩,⟨-1573260110076,-1573260110068⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1668355909725,-1668354326422⟩,⟨-4047500773091,-4047454987312⟩,⟨431109635441,431139764469⟩,⟨40018053797893,40019735784327⟩,⟨-7514037501462,-7512672439772⟩,⟨2302692434113,2304014744711⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-183518490327,-183518315476⟩,⟨-1647507142764,-1647500949898⟩,⟨-239611433610,-239607837756⟩,⟨2258644233428,2258899172086⟩,⟨-164684769742,-164503809517⟩,⟨668266929904,668423083461⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51162415035,51162589891⟩,⟨-65179009725,-65172816850⟩,⟨73657840259,73661436118⟩,⟨-1714636806877,-1714381868215⟩,⟨-1737944879818,-1737763919585⟩,⟨319508790695,319664944254⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4296033576,4296077270⟩,⟨-29001601773,-29000027860⟩,⟨5009372651,5010360196⟩,⟨-72594795693,-72529108014⟩,⟨-290500018448,-290450318893⟩,⟨52504626983,52547939097⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2380686703,2380702976⟩,⟨-6065832976,-6065235910⟩,⟨6854885202,6855243278⟩,⟨-151845167615,-151819428284⟩,⟨-170473759866,-170455110162⟩,⟨39603617165,39619214690⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4276817539,4276846858⟩,⟨-28419870095,-28418677496⟩,⟨4545683806,4546380422⟩,⟨-91227640740,-91171975641⟩,⟨-276497206139,-276458699685⟩,⟨44543018443,44573501208⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4276846858,-4276817539⟩,⟨28418677496,28419870095⟩,⟨-4546380422,-4545683806⟩,⟨91171975641,91227640740⟩,⟨276458699685,276497206139⟩,⟨-44573501208,-44543018443⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨19186718,19259731⟩,⟨-582924277,-580157765⟩,⟨462992229,464676390⟩,⟨18577179948,18698532726⟩,⟨-14041318763,-13953112754⟩,⟨7931125775,8004920654⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨55675565363,55675793034⟩,⟨-53290536046,-53282825344⟩,⟨125310338534,125314679764⟩,⟨-2228905657316,-2228614601296⟩,⟨-1697528279527,-1697311908259⟩,⟨466615163660,466805119017⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨19186718,19259731⟩,⟨-582924277,-580157765⟩,⟨462992229,464676390⟩,⟨18577179948,18698532726⟩,⟨-14041318763,-13953112754⟩,⟨7931125775,8004920654⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111669149696,112098646426⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112098646426,-111669149696⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437657167462,438086664192⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨43765716745,45348814848⟩,⟨-113816633344,-109951162777⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨155434866441,157447461274⟩,⟨985694994432,989560464999⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨43336220015,45778311578⟩,⟨-113816633344,-109951162777⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2151078655808,-2136933350016⟩,⟨6883458768080,6999930341028⟩,⟨3056315679593,3098927494724⟩,⟨-44564353428761,-43093682153870⟩,⟨-27506711011428,-26812251224854⟩,⟨-8734197415431,-8495649611477⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308029369406,-302092257564⟩,⟨-962875583922,-913353910850⟩,⟨-425007650192,-406840563579⟩,⟨5960316587765,6507841968797⟩,⟨3677915977218,3938775600146⟩,⟨1182397424667,1268451755809⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨302092257564,308029369406⟩,⟨913353910850,962875583922⟩,⟨406840563579,425007650192⟩,⟨-6507841968797,-5960316587765⟩,⟨-3938775600146,-3677915977218⟩,⟨-1268451755809,-1182397424667⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157447461274,-155434866441⟩,⟨-989560464999,-985694994432⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨942064166502,944076761335⟩,⟨-989560464999,-985694994432⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-169927318592,-167580863680⟩,⟨-1154945996613,-1147981977954⟩,⟨-511304217251,-509714002411⟩,⟨-1213175214701,-1198589072106⟩,⟨743454853841,751089336334⟩,⟨-237771021219,-236294330765⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145905171484,-143583680859⟩,⟨-841440903521,-830659090587⟩,⟨-372317539005,-369018748349⟩,⟨1016623765378,1051948838470⟩,⟨1380967838561,1397676676670⟩,⟨201622130925,204988005939⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨143583680859,145905171484⟩,⟨830659090587,841440903521⟩,⟨369018748349,372317539005⟩,⟨-1051948838470,-1016623765378⟩,⟨-1397676676670,-1380967838561⟩,⟨-204988005939,-201622130925⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨445675938423,453934540890⟩,⟨1744013001437,1804316487443⟩,⟨775859311928,797325189197⟩,⟨-7559790807267,-6976940353143⟩,⟨-5336452276816,-5058883815779⟩,⟨-1473439761748,-1384019555592⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨806393734573,816538898100⟩,⟨4131523531717,4205923891477⟩,⟨775859311928,797325189197⟩,⟨-19693951056234,-18901044507288⟩,⟨-5336452276816,-5058883815779⟩,⟨-1473439761748,-1384019555592⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨86672440030,91556623156⟩,⟨-227633266688,-219902325554⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13204132895495,13948214901948⟩,⟨31713921184007,36633071844957⟩,⟨-141002767101344,-126236272213480⟩,⟨152342119672033,192423469559585⟩,⟨-423509614387536,-252503748843064⟩,⟨2413728572482448,2850799255675216⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9684054054920,10358471651215⟩,⟨72875166656722,80560729127555⟩,⟨-95396621522995,-82468319217827⟩,⟨100231675354539,196179069868470⟩,⟨-899205972823732,-693721879994183⟩,⟨1547062881813854,1922335768714702⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨80582654464,86146744576⟩,⟨-710709347261,-562228422907⟩,⟨636239135781,841592067844⟩,⟨6072093281193,10916217356128⟩,⟨-8490182257898,-897112364535⟩,⟨-6966615101733,4455849818232⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1180094282240,1185658372352⟩,⟨-710709347261,-562228422907⟩,⟨636239135781,841592067844⟩,⟨6072093281193,10916217356128⟩,⟨-8490182257898,-897112364535⟩,⟨-6966615101733,4455849818232⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨77766510208,82938473664⟩,⟨-662178609831,-521378419675⟩,⟨590011713449,784124013111⟩,⟨5232115632529,9923571319840⟩,⟨-7630652572377,-359693526425⟩,⟨-7050103526007,3834974752323⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨83465978647,89436703720⟩,⟨-767670609294,-599355402601⟩,⟨678253442622,909043194645⟩,⟨6578250376482,12380562911703⟩,⟨-9882640731674,-1052904082866⟩,⟨-7445157834238,5671933108654⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-86146744576,-80582654464⟩,⟨562228422907,710709347261⟩,⟨-841592067844,-636239135781⟩,⟨-10916217356128,-6072093281193⟩,⟨897112364535,8490182257898⟩,⟨-4455849818232,6966615101733⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1013364883200,1018928973312⟩,⟨562228422907,710709347261⟩,⟨-841592067844,-636239135781⟩,⟨-10916217356128,-6072093281193⟩,⟨897112364535,8490182257898⟩,⟨-4455849818232,6966615101733⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-89708873856,-83688290688⟩,⟨606692620038,771127166767⟩,⟨-913136304386,-686556517833⟩,⟨-12385030710869,-6887071804181⟩,⟨1346891785816,9852353073283⟩,⟨-5592997203049,7130151859697⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-83134155589,-77131312462⟩,⟨501171653795,671818158152⟩,⟨-797786261847,-564099526719⟩,⟨-10394709396821,-4459926074515⟩,⟨-631826756648,8359863408997⟩,⟨-4956933336930,8369010287870⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨331823058,12305391258⟩,⟨-266498955499,72462755551⟩,⟨-119532819225,344943667926⟩,⟨-3816459020339,7920636837188⟩,⟨-10514467488322,7306959326131⟩,⟨-12402091171168,14040943396524⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨165911529,6152695629⟩,⟨-133249477750,36231377776⟩,⟨-59766409613,172471833963⟩,⟨-1908229510170,3960318418594⟩,⟨-5257233744161,3653479663066⟩,⟨-6201045585584,7020471698262⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6152695629,-165911529⟩,⟨-36231377776,133249477750⟩,⟨-172471833963,59766409613⟩,⟨-3960318418594,1908229510170⟩,⟨-3653479663066,5257233744161⟩,⟨-7020471698262,6201045585584⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755970687987,761957491351⟩,⟨-36231377776,133249477750⟩,⟨-172471833963,59766409613⟩,⟨-3960318418594,1908229510170⟩,⟨-3653479663066,5257233744161⟩,⟨-7020471698262,6201045585584⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨5905862235,6749598107⟩,⟨-111368165756,-82410876952⟩,⟨93259292834,131877490106⟩,⟨1465025332937,2629357121986⟩,⟨-2418399001860,-782171667356⟩,⟨-355341351369,1986580473056⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6749598107,-5905862235⟩,⟨82410876952,111368165756⟩,⟨-131877490106,-93259292834⟩,⟨-2629357121986,-1465025332937⟩,⟨782171667356,2418399001860⟩,⟨-1986580473056,355341351369⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092762029669,1093605765541⟩,⟨82410876952,111368165756⟩,⟨-131877490106,-93259292834⟩,⟨-2629357121986,-1465025332937⟩,⟨782171667356,2418399001860⟩,⟨-1986580473056,355341351369⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6770400256,-5921780480⟩,⟨82855925159,112056046869⟩,⟨-132692049941,-93762926367⟩,⟨-2657017838076,-1479180769682⟩,⟨793461369263,2446859810979⟩,⟨-2014864503308,349540356854⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3385200128,-2960890240⟩,⟨41427962579,56028023435⟩,⟨-66346024971,-46881463183⟩,⟨-1328508919038,-739590384841⟩,⟨396730684631,1223429905490⟩,⟨-1007432251654,174770178427⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨2960890240,3385200128⟩,⟨-56028023435,-41427962579⟩,⟨46881463183,66346024971⟩,⟨739590384841,1328508919038⟩,⟨-1223429905490,-396730684631⟩,⟨-174770178427,1007432251654⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765084273856,765508603008⟩,⟨-56028023435,-41427962579⟩,⟨46881463183,66346024971⟩,⟨739590384841,1328508919038⟩,⟨-1223429905490,-396730684631⟩,⟨-174770178427,1007432251654⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273190507417,273401441386⟩,⟨20602719238,27842041439⟩,⟨-32969372527,-23314823208⟩,⟨-657339280497,-366256333234⟩,⟨195542916839,604599750465⟩,⟨-496645118264,88835337843⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530168547712,1531017206016⟩,⟨-112056046870,-82855925158⟩,⟨93762926366,132692049942⟩,⟨1479180769682,2657017838076⟩,⟨-2446859810980,-793461369262⟩,⟨-349540356854,2014864503308⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1186467213396,1192981757763⟩,⟨-836681140635,-654673296853⟩,⟨740853282470,990762558544⟩,⟨7792978385348,14024684119134⟩,⟨-11384764922860,-1862202373439⟩,⟨-7276227033251,6891282187727⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1273422799016,1286451887750⟩,⟨-1673362281270,-1309346593706⟩,⟨1481706564940,1981525117088⟩,⟨15585956770704,28049368238256⟩,⟨-22769529845711,-3724404746879⟩,⟨-14547772049332,13782564375450⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨161454800896,172647347520⟩,⟨-1444831431605,-1119079398364⟩,⟨1266392946845,1710908512597⟩,⟨11422484844321,23079674579751⟩,⟨-18370967712575,-934946691609⟩,⟨-15223264992765,10441678386844⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨55404711688,59699375366⟩,⟨-495357677725,-376120805363⟩,⟨423933897921,587902888928⟩,⟨3692323568745,7761246988250⟩,⟨-6236279605035,8569231044⟩,⟨-5641920509423,3665232645301⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380193816438,380698394030⟩,⟨808857516,18181883441⟩,⟨-22611434525,548051091⟩,⟨-553463307191,147869714491⟩,⟨-332782142892,651448628322⟩,⟨-786427886838,620733006181⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175547463747,3179761919700⟩,⟨-152064705144,-6746982581⟩,⟨-4583641064,189111383047⟩,⟨-1236683940292,4643450569993⟩,⟨-5466496963837,2783671428156⟩,⟨-5192063561817,6599806461817⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨160016763111,172649197720⟩,⟨-1440819367576,-1086630876813⟩,⟨1224133096757,1710469450825⟩,⟨10601429354523,22834484807031⟩,⟨-18498492789033,175388620128⟩,⟨-16603113556801,11160345613937⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨321471564007,345296545240⟩,⟨-2885650799181,-2205710275177⟩,⟨2490526043602,3421377963422⟩,⟨22023914198844,45914159386782⟩,⟨-36869460501608,-759558071481⟩,⟨-31826378549566,21602024000781⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519768656063,528033723300⟩,⟨-50216421584,184682790478⟩,⟨-239044686052,82835801616⟩,⟨-5497753771762,2677088912264⟩,⟨-5105499404772,7300973225968⟩,⟨-9749072024687,8648711939998⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357367633585,365925417241⟩,⟨-52199691639,191976736090⟩,⟨-248485624941,86107356211⟩,⟨-5724013113580,2816391548223⟩,⟨-5350592934698,7604379431066⟩,⟨-10153596993708,9046533698833⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714735267170,731850834482⟩,⟨-104399383278,383953472180⟩,⟨-496971249882,172214712422⟩,⟨-11448026227160,5632783096446⟩,⟨-10701185869396,15208758862132⟩,⟨-20307193987416,18093067397666⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523418949605,1525111343781⟩,⟨-29645169918,28512240598⟩,⟨-38114563740,39432757108⟩,⟨-1150176352304,1191992505139⟩,⟨-1664688143624,1624937632598⟩,⟨-2336120829910,2370205854677⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨990295347908,1015136158116⟩,⟨-164542621919,551552605413⟩,⟨-714708827225,265122714770⟩,⟨-16665614492037,8626445246214⟩,⟨-15977645808859,22204527130293⟩,⟨-29758319017277,26708642644168⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67878366592,67983226611⟩,⟨10238122418,13846246040⟩,⟨-16396141238,-11585849974⟩,⟨-326132130300,-180593950515⟩,⟨95501553070,299802367376⟩,⟨-245999963610,46156290296⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49782729122,50486913957⟩,⟨262568416147,270336636739⟩,⟨35721291805,40801735115⟩,⟨-1382941100430,-1193374686571⟩,⟨-315408187766,-123159885830⟩,⟨-297571970142,-67515938573⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2129505250565,2131868027498⟩,⟨-312065341490,-230617898828⟩,⟨260976013790,369534630524⟩,⟨4129580692245,7422380048277⟩,⟨-6841316313310,-2222620323804⟩,⟨-957444743437,5643231638667⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2963590265246,2968523977920⟩,⟨-651804030743,-481419540838⟩,⟨544792721496,771838873631⟩,⟨8646651462925,15550668247719⟩,⟨-14345798595999,-4669264565642⟩,⟨-1966417164642,11853788751955⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134182856894,136307439473⟩,⟨677789674261,708072920748⟩,⟨120948735581,145599817036⟩,⟨-3662765200767,-2732467225355⟩,⟨-1404370087563,-369241001390⟩,⟨-858296028277,419601169623⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8869111064580,9009540023207⟩,⟨-47542670252344,-44101715377293⟩,⟨-9776117525907,-7869766853047⟩,⟨616385504904809,747690031094340⟩,⟨102290329335685,197470357279071⟩,⟨-14207544127929,78845051518532⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7988127824622,8318156547422⟩,⟨-45242574710068,-35201527043248⟩,⟨-14882323894529,-4915600396917⟩,⟨370900679586944,775228800706112⟩,⟨-55161114697868,396630302762725⟩,⟨-261675358714064,304358038680818⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15976255649244,16636313094844⟩,⟨-90485149420136,-70403054086496⟩,⟨-29764647789058,-9831200793834⟩,⟨741801359173888,1550457601412224⟩,⟨-110322229395736,793260605525450⟩,⟨-523350717428128,608716077361636⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10784481866270,10825960642718⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533866,2099083303790624⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9684970238494,9726449014942⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533869,2099083303790615⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2392217469760,2396916459264⟩,⟨-12101371604921,-11957606413725⟩,⟨0,0⟩,⟨101381360168522,108260423343400⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7678280804482,7777700378915⟩,⟨-49515948254148,-48069641095385⟩,⟨-21921122925001,-21343339553879⟩,⟨601877022702891,630476622152800⟩,⟨320858809297547,334134974881080⟩,⟨118656286455760,123567534587904⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6578769176706,6678188751139⟩,⟨-49515948254148,-48069641095384⟩,⟨-21921122925001,-21343339553878⟩,⟨601877022702894,630476622152791⟩,⟨320858809297547,334134974881077⟩,⟨118656286455760,123567534587904⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1967006031488,1983497791360⟩,⟨-8275614997799,-7914291029608⟩,⟨-3663683722982,-3514014186999⟩,⟨36806876204957,48404630912718⟩,⟨25251712885982,30550182286680⟩,⟨7328067016653,9421168884659⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100284130918,100713627649⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133176961661,135189556495⟩,⟨702843090369,710324156109⟩,⟨312252724673,314285221743⟩,⟨-1781208837000,-1767320322048⟩,⟨-1577197890442,-1569322329700⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4359223501248,4380414250624⟩,⟨-20376986602720,-19871897443333⟩,⟨-3663683722982,-3514014186999⟩,⟨138188236373479,156665054256118⟩,⟨25251712885982,30550182286680⟩,⟨7328067016653,9421168884659⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨642943128014,690593090480⟩,⟨-5771301598362,-4411420550354⟩,⟨4981052087204,6842755926844⟩,⟨44047828397688,91828318773564⟩,⟨-73738921003216,-1519116142962⟩,⟨-63652757099132,43204048001562⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5002166629262,5071007341104⟩,⟨-26148288201082,-24283317993687⟩,⟨1317368364222,3328741739845⟩,⟨182236064771167,248493373029682⟩,⟨-48487208117234,29031066143718⟩,⟨-56324690082479,52625216886221⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨456237042383,464496720413⟩,⟨1587049332309,1826128881943⟩,⟨120154383243,304907786019⟩,⟨-35194482828995,-25906305727514⟩,⟨-3392607332427,5311793497988⟩,⟨-5159257729622,4820391494311⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨31725078447,33746572358⟩,⟨-684993761655,-644263062584⟩,⟨320394994437,322946015318⟩,⟨7927025738846,8596166303857⟩,⟨-6562818552468,-6498504886492⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨487962120830,498243292771⟩,⟨902055570654,1181865819359⟩,⟨440549377680,627853801337⟩,⟨-27267457090149,-17310139423657⟩,⟨-9955425884895,-1186711388504⟩,⟨-5159257729622,4820391494311⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504367106722,505357825907⟩,⟨2516159178967,2556424289217⟩,⟨0,0⟩,⟨2234856254543,4531068346710⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨223837599217,229002714339⟩,⟨1530459055709,1701652214765⟩,⟨202088463073,288574330654⟩,⟨-7412260699581,-391437016168⟩,⟨-3567547556243,915426897593⟩,⟨-2371299405728,2215549616800⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-690593090480,-642943128014⟩,⟨4411420550354,5771301598362⟩,⟨-6842755926844,-4981052087204⟩,⟨-91828318773564,-44047828397688⟩,⟨1519116142962,73738921003216⟩,⟨-43204048001562,63652757099132⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3668630410768,3737471122610⟩,⟨-15965566052366,-14100595844971⟩,⟨-10506439649826,-8495066274203⟩,⟨46359917599915,112617225858430⟩,⟨26770829028944,104289103289896⟩,⟨-35875980984909,73073925983791⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨444358239804,459537717215⟩,⟨382073032155,706624185939⟩,⟨-249948311668,39367319025⟩,⟨-21068079230384,-10077187635926⟩,⟨-13469792287599,-1848197013866⟩,⟨-11604104400082,2997154691390⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨310869732882,314894922548⟩,⟨1971389988864,1979120929998⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-314894922548,-310869732882⟩,⟨-1979120929998,-1971389988864⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨784616705228,788641894894⟩,⟨-1979120929998,-1971389988864⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1403664820454,1422694783011⟩,⟨-9506110188126,-9174455908920⟩,⟨-4208434197866,-4073538375242⟩,⟨54645714178257,64511191836710⟩,⟨34554789227483,39068852577253⟩,⟨10824312794565,12596476521810⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1422694783011,-1403664820454⟩,⟨9174455908920,9506110188126⟩,⟨4073538375242,4208434197866⟩,⟨-64511191836710,-54645714178257⟩,⟨-39068852577253,-34554789227483⟩,⟨-12596476521810,-10824312794565⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-323183155235,-304153192678⟩,⟨9174455908920,9506110188126⟩,⟨4073538375242,4208434197866⟩,⟨-64511191836710,-54645714178257⟩,⟨-39068852577253,-34554789227483⟩,⟨-12596476521810,-10824312794565⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13455773276,-11987912945⟩,⟨392017897850,429242657238⟩,⟨31786407697,54151484787⟩,⟨-4653993851925,-3988700775670⟩,⟨1893741173034,2341475473562⟩,⟨2718462480253,2926965860437⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430902466528,447549804270⟩,⟨774090930005,1135866843177⟩,⟨-218161903971,93518803812⟩,⟨-25722073082309,-14065888411596⟩,⟨-11576051114565,493278459696⟩,⟨-8885641919829,5924120551827⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100713627649,-100284130918⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨3952605003,4193225165⟩,⟨24074259789,26451178948⟩,⟨39917784923,40128086017⟩,⟨-272951882548,-261735307013⟩,⟨247702508009,248816179610⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8599718729,9141158822⟩,⟨6227391071,14677035555⟩,⟨86849488477,87478538129⟩,⟨-812827675082,-680218808036⟩,⟨97273538155,108293929972⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1480548963959,1499175610851⟩,⟨-7819280146737,-7491281675235⟩,⟨-1482316176719,-1406788706729⟩,⟨110080162892435,118179595631309⟩,⟨23408911110932,25383750231495⟩,⟨5182911634751,5670581021314⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11579963624,12463899440⟩,⟨-56622706595,-38580275561⟩,⟨104623570759,108273255726⟩,⟨-456057653762,-18281825347⟩,⟨-327824560597,-241003448518⟩,⟨-195332288162,-175097809387⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12463899440,-11579963624⟩,⟨38580275561,56622706595⟩,⟨-108273255726,-104623570759⟩,⟨18281825347,456057653762⟩,⟨241003448518,327824560597⟩,⟨175097809387,195332288162⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113177527089,-111864094542⟩,⟨-837593052823,-818691628329⟩,⟨-108273255726,-104623570759⟩,⟨2217305080899,2655080909314⟩,⟨241003448518,327824560597⟩,⟨175097809387,195332288162⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨77527698660,82583192041⟩,⟨-549879335019,-508634964419⟩,⟨630422649126,651798326458⟩,⟨3033566725029,3728644107053⟩,⟨-3934139133467,-3466055466145⟩,⟨-2630669075365,-2405233123113⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨104395034149,112601544401⟩,⟨-1337054347417,-1213121138697⟩,⟨737561275429,789527860695⟩,⟨18777665305316,21781362814196⟩,⟨-7698125247753,-6314596534906⟩,⟨-4978899699510,-4426068384009⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-112601544401,-104395034149⟩,⟨1213121138697,1337054347417⟩,⟨-789527860695,-737561275429⟩,⟨-21781362814196,-18777665305316⟩,⟨6314596534906,7698125247753⟩,⟨4426068384009,4978899699510⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨986910083375,995116593627⟩,⟨1213121138697,1337054347417⟩,⟨-789527860695,-737561275429⟩,⟨-21781362814196,-18777665305316⟩,⟨6314596534906,7698125247753⟩,⟨4426068384009,4978899699510⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119538241357,122353750115⟩,⟨777802343048,807277628006⟩,⟨183199009564,195108686592⟩,⟨-2739266736986,-2133178583635⟩,⟨-828147078244,-551378723009⟩,⟨-231210878978,-119481402191⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11381030751,11649856459⟩,⟨166587047190,172434211756⟩,⟨21288762600,22290076838⟩,⟨672590414539,824957709373⟩,⟨88315697972,115922910944⟩,⟨-20301984072,-14304641803⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165370017229,176269768019⟩,⟨1461829243765,1880298633763⟩,⟨-6038281338,235500464107⟩,⟨-10929880174421,7576445076210⟩,⟨-6387971080613,7306296006340⟩,⟨-7059155424732,5861085911955⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176269768019,-165370017229⟩,⟨-1880298633763,-1461829243765⟩,⟨-235500464107,6038281338⟩,⟨-7576445076210,10929880174421⟩,⟨-7306296006340,6387971080613⟩,⟨-5861085911955,7059155424732⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47567831198,63632697110⟩,⟨-349839578054,239822971000⟩,⟨-33412001034,294612611992⟩,⟨-14988705775791,10538443158253⟩,⟨-10873843562583,7303397978206⟩,⟨-8232385317683,9274705041532⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28581226818148,30011588278282⟩,⟨-288448805969430,-240946945991571⟩,⟨-109128725531462,-68647587126912⟩,⟨2875407817909059,4891484734199852⟩,⟨463667890857616,2418803698135774⟩,⟨-774794863830709,1439017998151801⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨12996125539,13615536016⟩,⟨169124403712,179667850118⟩,⟨39834571764,43423423422⟩,⟨490794131138,721594464796⟩,⟨74880005216,166612216792⟩,⟨9590365141,43264304426⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337827452119,371641236689⟩,⟨824364030019,2056131767169⟩,⟨-315890394690,373850748588⟩,⟨-47524094329515,6144878550417⟩,⟨-21797231609824,15211849558521⟩,⟨-17964911134777,14026534155550⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371641236689,-337827452119⟩,⟨-2056131767169,-824364030019⟩,⟨-373850748588,315890394690⟩,⟨-6144878550417,47524094329515⟩,⟨-15211849558521,21797231609824⟩,⟨-14026534155550,17964911134777⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59261229839,109722352151⟩,⟨-1282040837164,311502813158⟩,⟨-592012652559,409409198502⟩,⟨-31866951632726,33458205917919⟩,⟨-26787900673086,22290510069520⟩,⟨-22912176075379,23889031686604⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨233461092579,235903184144⟩,⟨1578157425293,1586497484493⟩,⟨312252724673,314285221743⟩,⟨-3980232092552,-3966343577600⟩,⟨-1577197890442,-1569322329700⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1712448261927,-1625421075345⟩,⟨-5510525056209,-2581820174264⟩,⟨-638019088905,1543591059143⟩,⟨-22533588326544,102563067231490⟩,⟨-64132473441915,47900878659346⟩,⟨-58242605796221,62688359089848⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-190561392378,-176714799464⟩,⟨-1870516440888,-1430528358445⟩,⟨-374873306477,-99054319796⟩,⟨-7445853771855,12026736749282⟩,⟨-7767844977715,7323370293829⟩,⟨-6531044872935,7883889829294⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨42899700201,59188384680⟩,⟨-292359015595,155969126048⟩,⟨-62620581804,215230901947⟩,⟨-11426085864407,8060393171682⟩,⟨-9345042868157,5754047964129⟩,⟨-6880145183463,7535473693636⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2563800242,6350027617⟩,⟨-109107475196,41960178931⟩,⟨-37596150969,53093936262⟩,⟨-3899278289745,3803830536887⟩,⟨-3109219508884,2290683728050⟩,⟨-2464793423325,2527485955323⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1673819749,3186200849⟩,⟨-31476261720,16792110966⟩,⟨-6741922490,23172414184⟩,⟨-1313111253120,1023282394669⟩,⟨-1120575119332,680560660920⟩,⟨-765253506098,895555525638⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨2994432672,5747844941⟩,⟨-80763918172,18244480442⟩,⟨-22779041100,36453098810⟩,⟨-2565571125883,2460070475540⟩,⟨-2213417629266,1471873663066⟩,⟨-1523772488526,1687795417475⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5747844941,-2994432672⟩,⟨-18244480442,80763918172⟩,⟨-36453098810,22779041100⟩,⟨-2460070475540,2565571125883⟩,⟨-1471873663066,2213417629266⟩,⟨-1687795417475,1523772488526⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3184044699,3355594945⟩,⟨-127351955638,122724097103⟩,⟨-74049249779,75872977362⟩,⟨-6359348765285,6369401662770⟩,⟨-4581093171950,4504101357316⟩,⟨-4152588840800,4051258443849⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47567831198,63632697110⟩,⟨-349839578054,239822971000⟩,⟨-33412001034,294612611992⟩,⟨-14988705775791,10538443158253⟩,⟨-10873843562583,7303397978206⟩,⟨-8232385317683,9274705041532⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3184044699,3355594945⟩,⟨-127351955638,122724097103⟩,⟨-74049249779,75872977362⟩,⟨-6359348765285,6369401662770⟩,⟨-4581093171950,4504101357316⟩,⟨-4152588840800,4051258443849⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (521/5120) u, BivariateJet2.affineZ (521/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000032

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000033Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2133219505344,-2133219466240⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2133219505344,-2133219466240⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-170549246400,-170549246336⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-170549246400,-170549246336⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨82722870464,82722870528⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-89456667328,-89456667264⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨82722994176,82722994240⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-89456812032,-89456811968⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6733817792,-6733817728⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6733796864,-6733796800⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨172179537728,172179537792⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨172179806144,172179806208⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2394564936256,2394564994112⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1962670219904,1962670258496⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1962670219904,1962670258496⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2514672104640,-2514672046784⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2510451325440,-2510451267584⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-118233797888,-118233797824⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-117755645376,-117755645312⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2140248186688,-2140248147456⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2126230248704,-2126230209728⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-171726343424,-171726343360⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-169374288832,-169374288768⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨80149035968,80149036032⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-86454131392,-86454131328⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨85319548672,85319548736⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-92501344000,-92501343936⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7181795264,-7181795200⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6305095360,-6305095296⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨166603167296,166603167360⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨177820892672,177820892736⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2392217469760,2392217527616⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2396916401408,2396916459264⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1954503866304,1954503904896⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1970873858688,1970873897280⟩



end LaneCBRB2Cell000033Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000033
open Set LaneCBRB2Cell000033Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111883898060,111883898061⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨115749368627,115749368628⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-111883898061,-111883898060⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437871915827,437871915828⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46096281763,46096281765⟩,⟨-115749368628,-115749368627⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157980179823,157980179826⟩,⟨983762259148,983762259149⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46096281762,46096281766⟩,⟨-115749368628,-115749368627⟩,⟨437871915827,437871915828⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2133219505344,-2133219466240⟩,⟨6846795870796,6846795870935⟩,⟨3047504208809,3047504208876⟩,⟨-42635850785019,-42635850783291⟩,⟨-26629577518003,-26629577517063⟩,⟨-8446733684754,-8446733684390⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-306505536230,-306505530605⟩,⟨-924885895946,-924885860917⟩,⟨-411666086410,-411666070815⟩,⟨6126010133363,6126010133991⟩,⟨3760390803277,3760390842717⟩,⟨1213644742477,1213644742613⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306505530605,306505536230⟩,⟨924885860917,924885895946⟩,⟨411666070815,411666086410⟩,⟨-6126010133991,-6126010133363⟩,⟨-3760390842717,-3760390803277⟩,⟨-1213644742613,-1213644742477⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157980179826,-157980179823⟩,⟨-983762259149,-983762259148⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941531447950,941531447953⟩,⟨-983762259149,-983762259148⟩,⟨-437871915828,-437871915827⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-170549246400,-170549246336⟩,⟨-1148828374514,-1148828374507⟩,⟨-511342732076,-511342732072⟩,⟨-1200357141068,-1200357141054⟩,⟨749721254495,749721254508⟩,⟨-237806843549,-237806843545⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146044366293,-146044366237⟩,⟨-831167318242,-831167318174⟩,⟨-369952010894,-369952010862⟩,⟨1027887262412,1027887262444⟩,⟨1386474306292,1386474306380⟩,⟨203638248178,203638248189⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146044366237,146044366293⟩,⟨831167318174,831167318242⟩,⟨369952010862,369952010894⟩,⟨-1027887262444,-1027887262412⟩,⟨-1386474306380,-1386474306292⟩,⟨-203638248189,-203638248178⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨452549896842,452549902523⟩,⟨1756053179091,1756053214188⟩,⟨781618081677,781618097304⟩,⟨-7153897396435,-7153897395775⟩,⟨-5146865149097,-5146865109569⟩,⟨-1417282990802,-1417282990655⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨814210282201,814210293830⟩,⟨4150618115335,4150618208376⟩,⟨781618081677,781618097304⟩,⟨-19183149193160,-19183149191995⟩,⟨-5146865149097,-5146865109569⟩,⟨-1417282990802,-1417282990655⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92192563524,92192563532⟩,⟨-231498737256,-231498737254⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13113051349255,13113051350394⟩,⟨32927328545816,32927328551822⟩,⟨-124561823593364,-124561823571438⟩,⟨165363337073449,165363337119399⟩,⟨-312779076493260,-312779076269075⟩,⟨2366443549742339,2366443550369814⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9710475969398,9710476108933⟩,⟨73884655598657,73884657065293⟩,⟨-82918741961674,-82918740440824⟩,⟨142270838856162,142270846290912⟩,⟨-739811210652555,-739811195606191⟩,⟨1558399357877073,1558399386945566⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨85914271744,85914405120⟩,⟨-647957809327,-647955759231⟩,⟨727183134055,727185433725⟩,⟨8482803729364,8482854762765⟩,⟨-4432309495755,-4432236183642⟩,⟨-1411411666267,-1411309224830⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1185425899520,1185426032896⟩,⟨-647957809327,-647955759231⟩,⟨727183134055,727185433725⟩,⟨8482803729364,8482854762765⟩,⟨-4432309495755,-4432236183642⟩,⟨-1411411666267,-1411309224830⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨82722870464,82722994240⟩,⟨-600996777574,-600994808438⟩,⟨674480135603,674482344493⟩,⟨7539500980514,7539551353183⟩,⟨-3742403967306,-3742333090646⟩,⟨-1722872155644,-1722774281380⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨89186717678,89186861161⟩,⟨-696707716954,-696705293863⟩,⟨781893411528,781896129717⟩,⟨9475186471375,9475251051225⟩,⟨-5163264364530,-5163176362355⟩,⟨-1071523498523,-1071404158142⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-85914405120,-85914271744⟩,⟨647955759231,647957809327⟩,⟨-727185433725,-727183134055⟩,⟨-8482854762765,-8482803729364⟩,⟨4432236183642,4432309495755⟩,⟨1411309224830,1411411666267⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1013597222656,1013597356032⟩,⟨647955759231,647957809327⟩,⟨-727185433725,-727183134055⟩,⟨-8482854762765,-8482803729364⟩,⟨4432236183642,4432309495755⟩,⟨1411309224830,1411411666267⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-89456812032,-89456667264⟩,⟨702877614388,702879930745⟩,⟨-788823037454,-788820439060⟩,⟨-9651204413243,-9651144881774⟩,⟨5312184306129,5312267787865⟩,⟨965008638944,965123693292⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-82466784220,-82466639911⟩,⟨595237504836,595239977572⟩,⟨-668021644268,-668018870371⟩,⟨-7378480157559,-7378413486837⟩,⟨3606753022639,3606843178044⟩,⟨1818174065471,1818295503910⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6719933458,6720221250⟩,⟨-101470212118,-101465316291⟩,⟨113871767260,113877259346⟩,⟨2096706313816,2096837564388⟩,⟨-1556511341891,-1556333184311⟩,⟨746650566948,746891345768⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3359966729,3360110625⟩,⟨-50735106059,-50732658145⟩,⟨56935883630,56938629673⟩,⟨1048353156908,1048418782194⟩,⟨-778255670946,-778166592155⟩,⟨373325283474,373445672884⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3360110625,-3359966729⟩,⟨50732658145,50735106059⟩,⟨-56938629673,-56935883630⟩,⟨-1048418782194,-1048353156908⟩,⟨778166592155,778255670946⟩,⟨-373445672884,-373325283474⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758763272991,758763436151⟩,⟨50732658145,50735106059⟩,⟨-56938629673,-56935883630⟩,⟨-1048418782194,-1048353156908⟩,⟨778166592155,778255670946⟩,⟨-373445672884,-373325283474⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6713218762,6713239607⟩,⟨-101261156908,-101260679324⟩,⟨113642107656,113642643466⟩,⟨2089365026541,2089379892515⟩,⟨-1549751167198,-1549733212670⟩,⟨741301331376,741323766788⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6713239607,-6713218762⟩,⟨101260679324,101261156908⟩,⟨-113642643466,-113642107656⟩,⟨-2089379892515,-2089365026541⟩,⟨1549733212670,1549751167198⟩,⟨-741323766788,-741301331376⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092798388169,1092798409014⟩,⟨101260679324,101261156908⟩,⟨-113642643466,-113642107656⟩,⟨-2089379892515,-2089365026541⟩,⟨1549733212670,1549751167198⟩,⟨-741323766788,-741301331376⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6733817792,-6733796800⟩,⟨101882738330,101883220792⟩,⟨-114340768851,-114340227568⟩,⟨-2111656024070,-2111640937257⟩,⟨1569848420575,1569866615475⟩,⟨-757768402411,-757745702366⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3366908896,-3366898400⟩,⟨50941369165,50941610396⟩,⟨-57170384426,-57170113784⟩,⟨-1055828012035,-1055820468628⟩,⟨784924210287,784933307738⟩,⟨-378884201206,-378872851183⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3366898400,3366908896⟩,⟨-50941610396,-50941369165⟩,⟨57170113784,57170384426⟩,⟨1055820468628,1055828012035⟩,⟨-784933307738,-784924210287⟩,⟨378872851183,378884201206⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765490282016,765490311776⟩,⟨-50941610396,-50941369165⟩,⟨57170113784,57170384426⟩,⟨1055820468628,1055828012035⟩,⟨-784933307738,-784924210287⟩,⟨378872851183,378884201206⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273199597042,273199602254⟩,⟨25315169831,25315289227⟩,⟨-28410660867,-28410526914⟩,⟨-522344973129,-522341256635⟩,⟨387433303167,387437791800⟩,⟨-185330941697,-185325332844⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530980564032,1530980623552⟩,⟨-101883220792,-101882738330⟩,⟨114340227568,114340768852⟩,⟨2111640937256,2111656024070⟩,⟨-1569866615476,-1569848420574⟩,⟨757745702366,757768402412⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1192708142360,1192708299306⟩,⟨-762457354373,-762454741346⟩,⟨855682229054,855685160292⟩,⟨10956602139469,10956671371254⟩,⟨-6309555651505,-6309460658911⟩,⟨-433039073002,-432909841992⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1285904656944,1285904970836⟩,⟨-1524914708745,-1524909482692⟩,⟨1711364458109,1711370320583⟩,⟨21913204278946,21913342742500⟩,⟨-12619111303007,-12618921317825⟩,⟨-866077997068,-865819832923⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨172179537728,172179806208⟩,⟨-1303876958979,-1303872172167⟩,⟨1463300293356,1463305663256⟩,⟨17190633654416,17190767974325⟩,⟨-9054683485527,-9054505666449⟩,⟨-2688006993144,-2687771776165⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59288680881,59288785673⟩,⟨-443185885623,-443184177284⟩,⟨497373554355,497375470727⟩,⟨5712188094082,5712232899994⟩,⟨-2930787468333,-2930725714135⟩,⟨-1078498655972,-1078414429760⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380408230896,380408252944⟩,⟨9934026446,9934314430⟩,⟨-11149010964,-11148687869⟩,⟨-207327489916,-207318483693⟩,⟨154664127535,154674976719⟩,⟨-75687470373,-75673950678⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177969484780,3177969668972⟩,⟨-82992289274,-82989873805⟩,⟨93137279669,93139989635⟩,⟨1736294249394,1736369941144⟩,⟨-1297035417153,-1296944349331⟩,⟨637647109624,637760445211⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨171364825867,171365138685⟩,⟨-1285435986828,-1285430836733⟩,⟨1442604084084,1442609861392⟩,⟨16670730154030,16670867067678⟩,⟨-8616016196504,-8615829705924⟩,⟨-2998588316629,-2998335744450⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨343544363595,343544944893⟩,⟨-2589312945807,-2589303008900⟩,⟨2905904377440,2905915524648⟩,⟨33861363808446,33861635042003⟩,⟨-17670699682031,-17670335372373⟩,⟨-5686595309773,-5686107520615⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523615839883,523616065075⟩,⟨70020319510,70023713138⟩,⟨-78585708800,-78581901858⟩,⟨-1442327693624,-1442236355794⟩,⟨1068757124776,1068880807672⟩,⟨-509526629920,-509359790938⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361342671075,361342904180⟩,⟨72480607023,72484135480⟩,⟨-81346973878,-81343015679⟩,⟨-1488160524141,-1488065186523⟩,⟨1100870485247,1100999278592⟩,⟨-521326064924,-521152659361⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722685342150,722685808360⟩,⟨144961214046,144968270960⟩,⟨-162693947756,-162686031358⟩,⟨-2976321048282,-2976130373046⟩,⟨2201740970494,2201998557184⟩,⟨-1042652129848,-1042305318722⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524267324425,1524267404790⟩,⟨-622541468,-621581422⟩,⟨697584102,698661196⟩,⟨22261044741,22290997529⟩,⟨-20133402806,-20097253376⟩,⟨16421935578,16467071036⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001868124949,1001868824085⟩,⟨200552440214,200562865185⟩,⟨-225086248716,-225074553971⟩,⟨-4111645400256,-4111360889226⟩,⟨3039252932413,3039634250958⟩,⟨-1434855312098,-1434344444747⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67882883580,67882886171⟩,⟨12580302058,12580361632⟩,⟨-14118597844,-14118531006⟩,⟨-258412148606,-258410285753⟩,⟨191225623362,191227869992⟩,⟨-90631477212,-90628674304⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50268628725,50268631363⟩,⟨265571486667,265571546443⟩,⟨37801311503,37801363955⟩,⟨-1280729798320,-1280727918918⟩,⟨-220510728487,-220508752183⟩,⟨-174689416595,-174687241248⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131765984307,2131766150062⟩,⟨-283728217070,-283726862460⟩,⟨318418944686,318420464454⟩,⟨5899457984056,5899500405826⟩,⟨-4393013615580,-4392962575110⟩,⟨2133979488354,2134043011492⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2968310845097,2968311191298⟩,⟨-592602740684,-592599888367⟩,⟨665058745017,665061945104⟩,⟨12361209494333,12361298951705⟩,⟨-9219630228844,-9219522846753⟩,⟨4506758908032,4506892229728⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135708356367,135708379318⟩,⟨689860276275,689860653099⟩,⟨132456656525,132456957933⟩,⟨-3178666152290,-3178655113401⟩,⟨-876555721966,-876544450222⟩,⟨-219828302220,-219815984862⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8908262155145,8908263661711⟩,⟨-45284319640767,-45284279588056⟩,⟨-8694833072065,-8694810345894⟩,⟨669051865200372,669053396952676⟩,⟨145937166057822,145938219716251⟩,⟨31402257218975,31403156500395⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8117152812637,8117159849824⟩,⟨-39637938566289,-39637788537889⟩,⟨-9746336068669,-9746214772579⟩,⟨559802547816410,559807553045160⟩,⟨165284959797089,165289682736704⟩,⟨20548043033607,20553217709524⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16234305625274,16234319699648⟩,⟨-79275877132578,-79275577075778⟩,⟨-19492672137338,-19492429545158⟩,⟨1119605095632820,1119615106090320⟩,⟨330569919594178,330579365473408⟩,⟨41096086067214,41106435419048⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10805181447606,10805181447704⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230896,2087019636287702⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9705669819830,9705669819928⟩,⟨-106185276415824,-106185276413897⟩,⟨0,0⟩,⟨2087019636230908,2087019636287687⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2394564936256,2394564994112⟩,⟨-12029251796733,-12029251796224⟩,⟨0,0⟩,⟨104822536628670,104822536664337⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7652389185441,7652389185588⟩,⟨-47652380707105,-47652380705224⟩,⟨-21210042406013,-21210042405148⟩,⟨593474621284510,593474621319930⟩,⟨317414307358763,317414307376911⟩,⟨117575279543832,117575279551149⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6552877557665,6552877557812⟩,⟨-47652380707105,-47652380705224⟩,⟨-21210042406014,-21210042405147⟩,⟨593474621284518,593474621319923⟩,⟨317414307358765,317414307376908⟩,⟨117575279543833,117575279551148⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1962670219904,1962670258496⟩,⟨-7995624245628,-7995624245094⟩,⟨-3558846941031,-3558846940788⟩,⟨41435493633998,41435493652910⟩,⟨27379298767630,27379298776727⟩,⟨8208926839176,8208926843012⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100498837339,100498837341⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135281250055,135281250059⟩,⟨701064132670,701064132677⟩,⟨312043171035,312043171040⟩,⟨-1760396448892,-1760396448888⟩,⟨-1567102536260,-1567102536248⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4357235156160,4357235252608⟩,⟨-20024876042361,-20024876041318⟩,⟨-3558846941031,-3558846940788⟩,⟨146258030262668,146258030317247⟩,⟨27379298767630,27379298776727⟩,⟨8208926839176,8208926843012⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨687088727190,687089889786⟩,⟨-5178625891614,-5178606017800⟩,⟨5811808754880,5811831049296⟩,⟨67722727616892,67723270084006⟩,⟨-35341399364062,-35340670744746⟩,⟨-11373190619546,-11372215041230⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5044323883350,5044325142394⟩,⟨-25203501933975,-25203482059118⟩,⟨2252961813849,2252984108508⟩,⟨213980757879560,213981300401253⟩,⟨-7962100596432,-7961371968019⟩,⟨-3164263780370,-3163288198218⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461067143476,461067258567⟩,⟨1714045433274,1714048252765⟩,⟨205927829357,205929867164⟩,⟨-30678523786714,-30678440019920⟩,⟨1066687726685,1066772082993⟩,⟨-289223708904,-289134537605⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33863195875,33863197811⟩,⟨-687494312691,-687494302916⟩,⟨321668947845,321668966201⟩,⟨8543123708759,8543123735004⟩,⟨-6530558220472,-6530558128119⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨494930339351,494930456378⟩,⟨1026551120583,1026553949849⟩,⟨527596777202,527598833365⟩,⟨-22135400077955,-22135316284916⟩,⟨-5463870493787,-5463786045126⟩,⟨-289223708904,-289134537605⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504862395711,504862407910⟩,⟨2536208829314,2536208952001⟩,⟨0,0⟩,⟨3381169318170,3381172243620⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨227257002584,227257061811⟩,⟨1613001363342,1613002999016⟩,⟨242256440203,242257390186⟩,⟨-3906090636369,-3906036957375⟩,⟨-1291852831260,-1291809192614⟩,⟨-132802759347,-132761811381⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-687089889786,-687088727190⟩,⟨5178606017800,5178625891614⟩,⟨-5811831049296,-5811808754880⟩,⟨-67723270084006,-67722727616892⟩,⟨35340670744746,35341399364062⟩,⟨11372215041230,11373190619546⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3670145266374,3670146525418⟩,⟨-14846270024561,-14846250149704⟩,⟨-9370677990327,-9370655695668⟩,⟨78534760178662,78535302700355⟩,⟨62719969512376,62720698140789⟩,⟨19581141880406,19582117462558⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451565792462,451565947386⟩,⟨513487284758,513490532975⟩,⟨-111352406160,-111349305708⟩,⟨-15145821832482,-15145727720636⟩,⟨-7702313690833,-7702202391372⟩,⟨-4073757983441,-4073624896125⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨315960359646,315960359652⟩,⟨1967524518296,1967524518298⟩,⟨875743831654,875743831656⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-315960359652,-315960359646⟩,⟨-1967524518298,-1967524518296⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨783551268124,783551268130⟩,⟨-1967524518298,-1967524518296⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1398668918877,1398668946391⟩,⟨-9210073923967,-9210073854479⟩,⟨-4099397671034,-4099397640097⟩,⟨58144002709806,58144002725452⟩,⟨36173586478977,36173586563677⟩,⟨11519106508025,11519106511205⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1398668946391,-1398668918877⟩,⟨9210073854479,9210073923967⟩,⟨4099397640097,4099397671034⟩,⟨-58144002725452,-58144002709806⟩,⟨-36173586563677,-36173586478977⟩,⟨-11519106511205,-11519106508025⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-299157318615,-299157291101⟩,⟨9210073854479,9210073923967⟩,⟨4099397640097,4099397671034⟩,⟨-58144002725452,-58144002709806⟩,⟨-36173586563677,-36173586478977⟩,⟨-11519106511205,-11519106508025⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12541968364,-12541967209⟩,⟨417619437038,417619442884⟩,⟨52727410034,52727422306⟩,⟨-4376800294330,-4376800278813⟩,⟨2018886400731,2018886462874⟩,⟨2782175413247,2782175438072⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439023824098,439023980177⟩,⟨931106721796,931109975859⟩,⟨-58624996126,-58621883402⟩,⟨-19522622126812,-19522527999449⟩,⟨-5683427290102,-5683315928498⟩,⟨-1291582570194,-1291449458053⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100498837341,-100498837339⟩,⟨-875743831656,-875743831654⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4213345821,4213345823⟩,⟨26135110097,26135110102⟩,⟨40022876823,40022876824⟩,⟨-276577690589,-276577690578⟩,⟨248259301866,248259301870⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9176010432,9176010659⟩,⟨10821914139,10821915551⟩,⟨87163587057,87163589166⟩,⟨-772525981749,-772525966707⟩,⟨102798145600,102798158703⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1484783266406,1484783287613⟩,⟨-7569013415553,-7569013029665⟩,⟨-1425348602865,-1425348533650⟩,⟨112151596217146,112151603984958⟩,⟨23917818560597,23917820139787⟩,⟨5321124621366,5321124922155⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12391307556,12391308041⟩,⟨-48553511766,-48553504866⟩,⟨105810633184,105810638587⟩,⟨-256251858510,-256251708277⟩,⟨-275635337795,-275635252375⟩,⟨-181580894644,-181580874591⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12391308041,-12391307556⟩,⟨48553504866,48553511766⟩,⟨-105810638587,-105810633184⟩,⟨256251708277,256251858510⟩,⟨275635252375,275635337795⟩,⟨181580874591,181580894644⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112890145382,-112890144895⟩,⟨-827190326790,-827190319888⟩,⟨-105810638587,-105810633184⟩,⟨2455274963829,2455275114062⟩,⟨275635252375,275635337795⟩,⟨181580874591,181580894644⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨82283622271,82283623897⟩,⟨-541828186550,-541828182432⟩,⟨632415829358,632415844755⟩,⟨3420608760094,3420608761166⟩,⟨-3624354504160,-3624354464835⟩,⟨-2490412272777,-2490412272384⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨111116010382,111116014165⟩,⟨-1298124779446,-1298124723361⟩,⟨747347796714,747347836994⟩,⟨20472099434722,20472100686339⟩,⟨-6755550435643,-6755549791683⟩,⟨-4604505370470,-4604505171981⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-111116014165,-111116010382⟩,⟨1298124723361,1298124779446⟩,⟨-747347836994,-747347796714⟩,⟨-20472100686339,-20472099434722⟩,⟨6755549791683,6755550435643⟩,⟨4604505171981,4604505370470⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨988395613611,988395617394⟩,⟨1298124723361,1298124779446⟩,⟨-747347836994,-747347796714⟩,⟨-20472100686339,-20472099434722⟩,⟨6755549791683,6755550435643⟩,⟨4604505171981,4604505370470⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121609804553,121609805023⟩,⟨789933118443,789933127768⟩,⟨188556397816,188556403854⟩,⟨-2445924238221,-2445924006550⟩,⟨-685655201136,-685655074862⟩,⟨-171182708643,-171182660130⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11590768567,11590768668⟩,⟨169860204674,169860206826⟩,⟨21727787882,21727789088⟩,⟨740451397608,740451451405⟩,⟨102607406286,102607433534⟩,⟨-16921700991,-16921694630⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨171137871210,171138021070⟩,⟨1672282563460,1672287939948⟩,⟨115324378904,115327233976⟩,⟨-1758813534945,-1758604611870⟩,⟨421824158681,421969012778⟩,⟨-587026460435,-586907415287⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-171138021070,-171137871210⟩,⟨-1672287939948,-1672282563460⟩,⟨-115327233976,-115324378904⟩,⟨1758604611870,1758813534945⟩,⟨-421969012778,-421824158681⟩,⟨586907415287,587026460435⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56118981514,56119190601⟩,⟨-59286576606,-59279564444⟩,⟨126929206227,126933011282⟩,⟨-2147486024499,-2147223422430⟩,⟨-1713821844038,-1713633351295⟩,⟨454104655940,454264649054⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28978855144983,28978880838090⟩,⟨-259566083028473,-259565442276688⟩,⟨-87341638268645,-87341158989312⟩,⟨3763313997170862,3763336800284131⟩,⟨1392679612768307,1392699571592774⟩,⟨320747347315820,320767498312492⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13450466725,13450466830⟩,⟨174738692554,174738695294⟩,⟨41709984880,41709986380⟩,⟨593983644468,593983724607⟩,⟨119261218070,119261258466⟩,⟨26804663022,26804678044⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨354502050737,354502367812⟩,⟨1430127913207,1430139931860⟩,⟨30851698762,30858584393⟩,⟨-20810313522580,-20809813262318⟩,⟨-3547227016263,-3546877825212⟩,⟨-1996401912091,-1996117748199⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-354502367812,-354502050737⟩,⟨-1430139931860,-1430127913207⟩,⟨-30858584393,-30851698762⟩,⟨20809813262318,20810313522580⟩,⟨3546877825212,3547227016263⟩,⟨1996117748199,1996401912091⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84521456286,84521929440⟩,⟨-499033210064,-499017937348⟩,⟨-89483580519,-89473582164⟩,⟨1287191135506,1287785523131⟩,⟨-2136549464890,-2136088912235⟩,⟨704535178005,704952454038⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235780087394,235780087400⟩,⟨1576807964324,1576807964333⟩,⟨312043171035,312043171040⟩,⟨-3959419704444,-3959419704440⟩,⟨-1567102536260,-1567102536248⟩,⟨-348758139209,-348758139207⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1666826129687,-1666824677437⟩,⟨-4074027706199,-4073986172940⟩,⟨439048982355,439075332867⟩,⟨40579972828435,40581487250916⟩,⟨-7578144198451,-7576957529992⟩,⟨2212200859646,2213312980068⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-184356759418,-184356598080⟩,⟨-1648116170217,-1648110517260⟩,⟨-237285421400,-237282248551⟩,⟨2342340085798,2342570932762⟩,⟨-181966716921,-181808287036⟩,⟨654770506646,654902854196⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51423327976,51423489320⟩,⟨-71308205893,-71302552927⟩,⟨74757749635,74760922489⟩,⟨-1617079618646,-1616848771678⟩,⟨-1749069253181,-1748910823284⟩,⟨306012367437,306144714989⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4313968059,4314008282⟩,⟨-30028200561,-30026761592⟩,⟨5190027190,5190901648⟩,⟨-45575393185,-45515687937⟩,⟨-293581969097,-293538229104⟩,⟨50206420187,50243274222⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2405030190,2405045283⟩,⟨-6670082738,-6669533040⟩,⟨6992726918,6993045644⟩,⟨-142011817745,-141988283659⟩,⟨-173302962712,-173286449838⟩,⟨38789758883,38803091254⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4293070680,4293097707⟩,⟨-29395788615,-29394697390⟩,⟨4697748253,4698366291⟩,⟨-65860692995,-65810115150⟩,⟨-278729611232,-278695656169⟩,⟨41927581400,41953557525⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4293097707,-4293070680⟩,⟨29394697390,29395788615⟩,⟨-4698366291,-4697748253⟩,⟨65810115150,65860692995⟩,⟨278695656169,278729611232⟩,⟨-41953557525,-41927581400⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨20870352,20937602⟩,⟨-633503171,-630972977⟩,⟨491660899,493153395⟩,⟨20234721965,20345005058⟩,⟨-14886312928,-14808617872⟩,⟨8252862662,8315692822⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56118981514,56119190601⟩,⟨-59286576606,-59279564444⟩,⟨126929206227,126933011282⟩,⟨-2147486024499,-2147223422430⟩,⟨-1713821844038,-1713633351295⟩,⟨454104655940,454264649054⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨20870352,20937602⟩,⟨-633503171,-630972977⟩,⟨491660899,493153395⟩,⟨20234721965,20345005058⟩,⟨-14886312928,-14808617872⟩,⟨8252862662,8315692822⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨111669149696,112098646426⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨113816633344,117682103911⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112098646426,-111669149696⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437657167462,438086664192⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨45304355225,46888963278⟩,⟨-117682103911,-113816633344⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156973504921,158987609704⟩,⟨981829523865,985694994432⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44874858495,47318460008⟩,⟨-117682103911,-113816633344⟩,⟨437657167462,438086664192⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2140248186688,-2126230209728⟩,⟨6790044708471,6904242269191⟩,⟨3026708468036,3068552119641⟩,⟨-43354303954113,-41931986873394⟩,⟨-26970043678572,-26295367050601⟩,⟨-8563813126739,-8331848357994⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309476439157,-303554596293⟩,⟨-949307657722,-900314825455⟩,⟨-420642347352,-402631598451⟩,⟨5857632977708,6392604648097⟩,⟨3631917505985,3887966856784⟩,⟨1171230115447,1255743049807⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨303554596293,309476439157⟩,⟨900314825455,949307657722⟩,⟨402631598451,420642347352⟩,⟨-6392604648097,-5857632977708⟩,⟨-3887966856784,-3631917505985⟩,⟨-1255743049807,-1171230115447⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158987609704,-156973504921⟩,⟨-985694994432,-981829523865⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940524018072,942538122855⟩,⟨-985694994432,-981829523865⟩,⟨-438086664192,-437657167462⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-171726343424,-169374288768⟩,⟨-1152318374645,-1145346752354⟩,⟨-512141499843,-510546080773⟩,⟨-1207661295253,-1193092596740⟩,⟨745889680688,753545630058⟩,⟨-238550379310,-237066433868⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147209562216,-144883039529⟩,⟨-836559884623,-825781473835⟩,⟨-371605907672,-368299725191⟩,⟨1010270082383,1045497506077⟩,⟨1378112282437,1394843920359⟩,⟨201949184355,205325748166⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144883039529,147209562216⟩,⟨825781473835,836559884623⟩,⟨368299725191,371605907672⟩,⟨-1045497506077,-1010270082383⟩,⟨-1394843920359,-1378112282437⟩,⟨-205325748166,-201949184355⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨448437635822,456686001373⟩,⟨1726096299290,1785867542345⟩,⟨770931323642,792248255024⟩,⟨-7438102154174,-6867903060091⟩,⟨-5282810777143,-5010029788422⟩,⟨-1461068797973,-1373179299802⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨809155431972,819290358583⟩,⟨4113606829570,4187474946379⟩,⟨770931323642,792248255024⟩,⟨-19572262403141,-18792007214236⟩,⟨-5282810777143,-5010029788422⟩,⟨-1461068797973,-1373179299802⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89749716990,94636920016⟩,⟨-235364207822,-227633266688⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12774357189670,13469968041786⟩,⟨30726577496734,35324327071649⟩,⟨-131499319755102,-118152386676013⟩,⟨147815275656498,185272612257713⟩,⟨-392870631782055,-238354061005736⟩,⟨2185626449920643,2567499943936254⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9400937879010,10037015224095⟩,⟨70405130887760,77621766010216⟩,⟨-89028592573115,-77245282957863⟩,⟨98918373832828,188789019091184⟩,⟨-836731886927915,-650208877706605⟩,⟨1401049986246810,1731506668115831⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨83142566912,88717159168⟩,⟨-726074010681,-578075525605⟩,⟨634237973615,832773468029⟩,⟨6226551907148,11032055736112⟩,⟨-8246132682985,-942197417778⟩,⟨-6575582302112,4077541171451⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1182654194688,1188228786944⟩,⟨-726074010681,-578075525605⟩,⟨634237973615,832773468029⟩,⟨6226551907148,11032055736112⟩,⟨-8246132682985,-942197417778⟩,⟨-6575582302112,4077541171451⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨80149035968,85319548736⟩,⟨-675029793964,-534914461860⟩,⟨586883632536,774228101093⟩,⟨5347231485929,9996246890319⟩,⟨-7380895786348,-396523268585⟩,⟨-6658485512283,3477623769511⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨86209723656,92203794245⟩,⟨-785838110618,-617502362921⟩,⟨677495292594,901320139631⟩,⟨6767931878994,12550409804297⟩,⟨-9638863931459,-1112304971960⟩,⟨-7028922578814,5247438718817⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-88717159168,-83142566912⟩,⟨578075525605,726074010681⟩,⟨-832773468029,-634237973615⟩,⟨-11032055736112,-6226551907148⟩,⟨942197417778,8246132682985⟩,⟨-4077541171451,6575582302112⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1010794468608,1016369060864⟩,⟨578075525605,726074010681⟩,⟨-832773468029,-634237973615⟩,⟨-11032055736112,-6226551907148⟩,⟨942197417778,8246132682985⟩,⟨-4077541171451,6575582302112⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-92501344000,-86454131328⟩,⟨625364138490,789801331689⟩,⟨-905865771766,-686120872445⟩,⟨-12567666499174,-7091591237320⟩,⟨1409514275508,9620595150829⟩,⟨-5181750666171,6724563985765⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-85506602891,-79478338861⟩,⟨513820659962,684624519954⟩,⟨-787496401841,-560698497450⟩,⟨-10470158353758,-4548158151516⟩,⟨-594355070427,8097557866835⟩,⟨-4551560264325,7931320198761⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨703120765,12725455384⟩,⟨-272017450656,67122157033⟩,⟨-110001109247,340621642181⟩,⟨-3702226474764,8002251652781⟩,⟨-10233219001886,6985252894875⟩,⟨-11580482843139,13178758917578⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨351560382,6362727692⟩,⟨-136008725328,33561078517⟩,⟨-55000554624,170310821091⟩,⟨-1851113237382,4001125826391⟩,⟨-5116609500943,3492626447438⟩,⟨-5790241421570,6589379458789⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6362727692,-351560382⟩,⟨-33561078517,136008725328⟩,⟨-170310821091,55000554624⟩,⟨-4001125826391,1851113237382⟩,⟨-3492626447438,5116609500943⟩,⟨-6589379458789,5790241421570⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755760655924,761771842498⟩,⟨-33561078517,136008725328⟩,⟨-170310821091,55000554624⟩,⟨-4001125826391,1851113237382⟩,⟨-3492626447438,5116609500943⟩,⟨-6589379458789,5790241421570⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6287051685,7158391173⟩,⟨-117170609108,-87425511206⟩,⟨95919264202,134389295116⟩,⟨1549529446264,2739245453409⟩,⟨-2430585732652,-809403285178⟩,⟨-329435669381,1919505881552⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7158391173,-6287051685⟩,⟨87425511206,117170609108⟩,⟨-134389295116,-95919264202⟩,⟨-2739245453409,-1549529446264⟩,⟨809403285178,2430585732652⟩,⟨-1919505881552,329435669381⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092353236603,1093224576091⟩,⟨87425511206,117170609108⟩,⟨-134389295116,-95919264202⟩,⟨-2739245453409,-1549529446264⟩,⟨809403285178,2430585732652⟩,⟨-1919505881552,329435669381⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7181795264,-6305095296⟩,⟨87928288695,117938449607⟩,⟨-135269972824,-96470888620⟩,⟨-2769846827886,-1565472325416⟩,⟨821772909257,2461023458702⟩,⟨-1948726658485,323130188950⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3590897632,-3152547648⟩,⟨43964144347,58969224804⟩,⟨-67634986412,-48235444310⟩,⟨-1384923413943,-782736162708⟩,⟨410886454628,1230511729351⟩,⟨-974363329243,161565094475⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3152547648,3590897632⟩,⟨-58969224804,-43964144347⟩,⟨48235444310,67634986412⟩,⟨782736162708,1384923413943⟩,⟨-1230511729351,-410886454628⟩,⟨-161565094475,974363329243⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765275931264,765714300512⟩,⟨-58969224804,-43964144347⟩,⟨48235444310,67634986412⟩,⟨782736162708,1384923413943⟩,⟨-1230511729351,-410886454628⟩,⟨-161565094475,974363329243⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273088309150,273306144023⟩,⟨21856377801,29292652277⟩,⟨-33597323779,-23979816050⟩,⟨-684811363353,-387382361566⟩,⟨202350821294,607646433163⟩,⟨-479876470388,82358917346⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530551862528,1531428601024⟩,⟨-117938449608,-87928288694⟩,⟨96470888620,135269972824⟩,⟨1565472325416,2769846827886⟩,⟨-2461023458702,-821772909256⟩,⟨-323130188950,1948726658486⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1189455549332,1196015468189⟩,⟨-859121982555,-676521126369⟩,⟨742247975033,985373367380⟩,⟨8056490152905,14287851825397⟩,⟨-11172805726664,-1946982449515⟩,⟨-6854151597830,6448381059236⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1279399470888,1292519308602⟩,⟨-1718243965109,-1353042252739⟩,⟨1484495950066,1970746734760⟩,⟨16112980305817,28575703650784⟩,⟨-22345611453320,-3893964899030⟩,⟨-13703606492607,12896762118468⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨166603167296,177820892736⟩,⟨-1476653118892,-1150996878620⟩,⟨1262821025279,1693653154920⟩,⟨11723724429025,23352971223060⟩,⟨-17881790442786,-1037901802229⟩,⟨-14385683693623,9633047636509⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57148900763,61465683576⟩,⟨-505751977882,-386371930900⟩,⟨422208008537,581406195200⟩,⟨3777413108151,7836998143942⟩,⟨-6056698869440,-19301260332⟩,⟨-5345414263763,3375549409696⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380146793944,380667957682⟩,⟨1108689371,18960616046⟩,⟨-22834529499,243528627⟩,⟨-571287253267,145759052672⟩,⟨-326224287216,649447779614⟩,⟨-756971927168,594899631355⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175801364990,3180155242327⟩,⟨-158616890836,-9249470954⟩,⟨-2037262585,191024493299⟩,⟨-1219307755201,4794982176154⟩,⟨-5452074509430,2729264455733⟩,⟨-4976935887184,6355471596294⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨165067428543,177779307567⟩,⟨-1471670929643,-1116467594913⟩,⟨1219380963524,1692299893555⟩,⟨10848921731155,23081192194959⟩,⟨-17994525483830,94209358754⟩,⟨-15741104028997,10320527694395⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨331670595839,355600200303⟩,⟨-2948324048535,-2267464473533⟩,⟨2482201988803,3385953048475⟩,⟨22572646160180,46434163418019⟩,⟨-35876315926616,-943692443475⟩,⟨-30126787722620,19953575330904⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519479880533,527776446709⟩,⟨-46504073214,188461157976⟩,⟨-235992025374,76211788536⟩,⟨-5552482602700,2598652490413⟩,⟨-4881709613454,7103462125458⟩,⟨-9147644815784,8076037651333⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357069852953,365658012231⟩,⟨-48328948018,195856596589⟩,⟨-245252631409,79202429207⟩,⟨-5778997359473,2735595431893⟩,⟨-5117061711656,7396351383667⟩,⟨-9524316653533,8447782525791⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714139705906,731316024462⟩,⟨-96657896036,391713193178⟩,⟨-490505262818,158404858414⟩,⟨-11557994718946,5471190863786⟩,⟨-10234123423312,14792702767334⟩,⟨-19048633307066,16895565051582⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523393471355,1525141549339⟩,⟨-30512938402,29242320414⟩,⟨-37918406496,39350708622⟩,⟨-1173773127993,1220317381622⟩,⟨-1651620173524,1608812823396⟩,⟨-2242636070502,2278162327867⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989453624799,1014414424030⟩,⟨-154369967389,562798453622⟩,⟨-705604447637,245897931540⟩,⟨-16834639347108,8421636605131⟩,⟨-15320929201453,21616776543118⟩,⟨-27949264467201,24985077500161⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67827590641,67935842127⟩,⟨10857040720,14562577858⟩,⟨-16702606466,-11911847502⟩,⟨-339578858714,-190869349600⟩,⟨98726539214,301132589192⟩,⟨-237520282376,42997232034⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49915855383,50621729731⟩,⟨261753551574,269583885260⟩,⟨35112070500,40184673952⟩,⟨-1381111924187,-1188799327615⟩,⟨-309754611229,-118749724558⟩,⟨-291331378476,-69375035759⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130572287467,2133013877060⟩,⟨-328535524914,-244797422108⟩,⟨268580512522,376815124114⟩,⟨4372428461198,7741131649850⟩,⟨-6884575201768,-2303292743782⟩,⟨-883199719941,5461758893820⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2965818005425,2970917610320⟩,⟨-686389329494,-511147596193⟩,⟨560807716756,787256965442⟩,⟨9159184369481,16225936701617⟩,⟨-14444153332194,-4841592486334⟩,⟨-1809874526994,11480459152371⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134642816784,136781626064⟩,⟨674451422231,705219593044⟩,⟨120170814428,144825812498⟩,⟨-3652585491609,-2702988118198⟩,⟨-1393557227270,-363414038105⟩,⟨-834696276554,398975588874⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8838364145846,8978762094335⟩,⟨-47028123010559,-43580760368880⟩,⟨-9657823169464,-7765029910673⟩,⟨604439406629371,736214571770747⟩,⟨100059174116848,194100150927066⟩,⟨-12961917251454,76438860304565⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7953668902155,8283846708244⟩,⟨-44648966221453,-34622560539312⟩,⟨-14672413813854,-4979736299901⟩,⟨358318930379934,761212515443498⟩,⟨-50530245023150,387139168416856⟩,⟨-244516040462904,286950085135291⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15907337804310,16567693416488⟩,⟨-89297932442906,-69245121078624⟩,⟨-29344827627708,-9959472599802⟩,⟨716637860759868,1522425030886996⟩,⟨-101060490046300,774278336833712⟩,⟨-489032080925808,573900170270582⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10784481866270,10825960642718⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533866,2099083303790624⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9684970238494,9726449014942⟩,⟨-106594074020613,-105778825967633⟩,⟨0,0⟩,⟨2075048233533869,2099083303790615⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2392217469760,2396916459264⟩,⟨-12101371604921,-11957606413725⟩,⟨0,0⟩,⟨101381360168522,108260423343400⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7603899586045,7701464143411⟩,⟨-48360356480404,-46957955553786⟩,⟨-21493491769069,-20931827081930⟩,⟨579978618822950,607345313919961⟩,⟨311115738756856,323875700561304⟩,⟨115241233798497,119969444724931⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6504387958269,6601952515635⟩,⟨-48360356480405,-46957955553785⟩,⟨-21493491769070,-20931827081930⟩,⟨579978618822955,607345313919963⟩,⟨311115738756857,323875700561306⟩,⟨115241233798496,119969444724932⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1954503866304,1970873897280⟩,⟨-8174908171987,-7820537640261⟩,⟨-3633292520884,-3486057679538⟩,⟨35810878054645,47041143364627⟩,⟨24800613866275,29953027391617⟩,⟨7186596171709,9227093676143⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100284130918,100713627649⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134275389045,136289493829⟩,⟨697328648843,704798265510⟩,⟨311026020513,313059720235⟩,⟨-1767320322048,-1753486165276⟩,⟨-1571040316622,-1563164755880⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4346721336064,4367790356544⟩,⟨-20276279776908,-19778144053986⟩,⟨-3633292520884,-3486057679538⟩,⟨137192238223167,155301566708027⟩,⟨24800613866275,29953027391617⟩,⟨7186596171709,9227093676143⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨663341191678,711200400606⟩,⟨-5896648097070,-4534928947066⟩,⟨4964403977606,6771906096950⟩,⟨45145292320360,92868326836038⟩,⟨-71752631853232,-1887384886950⟩,⟨-60253575445240,39907150661808⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5010062527742,5078990757150⟩,⟨-26172927873978,-24313073001052⟩,⟨1331111456722,3285848417412⟩,⟨182337530543527,248169893544065⟩,⟨-46952017986957,28065642504667⟩,⟨-53066979273531,49134244337951⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨456957210589,465227989433⟩,⟨1591078250397,1829776775292⟩,⟨121407861654,300978821563⟩,⟨-35240464661193,-25999103314401⟩,⟨-3241045412741,5189181514102⟩,⟨-4860856271091,4500623607844⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32851467099,34881929444⟩,⟨-708066170644,-667109368834⟩,⟨320394994437,322946015318⟩,⟨8207475458881,8886324900775⟩,⟨-6562818552468,-6498504886492⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨489808677688,500109918877⟩,⟨883012079753,1162667406458⟩,⟨441802856091,623924836881⟩,⟨-27032989202312,-17112778413626⟩,⟨-9803863965209,-1309323372390⟩,⟨-4860856271091,4500623607844⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨504367106722,505357825907⟩,⟨2516159178967,2556424289217⟩,⟨0,0⟩,⟨2234856254543,4531068346710⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨224684650322,229860653525⟩,⟨1525949163049,1697168242278⟩,⟨202663457701,286768498969⟩,⟨-7387900736804,-382486102220⟩,⟨-3495018124613,850047369161⟩,⟨-2234148048233,2068577816032⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-711200400606,-663341191678⟩,⟨4534928947066,5896648097070⟩,⟨-6771906096950,-4964403977606⟩,⟨-92868326836038,-45145292320360⟩,⟨1887384886950,71752631853232⟩,⟨-39907150661808,60253575445240⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3635520935458,3704449164866⟩,⟨-15741350829842,-13881495956916⟩,⟨-10405198617834,-8450461657144⟩,⟨44323911387129,110156274387667⟩,⟨26687998753225,101705659244849⟩,⟨-32720554490099,69480669121383⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443979832189,459183412745⟩,⟨354495718947,679343498566⟩,⟨-261368444416,22759916242⟩,⟨-20722192283641,-9751258789605⟩,⟨-13185714486562,-1847875713126⟩,⟨-11157307471538,2679538873581⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨313947009842,317975219408⟩,⟨1963659047730,1971389988864⟩,⟨875314334924,876173328384⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-317975219408,-313947009842⟩,⟨-1971389988864,-1963659047730⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨781536408368,785564617934⟩,⟨-1971389988864,-1963659047730⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1389267646857,1408124080729⟩,⟨-9374416263367,-9049485106304⟩,⟨-4166407228164,-4033869345285⟩,⟨53388470411077,62924047665263⟩,⟨33989126266628,38370953059086⟩,⟨10658713180392,12383012581606⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1408124080729,-1389267646857⟩,⟨9049485106304,9374416263367⟩,⟨4033869345285,4166407228164⟩,⟨-62924047665263,-53388470411077⟩,⟨-38370953059086,-33989126266628⟩,⟨-12383012581606,-10658713180392⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-308612452953,-289756019081⟩,⟨9049485106304,9374416263367⟩,⟨4033869345285,4166407228164⟩,⟨-62924047665263,-53388470411077⟩,⟨-38370953059086,-33989126266628⟩,⟨-12383012581606,-10658713180392⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13281411169,-11825941650⟩,⟨399334947524,436467511294⟩,⟨41673334648,63968559733⟩,⟨-4714703291586,-4052493669908⟩,⟨1794611448218,2238949555478⟩,⟨2678424223192,2885086944658⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430698421020,447357471095⟩,⟨753830666471,1115811009860⟩,⟨-219695109768,86728475975⟩,⟨-25436895575227,-13803752459513⟩,⟨-11391103038344,391073842352⟩,⟨-8478883248346,5564625818239⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-100713627649,-100284130918⟩,⟨-876173328384,-875314334924⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4092940966,4334300468⟩,⟨24945088919,27325923330⟩,⟨39917784923,40128086017⟩,⟨-282192773125,-270967137892⟩,⟨247702508009,248816179610⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8905048963,9448700559⟩,⟨6569368347,15057756400⟩,⟨86849488477,87478538129⟩,⟨-839287973299,-705355185281⟩,⟨97273538155,108293929972⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1475576768296,1494058832020⟩,⟨-7731930949600,-7408780791844⟩,⟨-1462840705014,-1388480090360⟩,⟨108243275261427,116166365656270⟩,⟨22966224040097,24895152289798⟩,⟨5086202977563,5562329010983⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11950836206,12839258963⟩,⟨-57628397345,-39543357858⟩,⟨103983569485,107623781620⟩,⟨-475561144850,-36858674076⟩,⟨-318646191529,-232417657824⟩,⟨-191577279320,-171549609131⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12839258963,-11950836206⟩,⟨39543357858,57628397345⟩,⟨-107623781620,-103983569485⟩,⟨36858674076,475561144850⟩,⟨232417657824,318646191529⟩,⟨171549609131,191577279320⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113552886612,-112234967124⟩,⟨-836629970526,-817685937579⟩,⟨-107623781620,-103983569485⟩,⟨2235881929628,2674584400402⟩,⟨232417657824,318646191529⟩,⟨171549609131,191577279320⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨79770038090,84818309633⟩,⟨-562759534825,-521504780300⟩,⟨621622183710,642992041438⟩,⟨3080661022606,3774398689482⟩,⟨-3855003916685,-3389513442443⟩,⟨-2601970222486,-2378132554592⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨107053724615,115254392426⟩,⟨-1361154469717,-1237384880670⟩,⟨721388984927,772987576725⟩,⟨19015488964964,22004900709138⟩,⟨-7435171158979,-6068291892003⟩,⟨-4877583568248,-4332423356357⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-115254392426,-107053724615⟩,⟨1237384880670,1361154469717⟩,⟨-772987576725,-721388984927⟩,⟨-22004900709138,-19015488964964⟩,⟨6068291892003,7435171158979⟩,⟨4332423356357,4877583568248⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨984257235350,992457903161⟩,⟨1237384880670,1361154469717⟩,⟨-772987576725,-721388984927⟩,⟨-22004900709138,-19015488964964⟩,⟨6068291892003,7435171158979⟩,⟨4332423356357,4877583568248⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120200205125,123019695156⟩,⟨775345237607,804897047093⟩,⟨182607914669,194480714441⟩,⟨-2753313262081,-2146875890697⟩,⟨-822465637465,-547645937232⟩,⟨-226202318597,-115423242509⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11456620855,11727259387⟩,⟨166934031442,172807173258⟩,⟨21228684094,22229853260⟩,⟨663755624119,816736378908⟩,⟨88844367656,116335091772⟩,⟨-19902600533,-13953442922⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨165750259872,176709034477⟩,⟨1462700322647,1882382246962⟩,⟨-5859470760,231189453202⟩,⟨-10999259187020,7518407731938⟩,⟨-6209995134626,7162279248672⟩,⟨-6702438140212,5534694568075⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-176709034477,-165750259872⟩,⟨-1882382246962,-1462700322647⟩,⟨-231189453202,5859470760⟩,⟨-7518407731938,10999259187020⟩,⟨-7162279248672,6209995134626⟩,⟨-5534694568075,6702438140212⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47975615845,64110393653⟩,⟨-356433083913,234467919631⟩,⟨-28525995501,292627969729⟩,⟨-14906308468742,10616773084800⟩,⟨-10657297373285,7060042503787⟩,⟨-7768842616308,8771015956244⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28277057245875,29697579968974⟩,⟨-283247878937091,-236235601665440⟩,⟨-107347870080099,-68139092778784⟩,⟨2777046898226032,4765639269412704⟩,⟨468039777021736,2352493829011500⟩,⟨-709462582000273,1361689291911857⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13140460680,13764152206⟩,⟨169523730806,180113037214⟩,⟨39925923920,43519245454⟩,⟨477391002840,709049952966⟩,⟨73495730230,165000162780⟩,⟨10037747819,43562705950⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨337944183125,371766883148⟩,⟨813966219373,2041521557856⟩,⟨-317017826540,361103232199⟩,⟨-47332271816176,5963530253433⟩,⟨-21312174457034,14822099523698⟩,⟨-17120973650324,13274232647968⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-371766883148,-337944183125⟩,⟨-2041521557856,-813966219373⟩,⟨-361103232199,317017826540⟩,⟨-5963530253433,47332271816176⟩,⟨-14822099523698,21312174457034⟩,⟨-13274232647968,17120973650324⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58931537872,109413287970⟩,⟨-1287690891385,301844790487⟩,⟨-580798341967,403746302515⟩,⟨-31400425828660,33528519356663⟩,⟨-26213202562042,21703248299386⟩,⟨-21753115896314,22685599468563⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234559519963,237003121478⟩,⟨1572642983767,1580971593894⟩,⟨311026020513,313059720235⟩,⟨-3966343577600,-3952509420828⟩,⟨-1571040316622,-1563164755880⟩,⟨-349100310528,-348416135658⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1711040942560,-1623775038294⟩,⟨-5538190604934,-2607674495745⟩,⟨-605065668781,1526212252759⟩,⟨-21889085709105,103044404382370⟩,⟨-62646284681412,46308092560484⟩,⟨-54904267341471,59136619442962⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-191441117889,-177513441194⟩,⟨-1872211507414,-1430116073764⟩,⟨-370345750590,-98916650637⟩,⟨-7386999366508,12136139894897⟩,⟨-7622984300835,7145301008932⟩,⟨-6186594017149,7508468137041⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43118402074,59489680284⟩,⟨-299568523647,150855520130⟩,⟨-59319730077,214143069598⟩,⟨-11353342944108,8183630474069⟩,⟨-9194024617457,5582136253052⟩,⟨-6535694327677,7160052001383⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2571393290,6379676927⟩,⟨-110551705441,40932076765⟩,⟨-36703871318,52661310029⟩,⟨-3863430075099,3846338492153⟩,⟨-3062552052646,2236638672862⟩,⟨-2350617357414,2410473215038⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1690929454,3218721814⟩,⟨-32416638888,16324241482⟩,⟨-6419053130,23172656704⟩,⟨-1310760685283,1048798114108⟩,⟨-1111584621368,662810935216⟩,⟨-730341116787,858210948785⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3005814647,5769556816⟩,⟨-82038116201,17234055112⟩,⟨-22142287120,36175794431⟩,⟨-2537207093988,2499716422994⟩,⟨-2180606417416,1430618372274⟩,⟨-1451230033699,1607777085587⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5769556816,-3005814647⟩,⟨-17234055112,82038116201⟩,⟨-36175794431,22142287120⟩,⟨-2499716422994,2537207093988⟩,⟨-1430618372274,2180606417416⟩,⟨-1607777085587,1451230033699⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3198163526,3373862280⟩,⟨-127785760553,122970192966⟩,⟨-72879665749,74803597149⟩,⟨-6363146498093,6383545586141⟩,⟨-4493170424920,4417245090278⟩,⟨-3958394443001,3861703248737⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47975615845,64110393653⟩,⟨-356433083913,234467919631⟩,⟨-28525995501,292627969729⟩,⟨-14906308468742,10616773084800⟩,⟨-10657297373285,7060042503787⟩,⟨-7768842616308,8771015956244⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3198163526,3373862280⟩,⟨-127785760553,122970192966⟩,⟨-72879665749,74803597149⟩,⟨-6363146498093,6383545586141⟩,⟨-4493170424920,4417245090278⟩,⟨-3958394443001,3861703248737⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (521/5120) u, BivariateJet2.affineZ (539/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000033

end


