-- Prove2me | Definitions.Def_GeneralCK_RB2Cell003361_data
-- name    : GeneralCK_RB2Cell003361_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T23:26:14.288561+00:00
-- url     : https://prove2.me/theorems/2746300b-752f-4c31-87f3-b26783bf1bcb
-- title:
--   Exact certificate data for RB2 cell 003361
-- statement:
--   For RB2 cell 003361, the entropy coordinates are $e=H(u)$ and $f=H(u+\rho(1/2-u))$, with $$\frac{75}{512}\le u\le\frac{47}{320},\qquad \frac{109}{640}\le\rho\le\frac{227}{1280}.$$ This bundle stores the source's exact dyadic endpoints, proposed logarithm enclosures, input and register jet records, center and whole-cell instruction lists, and their affine-coordinate real semantics. Endpoint intervals at precision $40$ are lifted exactly to precision $64$ for logarithm checks. All integer data and program definitions are preserved from the release source. Separate theorem proofs check these proposals and use them to establish positivity of the correction matrix's first diagonal entry and determinant. The data bundle itself introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell003361Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2110517076928,-2110517038016⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2110517076928,-2110517038016⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-174404852288,-174404852224⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-174404852288,-174404852224⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-1725961083264,-1725961044672⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-1725961083264,-1725961044672⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-256533637632,-256533637568⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-256533637632,-256533637568⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨95927514624,95927514688⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-105103723264,-105103723200⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨95927637312,95927637376⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-105103870592,-105103870528⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-9176233216,-9176233152⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-9176208640,-9176208576⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨201031237888,201031237952⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨201031507904,201031507968⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1936112185792,1936112224384⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1936112185792,1936112224384⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1469427407936,1469427433024⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1469427407936,1469427433088⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2111982115968,-2111982077056⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2109053987328,-2109053948480⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-174656543168,-174656543104⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-174153219008,-174153218944⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-1733759445184,-1733759406592⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-1718210437440,-1718210398848⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-258579453312,-258579453248⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-254493524608,-254493524544⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨92853392512,92853392576⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-101424193920,-101424193856⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨99029748160,99029748224⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-108839922368,-108839922304⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-9810174144,-9810174080⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-8570801344,-8570801280⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨194277586368,194277586432⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨207869670528,207869670592⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1934397405376,1934397443968⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1937828858112,1937828896704⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1459630946496,1459630970432⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1479265882752,1479265909312⟩



end LaneCBRB2Cell003361Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell003361
open Set LaneCBRB2Cell003361Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨161276021964,161276021965⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨191126044672,191126044672⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-161276021965,-161276021964⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨388479791923,388479791924⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨67528713830,67528713831⟩,⟨-191126044672,-191126044672⟩,⟨388479791923,388479791924⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨228804735794,228804735796⟩,⟨908385583104,908385583104⟩,⟨388479791923,388479791924⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨67528713829,67528713832⟩,⟨-191126044672,-191126044672⟩,⟨388479791923,388479791924⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2110517076928,-2110517038016⟩,⟨7496004706000,7496004706047⟩,⟨0,0⟩,⟨-51104586012188,-51104586011546⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-309569985308,-309569979598⟩,⟨-1011005449159,-1011005410233⟩,⟨0,0⟩,⟨7496004705906,7496004706141⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨309569979598,309569985308⟩,⟨1011005410233,1011005449159⟩,⟨0,0⟩,⟨-7496004706141,-7496004705906⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨938235605811,938235605812⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-174404852288,-174404852224⟩,⟨-1288509849901,-1288509849898⟩,⟨0,0⟩,⟨-1509995521058,-1509995521050⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148823203057,-148823203001⟩,⟨-925106775554,-925106775486⟩,⟨0,0⟩,⟨1288509849892,1288509849907⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨148823203001,148823203057⟩,⟨925106775486,925106775554⟩,⟨0,0⟩,⟨-1288509849907,-1288509849892⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨458393182599,458393188365⟩,⟨1936112185719,1936112224713⟩,⟨0,0⟩,⟨-8784514556048,-8784514555798⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-1725961083264,-1725961044672⟩,⟨4365209083859,4365209083900⟩,⟨1866823459266,1866823459289⟩,⟨-17330467331846,-17330467331527⟩,⟨-12695197615352,-12695197615148⟩,⟨-3169616164223,-3169616164148⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-359166797035,-359166789000⟩,⟨-517554921243,-517554889340⟩,⟨-221337317384,-221337303738⟩,⟨3606412973512,3606412973680⟩,⟨2168766454489,2168766493186⟩,⟨659586647993,659586648036⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨359166789000,359166797035⟩,⟨517554889340,517554921243⟩,⟨221337303738,221337317384⟩,⟨-3606412973680,-3606412973512⟩,⟨-2168766493186,-2168766454489⟩,⟨-659586648036,-659586647993⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-228804735796,-228804735794⟩,⟨-908385583104,-908385583104⟩,⟨-388479791924,-388479791923⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨870706891980,870706891982⟩,⟨-908385583104,-908385583104⟩,⟨-388479791924,-388479791923⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-256533637632,-256533637568⟩,⟨-1147091541744,-1147091541738⟩,⟨-490564680619,-490564680615⟩,⟨-1196730413667,-1196730413655⟩,⟨876648552098,876648552110⟩,⟨-218873270452,-218873270448⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-203149835499,-203149835447⟩,⟨-696444706758,-696444706697⟩,⟨-297841246934,-297841246905⟩,⟨947694769825,947694769849⟩,⟨1248268732128,1248268732212⟩,⟨173326466252,173326466262⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨203149835447,203149835499⟩,⟨696444706697,696444706758⟩,⟨297841246905,297841246934⟩,⟨-947694769849,-947694769825⟩,⟨-1248268732212,-1248268732128⟩,⟨-173326466262,-173326466252⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨562316624447,562316632534⟩,⟨1213999596037,1213999628001⟩,⟨519178550643,519178564318⟩,⟨-4554107743529,-4554107743337⟩,⟨-3417035225398,-3417035186617⟩,⟨-832913114298,-832913114245⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨1020709807046,1020709820899⟩,⟨3150111781756,3150111852714⟩,⟨519178550643,519178564318⟩,⟨-13338622299577,-13338622299135⟩,⟨-3417035225398,-3417035186617⟩,⟨-832913114298,-832913114245⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨135057427658,135057427664⟩,⟨-382252089344,-382252089344⟩,⟨776959583846,776959583848⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨8951198320037,8951198320436⟩,⟨25334513763128,25334513765388⟩,⟨-51494534159191,-51494534154466⟩,⟨143408192884610,143408192903792⟩,⟨-145744618535142,-145744618482409⟩,⟨592476437897664,592476437979958⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8309667382559,8309667495709⟩,⟨49164065734247,49164066634359⟩,⟨-43577262266437,-43577261501739⟩,⟨169706796390290,169706801506294⟩,⟨-298687091090434,-298687085235302⟩,⟨494602521490437,494602530317690⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨100236537856,100236671744⟩,⟨-585961763649,-585960163276⟩,⟨519374036368,519375454486⟩,⟨4786963788355,4786997901171⟩,⟨-2475930904238,-2475895862794⟩,⟨-545005032397,-544966501521⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1199748165632,1199748299520⟩,⟨-585961763649,-585960163276⟩,⟨519374036368,519375454486⟩,⟨4786963788355,4786997901171⟩,⟨-2475930904238,-2475895862794⟩,⟨-545005032397,-544966501521⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨95927514624,95927637376⟩,⟨-537005840910,-537004314315⟩,⟨475981330733,475982683490⟩,⟨4124746352437,4124779595971⟩,⟨-2036601364878,-2036567676295⟩,⟨-705525640406,-705489101744⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨104672708133,104672853758⟩,⟨-637084460363,-637082524160⟩,⟨564687060332,564688776084⟩,⟨5490787480299,5490830957755⟩,⟨-2945611896970,-2945568728092⟩,⟨-367717386785,-367671502866⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-100236671744,-100236537856⟩,⟨585960163276,585961763649⟩,⟨-519375454486,-519374036368⟩,⟨-4786997901171,-4786963788355⟩,⟨2475895862794,2475930904238⟩,⟨544966501521,545005032397⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨999274956032,999275089920⟩,⟨585960163276,585961763649⟩,⟨-519375454486,-519374036368⟩,⟨-4786997901171,-4786963788355⟩,⟨2475895862794,2475930904238⟩,⟨544966501521,545005032397⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-105103870592,-105103723200⟩,⟨644737389568,644739236859⟩,⟨-571473694945,-571472058006⟩,⟨-5645245445962,-5645205039135⟩,⟨3059353907205,3059394748659⟩,⟨302606918168,302651095999⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-95522118261,-95521971506⟩,⟨529947171556,529949160483⟩,⟨-469727895460,-469726132978⟩,⟨-3985810127718,-3985764968725⟩,⟨1934661078316,1934705658914⟩,⟨762812192374,762859156493⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨9150589872,9150882252⟩,⟨-107137288807,-107133363677⟩,⟨94959164872,94962643106⟩,⟨1504977352581,1505065989030⟩,⟨-1010950818654,-1010863069178⟩,⟨395094805589,395187653627⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4575294936,4575441126⟩,⟨-53568644404,-53566681838⟩,⟨47479582436,47481321553⟩,⟨752488676290,752532994515⟩,⟨-505475409327,-505431534589⟩,⟨197547402794,197593826814⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4575441126,-4575294936⟩,⟨53566681838,53568644404⟩,⟨-47481321553,-47479582436⟩,⟨-752532994515,-752488676290⟩,⟨505431534589,505475409327⟩,⟨-197593826814,-197547402794⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757547942490,757548107944⟩,⟨53566681838,53568644404⟩,⟨-47481321553,-47479582436⟩,⟨-752532994515,-752488676290⟩,⟨505431534589,505475409327⟩,⟨-197593826814,-197547402794⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨9138023889,9138048302⟩,⟨-106838082426,-106837647922⟩,⟨94697052658,94697437714⟩,⟨1497352040920,1497362838052⟩,⟨-1005015711810,-1005005696294⟩,⟨391300816994,391310654528⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9138048302,-9138023889⟩,⟨106837647922,106838082426⟩,⟨-94697437714,-94697052658⟩,⟨-1497362838052,-1497352040920⟩,⟨1005005696294,1005015711810⟩,⟨-391310654528,-391300816994⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090373579474,1090373603887⟩,⟨106837647922,106838082426⟩,⟨-94697437714,-94697052658⟩,⟨-1497362838052,-1497352040920⟩,⟨1005005696294,1005015711810⟩,⟨-391310654528,-391300816994⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9176233216,-9176208576⟩,⟨107733015322,107733455880⟩,⟨-95491064574,-95490674152⟩,⟨-1520467772227,-1520456764465⟩,⟨1022784708016,1022794906678⟩,⟨-402883362305,-402873365674⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4588116608,-4588104288⟩,⟨53866507661,53866727940⟩,⟨-47745532287,-47745337076⟩,⟨-760233886114,-760228382232⟩,⟨511392354008,511397453339⟩,⟨-201441681153,-201436682837⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4588104288,4588116608⟩,⟨-53866727940,-53866507661⟩,⟨47745337076,47745532287⟩,⟨760228382232,760233886114⟩,⟨-511397453339,-511392354008⟩,⟨201436682837,201441681153⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766711487904,766711519488⟩,⟨-53866727940,-53866507661⟩,⟨47745337076,47745532287⟩,⟨760228382232,760233886114⟩,⟨-511397453339,-511392354008⟩,⟨201436682837,201441681153⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272593394868,272593400972⟩,⟨26709411980,26709520607⟩,⟨-23674359429,-23674263164⟩,⟨-374340709513,-374338010230⟩,⟨251251424073,251253927953⟩,⟨-97827663632,-97825204248⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533422975808,1533423038976⟩,⟨-107733455880,-107733015322⟩,⟨95490674152,95491064574⟩,⟨1520456764464,1520467772228⟩,⟨-1022794906678,-1022784708016⟩,⟨402873365674,402883362306⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1209802817872,1209802979968⟩,⟨-709412643169,-709410515525⟩,⟨628795993280,628797878669⟩,⟨6627459195185,6627506926955⟩,⟨-3734999653042,-3734952101768⟩,⟨-6192663597,-6142006044⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1320094007968,1320094332160⟩,⟨-1418825286337,-1418821031050⟩,⟨1257591986560,1257595757339⟩,⟨13254918390375,13255013853907⟩,⟨-7469999306084,-7469904203537⟩,⟨-12385247600,-12284091682⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨201031237888,201031507968⟩,⟨-1181745308058,-1181741473595⟩,⟨1047453184620,1047456582555⟩,⟨9769942983909,9770033449607⟩,⟨-5096002870638,-5095914826410⟩,⟨-1008181743069,-1008091013265⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨69061555236,69061662568⟩,⟨-398836061003,-398834684751⟩,⟨353512735264,353513954813⟩,⟨3172449224795,3172479828033⟩,⟨-1609197876970,-1609167307875⟩,⟨-438371848389,-438339197371⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380169671865,380169696040⟩,⟨10540495043,10540757897⟩,⟨-9342949067,-9342716126⟩,⟨-150349674313,-150343108075⟩,⟨101471017643,101477096083⟩,⟨-40665285617,-40659335881⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179963664140,3179963866355⟩,⟨-88169130042,-88166920162⟩,⟨78147990527,78149948923⟩,⟨1262447459124,1262502787734⟩,⟨-853148060439,-853096891886⟩,⟨343939669715,343989672349⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨199737074799,199737397922⟩,⟨-1159035827457,-1159031626351⟩,⟨1027323992015,1027327714801⟩,⟨9318489808469,9318584323828⟩,⟨-4764341576175,-4764247955750⟩,⟨-1195986451090,-1195887331509⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨400768312687,400768905890⟩,⟨-2340781135515,-2340773099946⟩,⟨2074777176635,2074784297356⟩,⟨19088432792378,19088617773435⟩,⟨-9860344446813,-9860162782160⟩,⟨-2204168194159,-2203978344774⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨521939805522,521940033514⟩,⟨73813370566,73816091052⟩,⟨-65427930724,-65425519978⟩,⟨-1031749992322,-1031688314118⟩,⟨691843723082,691904672318⟩,⟨-268178189611,-268113858753⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359609135354,359609370980⟩,⟨76284550688,76287378915⟩,⟨-67618391486,-67615885261⟩,⟨-1060897808439,-1060833435207⟩,⟨710224280466,710287778432⟩,⟨-272918674440,-272851817327⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨719218270708,719218741960⟩,⟨152569101376,152574757830⟩,⟨-135236782972,-135231770522⟩,⟨-2121795616878,-2121666870414⟩,⟨1420448560932,1420575556864⟩,⟨-545837348880,-545703634654⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524284927506,1524285015087⟩,⟨-895807958,-894932896⟩,⟨793236438,794011916⟩,⟨23093926412,23115731308⟩,⟨-17789210384,-17768996206⟩,⟨11562711146,11582545312⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨997073193163,997073903763⟩,⟨210925008793,210933435439⟩,⟨-186963817791,-186956350512⟩,⟨-2926649399735,-2926456220652⟩,⟨1957792887826,1957982512766⟩,⟨-749342086868,-749143494482⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67581967346,67581970374⟩,⟨13243714940,13243769102⟩,⟨-11738801100,-11738753104⟩,⟨-184317131136,-184315777996⟩,⟨123431432914,123432686598⟩,⟨-47487819398,-47486590546⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨62738378664,62738382328⟩,⟨205917550639,205917614124⟩,⟨21014055425,21014102402⟩,⟨-915084745483,-915083138177⟩,⟨-122822696588,-122821355396⟩,⟨-106365642616,-106364453319⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2138573129501,2138573305695⟩,⟨-300498801726,-300497560506⟩,⟨266350241362,266351341332⟩,⟨4262091786479,4262122837592⟩,⟨-2871574645616,-2871545928132⟩,⟨1140313077694,1140341143025⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2982539783463,2982540152054⟩,⟨-628631531643,-628628909163⟩,⟨557194079716,557196403763⟩,⟨8960291295825,8960356983846⟩,⟨-6046366711701,-6046306066654⟩,⟨2420187552695,2420246647683⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨170184385129,170184416100⟩,⟨522702941014,522703333990⟩,⟨88796431990,88796700935⟩,⟨-2206448205468,-2206438705808⟩,⟨-585839168587,-585831464315⟩,⟨-129133097504,-129126319266⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨7103622336984,7103623629738⟩,⟨-21818028439332,-21818004095111⟩,⟨-3706440767328,-3706428192331⟩,⟨226121627189934,226122331926318⟩,⟨47220817824302,47221246812672⟩,⟨9257603250328,9257913681776⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨6441797637817,6441803401109⟩,⟨-18422592970207,-18422502103266⟩,⟨-4569043047844,-4568980785274⟩,⟨177775012750439,177777393249312⟩,⟨58468899658479,58470729744841⟩,⟨4814268736802,4815894778343⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨12883595275634,12883606802218⟩,⟨-36845185940414,-36845004206532⟩,⟨-9138086095688,-9137961570548⟩,⟨355550025500878,355554786498624⟩,⟨116937799316958,116941459489682⟩,⟨9628537473604,9631789556686⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨7496004706000,7496004706047⟩,⟨-51104586012188,-51104586011546⟩,⟨0,0⟩,⟨696818855868932,696818855882058⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨6396493078224,6396493078271⟩,⟨-51104586012188,-51104586011546⟩,⟨0,0⟩,⟨696818855868934,696818855882054⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨1936112185792,1936112224384⟩,⟨-8784514556044,-8784514555793⟩,⟨0,0⟩,⟨49594590484645,49594590494936⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨5283657330818,5283657330866⟩,⟨-20976830434763,-20976830434379⟩,⟨-8970942377439,-8970942377251⟩,⟨166561677838641,166561677843194⟩,⟨96622091497393,96622091499987⟩,⟨30462916914223,30462916915214⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨4184145703042,4184145703090⟩,⟨-20976830434763,-20976830434379⟩,⟨-8970942377440,-8970942377250⟩,⟨166561677838645,166561677843190⟩,⟨96622091497395,96622091499986⟩,⟨30462916914223,30462916915214⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1469427407936,1469427433088⟩,⟨-5512300625719,-5512300625522⟩,⟨-2357388139941,-2357388139849⟩,⟨16133736915699,16133736920142⟩,⟨13571846166199,13571846168420⟩,⟨2950742893273,2950742894165⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨137620105461,137620105463⟩,⟨776959583846,776959583848⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨181191226487,181191226490⟩,⟨530321507940,530321507946⟩,⟨226797070416,226797070420⟩,⟨-1500965240832,-1500965240832⟩,⟨-1283804312376,-1283804312368⟩,⟨-274515602966,-274515602964⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨3405539593728,3405539657472⟩,⟨-14296815181763,-14296815181315⟩,⟨-2357388139941,-2357388139849⟩,⟨65728327400344,65728327415078⟩,⟨13571846166199,13571846168420⟩,⟨2950742893273,2950742894165⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨801536625374,801537811780⟩,⟨-4681562271030,-4681546199892⟩,⟨4149554353270,4149568594712⟩,⟨38176865584756,38177235546870⟩,⟨-19720688893626,-19720325564320⟩,⟨-4408336388318,-4407956689548⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4207076219102,4207077469252⟩,⟨-18978377452793,-18978361381207⟩,⟨1792166213329,1792180454863⟩,⟨103905192985100,103905562961948⟩,⟨-6148842727427,-6148479395900⟩,⟨-1457593495045,-1457213795383⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨526577671694,526577828177⟩,⟨597466971004,597469866051⟩,⟨224316048190,224317830732⟩,⟨-22230671740458,-22230600218165⟩,⟨496799048657,496854588621⟩,⟨-182439335286,-182391810267⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨322552043928,322552043930⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-322552043930,-322552043928⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨776959583846,776959583848⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1368135525037,1368135552312⟩,⟨-10079719304986,-10079719227607⟩,⟨0,0⟩,⟨70183610639842,70183610648209⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨268623897261,268623924536⟩,⟨-10079719304986,-10079719227607⟩,⟨0,0⟩,⟨70183610639842,70183610648209⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨16498075897,16498077574⟩,⟨-665760588759,-665760579236⟩,⟨94910279325,94910288963⟩,⟨7814744724907,7814744752516⟩,⟨-3829993499294,-3829993444669⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨543075747591,543075905751⟩,⟨-68293617755,-68290713185⟩,⟨319226327515,319228119695⟩,⟨-14415927015551,-14415855465649⟩,⟨-3333194450637,-3333138856048⟩,⟨-182439335286,-182391810267⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨624408959557,624408972004⟩,⟨2833063871453,2833063984491⟩,⟨0,0⟩,⟨9713731213653,9713733393734⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨308410892570,308410988537⟩,⟨1360535982080,1360538095706⟩,⟨181287558941,181288580328⟩,⟨-3740845118207,-3740786865785⟩,⟨-1070373350661,-1070337090294⟩,⟨-103606687662,-103579696297⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-801537811780,-801536625374⟩,⟨4681546199892,4681562271030⟩,⟨-4149568594712,-4149554353270⟩,⟨-38177235546870,-38176865584756⟩,⟨19720325564320,19720688893626⟩,⟨4407956689548,4408336388318⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨2604001781948,2604003032098⟩,⟨-9615268981871,-9615252910285⟩,⟨-6506956734653,-6506942493119⟩,⟨27551091853474,27551461830322⟩,⟨33292171730519,33292535062046⟩,⟨7358699582821,7359079282483⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨429119860787,429120066810⟩,⟨-328549711572,-328546460076⟩,⟨-535168051981,-535165447184⟩,⟨-8289925795688,-8289847616063⟩,⟨-2675983376166,-2675911857854⟩,⟨-2121873975976,-2121805216910⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨457609471588,457609471592⟩,⟨1816771166208,1816771166208⟩,⟨776959583846,776959583848⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-457609471592,-457609471588⟩,⟨-1816771166208,-1816771166208⟩,⟨-776959583848,-776959583846⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨641902156184,641902156188⟩,⟨-1816771166208,-1816771166208⟩,⟨-776959583848,-776959583846⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨857861433823,857861448514⟩,⟨-5646116777349,-5646116735651⟩,⟨-2414615898404,-2414615880564⟩,⟨27635413230499,27635413233805⟩,⟨18652619437447,18652619489401⟩,⟨5054315662834,5054315663506⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-857861448514,-857861433823⟩,⟨5646116735651,5646116777349⟩,⟨2414615880564,2414615898404⟩,⟨-27635413233805,-27635413230499⟩,⟨-18652619489401,-18652619437447⟩,⟨-5054315663506,-5054315662834⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨241650179262,241650193953⟩,⟨5646116735651,5646116777349⟩,⟨2414615880564,2414615898404⟩,⟨-27635413233805,-27635413230499⟩,⟨-18652619489401,-18652619437447⟩,⟨-5054315663506,-5054315662834⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨14841430858,14841431762⟩,⟨304761993467,304761998599⟩,⟨233678398365,233678404660⟩,⟨-3660192166279,-3660192151501⟩,⟨187921311181,187921346956⟩,⟨1395844732226,1395844744894⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨443961291645,443961498572⟩,⟨-23787718105,-23784461477⟩,⟨-301489653616,-301487042524⟩,⟨-11950117961967,-11950039767564⟩,⟨-2488062064985,-2487990510898⟩,⟨-726029243750,-725960472016⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-137620105463,-137620105461⟩,⟨-776959583848,-776959583846⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨8452215041,8452215043⟩,⟨23796287650,23796287654⟩,⟨48623978667,48623978669⟩,⟨-405172282987,-405172282979⟩,⟨136895497501,136895497505⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨14883368328,14883368629⟩,⟨-25626217013,-25626216151⟩,⟨85621175111,85621176822⟩,⟨-712454982005,-712454967521⟩,⟨-147422731515,-147422726674⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1184397166424,1184397182500⟩,⟨-3655283389230,-3655283207662⟩,⟨-602437269192,-602437236968⟩,⟨38039535876206,38039538232066⟩,⟨7683492318681,7683492804445⟩,⟨1579337126444,1579337209986⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨16032408233,16032408776⟩,⟨-77083813589,-77083808826⟩,⟨84076583547,84076587245⟩,⟨-82155652061,-82155569541⟩,⟨-325401106396,-325401069291⟩,⟨-72447546457,-72447537998⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-16032408776,-16032408233⟩,⟨77083808826,77083813589⟩,⟨-84076587245,-84076583547⟩,⟨82155569541,82155652061⟩,⟨325401069291,325401106396⟩,⟨72447537998,72447546457⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-153652514239,-153652513694⟩,⟨-699875775022,-699875770257⟩,⟨-84076587245,-84076583547⟩,⟨2281178825093,2281178907613⟩,⟨325401069291,325401106396⟩,⟨72447537998,72447546457⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨90247834053,90247835602⟩,⟨-593976824102,-593976819701⟩,⟨374394826019,374394834921⟩,⟨2907271604608,2907271604996⟩,⟨-2173712675486,-2173712650068⟩,⟨-1484600430335,-1484600430201⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨97215232861,97215235850⟩,⟨-939858993050,-939858959570⟩,⟨353851202298,353851220857⟩,⟨10203309067326,10203309582647⟩,⟨-2630082322599,-2630082101496⟩,⟨-1879856077564,-1879856014927⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-97215235850,-97215232861⟩,⟨939858959570,939858993050⟩,⟨-353851220857,-353851202298⟩,⟨-10203309582647,-10203309067326⟩,⟨2630082101496,2630082322599⟩,⟨1879856014927,1879856077564⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨1002296391926,1002296394915⟩,⟨939858959570,939858993050⟩,⟨-353851220857,-353851202298⟩,⟨-10203309582647,-10203309067326⟩,⟨2630082101496,2630082322599⟩,⟨1879856014927,1879856077564⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨165170888573,165170889069⟩,⟨638313878496,638313885465⟩,⟨148432399031,148432402714⟩,⟨-2143049083259,-2143048961919⟩,⟨-713682572259,-713682516452⟩,⟨-86436032460,-86436013723⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨21472346783,21472346937⟩,⟨195609884710,195609886738⟩,⟨23498757226,23498758346⟩,⟨253416545471,253416582932⟩,⟨16087989088,16088005224⟩,⟨-7390327962,-7390324392⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨251603547049,251603773957⟩,⟨1572521769999,1572527398654⟩,⟨96890582965,96893275566⟩,⟨-3197015433247,-3196854511306⟩,⟨59011665484,59109611250⟩,⟨-289159413817,-289090441955⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-251603773957,-251603547049⟩,⟨-1572527398654,-1572521769999⟩,⟨-96893275566,-96890582965⟩,⟨3196854511306,3197015433247⟩,⟨-59109611250,-59011665484⟩,⟨289090441955,289159413817⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56807118613,56807441488⟩,⟨-211991416574,-211983674293⟩,⟨84394283375,84397997363⟩,⟨-543990606901,-543771432538⟩,⟨-1129482961911,-1129348755778⟩,⟨185483754293,185579717520⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨17218106232368,17218121931636⟩,⟨-113832030215651,-113831728707231⟩,⟨-39835337038437,-39835145695017⟩,⟨1033656161361076,1033664523678924⟩,⟨440118081040984,440124131552320⟩,⟨86627604577229,86632515917387⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨24812309158,24812309308⟩,⟨191777636244,191777638916⟩,⟨44595637956,44595639198⟩,⟨97270976911,97271031487⟩,⟨-42078908618,-42078885044⟩,⟨14107100929,14107108627⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨388555213205,388555569835⟩,⟨434385739002,434395338693⟩,⟨-200592941984,-200587962361⟩,⟨-14859922633153,-14859625807087⟩,⟨-2292029346654,-2291845948087⟩,⟨-1055592444555,-1055465666616⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-388555569835,-388555213205⟩,⟨-434395338693,-434385739002⟩,⟨200587962361,200592941984⟩,⟨14859625807087,14859922633153⟩,⟨2291845948087,2292029346654⟩,⟨1055465666616,1055592444555⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨55405721810,55406285367⟩,⟨-458183056798,-458170200479⟩,⟨-100901691255,-100894100540⟩,⟨2909507845120,2909882865589⟩,⟨-196216116898,-195961164244⟩,⟨329436422866,329631972539⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨318811331948,318811331953⟩,⟨1307281091786,1307281091794⟩,⟨226797070416,226797070420⟩,⟨-3699988496384,-3699988496384⟩,⟨-1283804312376,-1283804312368⟩,⟨-274515602966,-274515602964⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1800434417990,-1800432800807⟩,⟨-3051897494863,-3051864687099⟩,⟨291821446822,291839778000⟩,⟨23948586419425,23949508486820⟩,⟨-3895159919139,-3894551195450⟩,⟨900411810240,900886245359⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-270464946453,-270464702703⟩,⟨-1503692066260,-1503686186175⟩,⟨-199217901278,-199214923049⟩,⟨3563298239681,3563478247399⟩,⟨340918256024,341025925697⟩,⟨355590207560,355666587717⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨48346385495,48346629250⟩,⟨-196410974474,-196405094381⟩,⟨27579169138,27582147371⟩,⟨-136690256703,-136510248985⟩,⟨-942886056352,-942778386671⟩,⟨81074604594,81150984753⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2862579468,2862624856⟩,⟨-34355129276,-34353831696⟩,⟨-960463455,-959811232⟩,⟨299577971924,299620935427⟩,⟨-82772040659,-82746760524⟩,⟨10877005382,10893983161⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2125828350,2125849788⟩,⟨-17272775156,-17272170964⟩,⟨2425355236,2425629378⟩,⟨58146630062,58166722326⟩,⟨-92773550998,-92762305276⟩,⟨8513370007,8520421812⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨2841034476,2841063176⟩,⟨-33741719360,-33740804021⟩,⟨-1316556901,-1316144506⟩,⟨282087607807,282120833882⟩,⟨-72874329743,-72856364006⟩,⟨6681377509,6692035070⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-2841063176,-2841034476⟩,⟨33740804021,33741719360⟩,⟨1316144506,1316556901⟩,⟨-282120833882,-282087607807⟩,⟨72856364006,72874329743⟩,⟨-6692035070,-6681377509⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨21516292,21590380⟩,⟨-614325255,-612112336⟩,⟨355681051,356745669⟩,⟨17457138042,17533327620⟩,⟨-9915676653,-9872430781⟩,⟨4184970312,4212605652⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56807118613,56807441488⟩,⟨-211991416574,-211983674293⟩,⟨84394283375,84397997363⟩,⟨-543990606901,-543771432538⟩,⟨-1129482961911,-1129348755778⟩,⟨185483754293,185579717520⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨21516292,21590380⟩,⟨-614325255,-612112336⟩,⟨355681051,356745669⟩,⟨17457138042,17533327620⟩,⟨-9915676653,-9872430781⟩,⟨4184970312,4212605652⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨161061273600,161490770330⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨187260574105,194991515239⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-161490770330,-161061273600⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨388265043558,388694540288⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨66126390230,68932547380⟩,⟨-194991515239,-187260574105⟩,⟨388265043558,388694540288⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨227187663830,230423317710⟩,⟨904520112537,912251053671⟩,⟨388265043558,388694540288⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨65696893500,69362044110⟩,⟨-194991515239,-187260574105⟩,⟨388265043558,388694540288⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2111982115968,-2109053948480⟩,⟨7486036614626,7505999378951⟩,⟨0,0⟩,⟨-51240955760307,-50968759929238⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-310197373284,-308943449484⟩,⟨-1015394721248,-1006610289693⟩,⟨0,0⟩,⟨7446057851938,7545871815143⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨308943449484,310197373284⟩,⟨1006610289693,1015394721248⟩,⟨0,0⟩,⟨-7545871815143,-7446057851938⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨938020857446,938450354176⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-174656543168,-174153218944⟩,⟨-1288804838420,-1288214996387⟩,⟨0,0⟩,⟨-1510686990091,-1509304526658⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149072088603,-148574464911⟩,⟨-925861848224,-924351875624⟩,⟨0,0⟩,⟨1287035042247,1289984252536⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨148574464911,149072088603⟩,⟨924351875624,925861848224⟩,⟨0,0⟩,⟨-1289984252536,-1287035042247⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨457517914395,459269461887⟩,⟨1930962165317,1941256569472⟩,⟨0,0⟩,⟨-8835856067679,-8733092894185⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-1733759445184,-1718210398848⟩,⟨4316101300751,4414987257904⟩,⟨1852685458631,1881150408852⟩,⟨-17727973033698,-16942731634432⟩,⟨-12874850741860,-12519206423291⟩,⟨-3218453330848,-3121789094279⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-363341863222,-355026901600⟩,⟨-546659893472,-488253000834⟩,⟨-230098111713,-212512638455⟩,⟨3386105623444,3825311011506⟩,⟨2068290094585,2268500151887⟩,⟨633971745810,684989404785⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨355026901600,363341863222⟩,⟨488253000834,546659893472⟩,⟨212512638455,230098111713⟩,⟨-3825311011506,-3386105623444⟩,⟨-2268500151887,-2068290094585⟩,⟨-684989404785,-633971745810⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-230423317710,-227187663830⟩,⟨-912251053671,-904520112537⟩,⟨-388694540288,-388265043558⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨869088310066,872323963946⟩,⟨-912251053671,-904520112537⟩,⟨-388694540288,-388265043558⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-258579453312,-254493524544⟩,⟨-1154118205648,-1140092926935⟩,⟨-491749988753,-489384618209⟩,⟨-1211436786077,-1182172020024⟩,⟨869695491796,883580533566⟩,⟨-219932236577,-217821529568⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-205150221253,-201159625402⟩,⟨-706286715789,-686624895430⟩,⟨-300273641249,-295413000529⟩,⟨914686666734,980689233291⟩,⟨1234045639183,1262513955992⟩,⟨171139363192,175509673320⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨201159625402,205150221253⟩,⟨686624895430,706286715789⟩,⟨295413000529,300273641249⟩,⟨-980689233291,-914686666734⟩,⟨-1262513955992,-1234045639183⟩,⟨-175509673320,-171139363192⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨556186527002,568492084475⟩,⟨1174877896264,1252946609261⟩,⟨507925638984,530371752962⟩,⟨-4806000244797,-4300792290178⟩,⟨-3531014107879,-3302335733768⟩,⟨-860499078105,-805111109002⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨1013704441397,1027761546362⟩,⟨3105840061581,3194203178733⟩,⟨507925638984,530371752962⟩,⟨-13641856312476,-13033885184363⟩,⟨-3531014107879,-3302335733768⟩,⟨-860499078105,-805111109002⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨131393787000,138724088220⟩,⟨-389983030478,-374521148210⟩,⟨776530087116,777389080576⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨8714606346501,9200783744932⟩,⟨23527308176742,27308365254907⟩,⟨-54436278756861,-48781391265645⟩,⟨127035968817034,162105062692333⟩,⟨-184996953590505,-109410182755234⟩,⟨546123149846565,644142613726107⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8034508171908,8600374466763⟩,⟨46307750658115,52255618709659⟩,⟨-46858205711310,-40536249052897⟩,⟨135883300162682,206889222286025⟩,⟨-349747337082274,-251667877672421⟩,⟨443785454481999,550657335881984⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨96886849536,103626365184⟩,⟨-665906453726,-515432777270⟩,⟨451192535428,597125866341⟩,⟨2804500648593,7006643070361⟩,⟨-4837964972871,-305899698811⟩,⟨-2847953911669,1910541721395⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1196398477312,1203137992960⟩,⟨-665906453726,-515432777270⟩,⟨451192535428,597125866341⟩,⟨2804500648593,7006643070361⟩,⟨-4837964972871,-305899698811⟩,⟨-2847953911669,1910541721395⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨92853392512,99029748224⟩,⟨-611979957153,-471038513671⟩,⟨412331288656,548769365507⟩,⟨2222325326471,6237434256629⟩,⟨-4269530832738,25888393872⟩,⟨-2891212994372,1601192415148⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨101035454840,108363067304⟩,⟨-729633835213,-556073648560⟩,⟨486768188680,654270931788⟩,⟨3096621562517,8197642307944⟩,⟨-5772376729838,-384092924916⟩,⟨-3081803478350,2520232246703⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-103626365184,-96886849536⟩,⟨515432777270,665906453726⟩,⟨-597125866341,-451192535428⟩,⟨-7006643070361,-2804500648593⟩,⟨305899698811,4837964972871⟩,⟨-1910541721395,2847953911669⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨995885262592,1002624778240⟩,⟨515432777270,665906453726⟩,⟨-597125866341,-451192535428⟩,⟨-7006643070361,-2804500648593⟩,⟨305899698811,4837964972871⟩,⟨-1910541721395,2847953911669⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-108839922368,-101424193856⟩,⟨565240700454,735197031612⟩,⟨-659259513069,-494792717909⟩,⟨-8227311200817,-3366089419031⟩,⟨589824502021,5782196125578⟩,⟨-2504629639182,2921634053616⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-99249157782,-91865203950⟩,⟨446050468481,622866907053⟩,⟨-559546682702,-389050585787⟩,⟨-6713684963559,-1464733450956⟩,⟨-743217726136,4780561274190⟩,⟨-2159760022009,3569373551285⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1786297058,16497863354⟩,⟨-283583366732,66793258493⟩,⟨-72778494022,265220346001⟩,⟨-3617063401042,6732908856988⟩,⟨-6515594455974,4396468349274⟩,⟨-5241563500359,6089605797988⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨893148529,8248931677⟩,⟨-141791683366,33396629247⟩,⟨-36389247011,132610173001⟩,⟨-1808531700521,3366454428494⟩,⟨-3257797227987,2198234174637⟩,⟨-2620781750180,3044802898994⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-8248931677,-893148529⟩,⟨-33396629247,141791683366⟩,⟨-132610173001,36389247011⟩,⟨-3366454428494,1808531700521⟩,⟨-2198234174637,3257797227987⟩,⟨-3044802898994,2620781750180⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨753874451939,761230254351⟩,⟨-33396629247,141791683366⟩,⟨-132610173001,36389247011⟩,⟨-3366454428494,1808531700521⟩,⟨-2198234174637,3257797227987⟩,⟨-3044802898994,2620781750180⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8537482802,9766539335⟩,⟨-125520210264,-90837889614⟩,⟨79516436546,112555395548⟩,⟨977507043439,2127316035762⟩,⟨-1635218164866,-476933709632⟩,⟨-166525584159,1008705647791⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9766539335,-8537482802⟩,⟨90837889614,125520210264⟩,⟨-112555395548,-79516436546⟩,⟨-2127316035762,-977507043439⟩,⟨476933709632,1635218164866⟩,⟨-1008705647791,166525584159⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1089745088441,1090974144974⟩,⟨90837889614,125520210264⟩,⟨-112555395548,-79516436546⟩,⟨-2127316035762,-977507043439⟩,⟨476933709632,1635218164866⟩,⟨-1008705647791,166525584159⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9810174144,-8570801280⟩,⟨91548746900,126645150477⟩,⟨-113564142190,-80138697130⟩,⟨-2160968898297,-992779215206⟩,⟨487338579003,1662954025166⟩,⟨-1029475477884,162177057032⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4905087072,-4285400640⟩,⟨45774373450,63322575239⟩,⟨-56782071095,-40069348565⟩,⟨-1080484449149,-496389607603⟩,⟨243669289501,831477012583⟩,⟨-514737738942,81088528516⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4285400640,4905087072⟩,⟨-63322575239,-45774373450⟩,⟨40069348565,56782071095⟩,⟨496389607603,1080484449149⟩,⟨-831477012583,-243669289501⟩,⟨-81088528516,514737738942⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766408784256,767028489952⟩,⟨-63322575239,-45774373450⟩,⟨40069348565,56782071095⟩,⟨496389607603,1080484449149⟩,⟨-831477012583,-243669289501⟩,⟨-81088528516,514737738942⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272436272110,272743536244⟩,⟨22709472403,31380052566⟩,⟨-28138848887,-19879109136⟩,⟨-531829008941,-244376760859⟩,⟨119233427408,408804541217⟩,⟨-252176411948,41631396040⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532817568512,1534056979904⟩,⟨-126645150478,-91548746900⟩,⟨80138697130,113564142190⟩,⟨992779215206,2160968898298⟩,⟨-1662954025166,-487338579002⟩,⟨-162177057032,1029475477884⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1205760964472,1213920784879⟩,⟨-811697607473,-619861723078⟩,⟨542606125927,727858446720⟩,⟨4010026076616,9626148077516⟩,⟨-6870548012147,-925765950447⟩,⟨-2983116818007,3201666534181⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1312010301168,1328329941982⟩,⟨-1623395214947,-1239723446156⟩,⟨1085212251854,1455716893440⟩,⟨8020052153235,19252296155027⟩,⟨-13741096024292,-1851531900894⟩,⟨-5963240220394,6403333068362⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨194277586368,207869670592⟩,⟨-1360463339139,-1026168500154⟩,⟨898273427261,1219942899582⟩,⟨4955168955562,15176396043758⟩,⟨-10677176734691,-23109668736⟩,⟨-6350974105988,4632355610797⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨66429966495,71744147433⟩,⟨-464177819997,-340040283586⟩,⟨296859630133,416840667198⟩,⟨1433862016129,5061845799847⟩,⟨-3596846135939,254619562163⟩,⟨-2402739907269,1609261897586⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379800534747,380536335342⟩,⟨243591858,21098084605⟩,⟨-19403077790,457328500⟩,⟨-503255430725,191582566161⟩,⟨-242977925236,456100725984⟩,⟨-397882883974,310557465293⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176899831465,3183054548410⟩,⟨-176820062167,-2033621656⟩,⟨-3832805457,162614449856⟩,⟨-1605623778781,4237357427938⟩,⟨-3840582262980,2036789443462⟩,⟨-2603129796928,3351215305837⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨191940989099,207697243976⟩,⟨-1355319114575,-982626273101⟩,⟨857488273666,1217352488996⟩,⟨4039452428374,15079684812524⟩,⟨-10799053203808,871087723398⟩,⟨-7128625708707,5000735763338⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨386218575467,415566914568⟩,⟨-2715782453714,-2008794773255⟩,⟨1755761700927,2437295388578⟩,⟨8994621383936,30256080856282⟩,⟨-21476229938499,847978054662⟩,⟨-13479599814695,9633091374135⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨516890112782,527026259206⟩,⟨-46243302816,196334657074⟩,⟨-183621297262,50387090156⟩,⟨-4670041244287,2540789733507⟩,⟨-3078030894438,4520358752554⟩,⟨-4224824205434,3660905015335⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨354403028255,364878663591⟩,⟨-48023777479,203893997799⟩,⟨-190691144079,52327110265⟩,⟨-4858793909041,2676594663109⟩,⟨-3232061608538,4704149860072⟩,⟨-4396605407103,3835077734007⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨708806056510,729757327182⟩,⟨-96047554958,407787995598⟩,⟨-381382288158,104654220530⟩,⟨-9717587818082,5353189326218⟩,⟨-6464123217076,9408299720144⟩,⟨-8793210814206,7670155468014⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523051029177,1525519497102⟩,⟨-35807260864,33971463364⟩,⟨-32416698418,34047705644⟩,⟨-1134536820556,1183461854859⟩,⟨-1186020315534,1147879585864⟩,⟨-1170882704823,1196001062043⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨981842998821,1012503190186⟩,⟨-157027014867,588333443625⟩,⟨-550664880965,167800514229⟩,⟨-14262250061907,8237967412018⟩,⟨-9779640340340,13840470907680⟩,⟨-13000904033184,11458258595520⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67504081345,67656434624⟩,⟨11253876442,15568196440⟩,⟨-13960178242,-9851265322⟩,⟨-262911643294,-119311855121⟩,⟨57480996322,201993956806⟩,⟨-124390330479,22094334768⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨62235983088,63241424751⟩,⟨201057432326,211101716728⟩,⟨18134705236,23552993681⟩,⟨-1021602980674,-819756167458⟩,⟨-199636449193,-34250698675⟩,⟨-182690261173,-37878634059⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136884812297,2140341910120⟩,⟨-353394856688,-255254285772⟩,⟨223441025588,316893174374⟩,⟨2783291339765,6059214530850⟩,⟨-4666523777710,-1372132343034⟩,⟨-440862341827,2896141917300⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2979008588386,2986240766951⟩,⟨-739593606201,-533770963106⟩,⟨467245167165,663201971337⟩,⟨5852115565014,12741933581208⟩,⟨-9820968930634,-2897219439034⟩,⟨-898225843532,6110214268857⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨168621707531,171761822232⟩,⟨502203751479,543132766175⟩,⟨75581651768,102115106966⟩,⟨-2727392041467,-1683365433622⟩,⟨-1037488892250,-138262412212⟩,⟨-532432278283,277230959364⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨7038384921078,7169455447440⟩,⟨-23092911500859,-20579097646880⟩,⟨-4341728717039,-3097153670129⟩,⟨189320150093523,264728368533395⟩,⟨23776811449057,72081470555032⟩,⟨-9061574289003,27896536878446⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨6285144043220,6602109817713⟩,⟨-22289391156334,-14540466995034⟩,⟨-7588806972739,-1671542428508⟩,⟨51347736382666,304091809017209⟩,⟨-48384196351237,168810931879330⟩,⟨-94443170147138,104752400279446⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨12570288086440,13204219635426⟩,⟨-44578782312668,-29080933990068⟩,⟨-15177613945478,-3343084857016⟩,⟨102695472765332,608183618034418⟩,⟨-96768392702474,337621863758660⟩,⟨-188886340294276,209504800558892⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨7486036614626,7505999378951⟩,⟨-51240955760307,-50968759929238⟩,⟨0,0⟩,⟨694042688396362,699609849314076⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨6386524986850,6406487751175⟩,⟨-51240955760307,-50968759929238⟩,⟨0,0⟩,⟨694042688396369,699609849314074⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨1934397405376,1937828896704⟩,⟨-8821703006412,-8747498843670⟩,⟨0,0⟩,⟨48335777434174,50852266719516⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨5246542891705,5321265244927⟩,⟨-21367048477512,-20595153363806⟩,⟨-9104133178972,-8840464691773⟩,⟨161691365470135,171594814250446⟩,⟨94440924499680,98866737758448⟩,⟨29792500539756,31152456089071⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨4147031263929,4221753617151⟩,⟨-21367048477513,-20595153363806⟩,⟨-9104133178973,-8840464691772⟩,⟨161691365470138,171594814250445⟩,⟨94440924499681,98866737758448⟩,⟨29792500539756,31152456089072⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1459630946496,1479265909312⟩,⟨-5665093112909,-5363792549929⟩,⟨-2413799090010,-2302406678601⟩,⟨12922158953564,19328906362745⟩,⟨12159360966950,14980833517723⟩,⟨2460041923453,3438219006471⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨137405399039,137834895770⟩,⟨776530087116,777389080576⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨179576220785,182811874666⟩,⟨523781583664,536858937265⟩,⟨225438566316,228154507528⟩,⟨-1513766592187,-1488218247657⟩,⟨-1290126302908,-1277482321834⟩,⟨-274819186688,-274212187012⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨3394028351872,3417094806016⟩,⟨-14486796119321,-14111291393599⟩,⟨-2413799090010,-2302406678601⟩,⟨61257936387738,70181173082261⟩,⟨12159360966950,14980833517723⟩,⟨2460041923453,3438219006471⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨772437150934,831133829136⟩,⟨-5431564907428,-4017589546510⟩,⟨3511523401854,4874590777156⟩,⟨17989242767872,60512161712564⟩,⟨-42952459876998,1695956109324⟩,⟨-26959199629390,19266182748270⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4166465502806,4248228635152⟩,⟨-19918361026749,-18128880940109⟩,⟨1097724311844,2572184098555⟩,⟨79247179155610,130693334794825⟩,⟨-30793098910048,16676789627047⟩,⟨-24499157705937,22704401754741⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨520681037410,532558398057⟩,⟨445598383364,738073534242⟩,⟨137182039092,322449274905⟩,⟨-26758785697294,-17556244844239⟩,⟨-3084958391989,3909218677537⟩,⟨-3071217041771,2846226242932⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨322122547200,322981540660⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-322981540660,-322122547200⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨776530087116,777389080576⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1366168167545,1370105587123⟩,⟨-10112877497161,-10046715869087⟩,⟨0,0⟩,⟨69127138187530,71240953729681⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨266656539769,270593959347⟩,⟨-10112877497161,-10046715869087⟩,⟨0,0⟩,⟨69127138187530,71240953729681⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨15932988657,17070260714⟩,⟨-685953074195,-645716026339⟩,⟨94163090605,95659192660⟩,⟨7552576606481,8081104886727⟩,⟨-3845654168305,-3814403081036⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨536614026067,549628658771⟩,⟨-240354690831,92357507903⟩,⟨231345129697,418108467565⟩,⟨-19206209090813,-9475139957512⟩,⟨-6930612560294,94815596501⟩,⟨-3071217041771,2846226242932⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨623855811868,624962490260⟩,⟨2816129949455,2850103843148⟩,⟨0,0⟩,⟨8995144412160,10434454156663⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨304471340215,312408970153⟩,⟨1237787877450,1477218330184⟩,⟨131263735701,237652883778⟩,⟨-7772824810581,318696846820⟩,⟨-3346826757761,1137694872855⟩,⟨-1745679992887,1617795206245⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-831133829136,-772437150934⟩,⟨4017589546510,5431564907428⟩,⟨-4874590777156,-3511523401854⟩,⟨-60512161712564,-17989242767872⟩,⟨-1695956109324,42952459876998⟩,⟨-19266182748270,26959199629390⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨2562894522736,2644657655082⟩,⟨-10469206572811,-8679726486171⟩,⟨-7288389867166,-5813930080455⟩,⟨745774675174,52191930314389⟩,⟨10463404857626,57933293394721⟩,⟨-16806140824817,30397418635861⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨418581214638,439717790665⟩,⟨-519774701351,-126296419418⟩,⟨-686331030092,-400771593268⟩,⟨-13742869885104,-3060816690538⟩,⟨-7125343118262,2105359204176⟩,⟨-6480079516727,2030778022955⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨454375327660,460846635420⟩,⟨1809040225074,1824502107342⟩,⟨776530087116,777389080576⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-460846635420,-454375327660⟩,⟨-1824502107342,-1809040225074⟩,⟨-777389080576,-776530087116⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨638664992356,645136300116⟩,⟨-1824502107342,-1809040225074⟩,⟨-777389080576,-776530087116⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨847844773749,867956383101⟩,⟨-5778639187643,-5517174598820⟩,⟨-2462179126561,-2368245886671⟩,⟨25156226468287,30142225825087⟩,⟨17558534788818,19759302355711⟩,⟨4681095355097,5430631062500⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-867956383101,-847844773749⟩,⟨5517174598820,5778639187643⟩,⟨2368245886671,2462179126561⟩,⟨-30142225825087,-25156226468287⟩,⟨-19759302355711,-17558534788818⟩,⟨-5430631062500,-4681095355097⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨231555244675,251666854027⟩,⟨5517174598820,5778639187643⟩,⟨2368245886671,2462179126561⟩,⟨-30142225825087,-25156226468287⟩,⟨-19759302355711,-17558534788818⟩,⟨-5430631062500,-4681095355097⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨13835651997,15876255412⟩,⟨285025026494,325105300522⟩,⟨223272950240,244293286702⟩,⟨-3951115668033,-3382396695791⟩,⟨13429383526,358802521208⟩,⟨1329985492144,1461137566734⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨432416866635,455594046077⟩,⟨-234749674857,198808881104⟩,⟨-463058079852,-156478306566⟩,⟨-17693985553137,-6443213386329⟩,⟨-7111913734736,2464161725384⟩,⟨-5150094024583,3491915589689⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-137834895770,-137405399039⟩,⟨-777389080576,-776530087116⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨8210106777,8695233301⟩,⟨21954273737,25639275727⟩,⟨48521281535,48726789325⟩,⟨-414454277738,-395899347923⟩,⟨136377291242,137413787649⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨14444239466,15324871451⟩,⟨-31139712155,-20130182877⟩,⟨85364664398,85878291791⟩,⟨-780950116139,-643689706208⟩,⟨-151017398413,-143841539837⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1176270725338,1192582147464⟩,⟨-3757850445130,-3554626805163⟩,⟨-623960849211,-581319725280⟩,⟨36401033277671,39731215851374⟩,⟨7292949476574,8086321326676⟩,⟨1496030883269,1665256842403⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨15452620603,16622078060⟩,⟨-86152103720,-68232498596⟩,⟨82627444411,85510870419⟩,⟨-238698112118,77997520082⟩,⟨-350860545320,-299482344958⟩,⟨-77816689940,-67055661447⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-16622078060,-15452620603⟩,⟨68232498596,86152103720⟩,⟨-85510870419,-82627444411⟩,⟨-77997520082,238698112118⟩,⟨299482344958,350860545320⟩,⟨67055661447,77816689940⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-154456973830,-152858019642⟩,⟨-709156581980,-690377983396⟩,⟨-85510870419,-82627444411⟩,⟨2121025735470,2437721367670⟩,⟨299482344958,350860545320⟩,⟨67055661447,77816689940⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨87214374472,93318619522⟩,⟨-619717629419,-569085238503⟩,⟨363159082612,385372564985⟩,⟨2599153454067,3228690398687⟩,⟨-2363302512224,-1980590940240⟩,⟨-1559641480552,-1409176693708⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨93302983732,101217774198⟩,⟨-991114208978,-890770806624⟩,⟨335554643636,371882383584⟩,⟨9347579864457,11110162707590⟩,⟨-3001090907532,-2254930468482⟩,⟨-2010383445211,-1750228783046⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-101217774198,-93302983732⟩,⟨890770806624,991114208978⟩,⟨-371882383584,-335554643636⟩,⟨-11110162707590,-9347579864457⟩,⟨2254930468482,3001090907532⟩,⟨1750228783046,2010383445211⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨998293853578,1006208644044⟩,⟨890770806624,991114208978⟩,⟨-371882383584,-335554643636⟩,⟨-11110162707590,-9347579864457⟩,⟨2254930468482,3001090907532⟩,⟨1750228783046,2010383445211⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨163044967356,167298720520⟩,⟨621047720986,656090878566⟩,⟨142853804767,153989642861⟩,⟨-2383872938475,-1910034509894⟩,⟨-811304411318,-615089323661⟩,⟨-119979863481,-52310761035⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨21250865910,21697775778⟩,⟨191957608596,199241512064⟩,⟨22974322784,24024757794⟩,⟨182078464542,325030240189⟩,⟨5186503364,27034399720⟩,⟨-9444258235,-5343984692⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨242952870917,260572230194⟩,⟨1314858325130,1830661546617⟩,⟨-36858735484,223903708119⟩,⟨-12089677978081,5751089126200⟩,⟨-5574718894100,5795997194918⟩,⟨-4504176574414,3933566894044⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-260572230194,-242952870917⟩,⟨-1830661546617,-1314858325130⟩,⟨-223903708119,36858735484⟩,⟨-5751089126200,12089677978081⟩,⟨-5795997194918,5574718894100⟩,⟨-3933566894044,4504176574414⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨43899110021,69456099236⟩,⟨-592873669167,162360005054⟩,⟨-92639972418,274511619262⟩,⟨-13523913936781,12408374824901⟩,⟨-9142823952679,6712413766955⟩,⟨-5679246886931,6121971780659⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨16687391960056,17764752524958⟩,⟨-128008656858366,-99927864351610⟩,⟨-49407444962097,-30760552687042⟩,⟨567798401807696,1509737851856102⟩,⟨86027499643404,810204755725249⟩,⟨-211999037169934,389794631410364⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨24177699178,25455721596⟩,⟨184188512128,199658033178⟩,⟨42367162558,46861296550⟩,⟨-23862632129,216521087393⟩,⟨-85512802038,1353294244⟩,⟨608873756,27619178188⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨366947227008,411286777760⟩,⟨-168189976144,1028501815413⟩,⟨-500863021339,80726701339⟩,⟨-34389602767906,4972008049354⟩,⟨-13917462341850,9776146844267⟩,⟨-9110428267460,7100131197258⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-411286777760,-366947227008⟩,⟨-1028501815413,168189976144⟩,⟨-80726701339,500863021339⟩,⟨-4972008049354,34389602767906⟩,⟨-9776146844267,13917462341850⟩,⟨-7100131197258,9110428267460⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨21130088875,88646819069⟩,⟨-1263251490270,366998857248⟩,⟨-543784781191,344384714773⟩,⟨-22665993602491,27946389381577⟩,⟨-16888060579003,16381624067234⟩,⟨-12250225221841,12602343857149⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨316981619824,320646770436⟩,⟨1300311670780,1314248017841⟩,⟨225438566316,228154507528⟩,⟨-3712789847739,-3687241503209⟩,⟨-1290126302908,-1277482321834⟩,⟨-274819186688,-274212187012⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1854899716523,-1747566187280⟩,⟨-4473445447103,-1630493285830⟩,⟨-562146836721,1187470424963⟩,⟨-24667882384436,72502239657246⟩,⟨-39719995205352,31063489684123⟩,⟨-28161691624157,29829628277795⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-282236532501,-259144027911⟩,⟨-1787506775402,-1228878065780⟩,⟨-345318577655,-46369856302⟩,⟨-6056295153068,13211455451530⟩,⟨-6028020608461,6591960069697⟩,⟨-4359324557690,5073821332661⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨34745087323,61502742525⟩,⟨-487195104622,85369952061⟩,⟨-119880011339,181784651226⟩,⟨-9769085000807,9524213948321⟩,⟨-7318146911369,5314477747863⟩,⟨-4634143744378,4799609145649⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨843640096,5599815506⟩,⟨-127599274266,36273383595⟩,⟨-41819847502,43886939939⟩,⟨-2917942193518,4128112090669⟩,⟨-2305036936173,1975659958821⟩,⟨-1503258783065,1461629091626⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1097961188,3440243143⟩,⟨-54503898500,9550578728⟩,⟨-13411316962,20336764646⟩,⟨-1168550338181,1497254467149⟩,⟨-979799910826,700783696174⟩,⟨-558074854026,597055595659⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨1457572696,4628449826⟩,⟨-91054113648,7492971678⟩,⟨-25595872785,25061608062⟩,⟨-1657661855592,2636509587714⟩,⟨-1431814728857,1178451349276⟩,⟨-837660812837,872911866592⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4628449826,-1457572696⟩,⟨-7492971678,91054113648⟩,⟨-25061608062,25595872785⟩,⟨-2636509587714,1657661855592⟩,⟨-1178451349276,1431814728857⟩,⟨-872911866592,837660812837⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3784809730,4142242810⟩,⟨-135092245944,127327497243⟩,⟨-66881455564,69482812724⟩,⟨-5554451781232,5785773946261⟩,⟨-3483488285449,3407474687678⟩,⟨-2376170649657,2299289904463⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨43899110021,69456099236⟩,⟨-592873669167,162360005054⟩,⟨-92639972418,274511619262⟩,⟨-13523913936781,12408374824901⟩,⟨-9142823952679,6712413766955⟩,⟨-5679246886931,6121971780659⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3784809730,4142242810⟩,⟨-135092245944,127327497243⟩,⟨-66881455564,69482812724⟩,⟨-5554451781232,5785773946261⟩,⟨-3483488285449,3407474687678⟩,⟨-2376170649657,2299289904463⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (751/5120) u, BivariateJet2.affineZ (89/512) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell003361


