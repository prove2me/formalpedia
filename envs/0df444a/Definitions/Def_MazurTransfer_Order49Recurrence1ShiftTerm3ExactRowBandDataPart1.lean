-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart1
-- name    : MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart1
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:45:57.672922+00:00
-- url     : https://prove2.me/theorems/98386399-5996-4559-a4ae-49a7a4be0e3c
-- title:
--   Exact first-recurrence ShiftTerm3 data: part 1
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for ShiftTerm3 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 3 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0

namespace MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

































 def recurrence1ShiftTerm3Row1Band1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (529376468614389077436976) * X ^ 2 +
    (-2288885857949590672668730956) * X ^ 3 +
    (218079071505138636739149407112) * X ^ 4 +
    (85929377421496670212692452826556) * X ^ 5 +
    (-10901881501248580481033928727539074) * X ^ 6 +
    (398501921668764926327746456106109627) * X ^ 7 +
    (5492130886499661004639907155697279994) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-898382941273102212355382675592983348391) +
    (7458871324931510681956351659751514250619) * X ^ 1 +
    (980386089045363832537789429419069850302762) * X ^ 2 +
    (-4598653978598955570399395206136261468587673) * X ^ 3 +
    (-651414755428376191469169516335720863556051374) * X ^ 4 +
    (-1348507576912669235420736695794707971015072677) * X ^ 5 +
    (228032535540408485665231965103628007371522235162) * X ^ 6 +
    (2004386485310361127875578915181840378608387843525) * X ^ 7 +
    (-47836915795580173637582590158138591293606233782945) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-692366890863550957889819119933698524214408908172629) +
    (5321892980017610705281949369576628155315499643842498) * X ^ 1 +
    (137826824014427670251168957211305752174861898901565059) * X ^ 2 +
    (-161417979602687177798727182178480120548545903853835393) * X ^ 3 +
    (-18249659813687490377596600540982139856978726215872068198) * X ^ 4 +
    (-40855934624019413530669130600709029572700498658016189142) * X ^ 5 +
    (1714388753086703091599704812627782893202593802258595282475) * X ^ 6 +
    (7437489311368630336391340067765504267722144354310194153463) * X ^ 7 +
    (-117276493878213885960636607074300692284932264307515588337469) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-796494277521847982318119682118307831447568736167408626843703) +
    (7394324581523967571465353629184385447959112902688767787760321) * X ^ 1 +
    (48300274868166296008544848956611515417050738287587598632826129) * X ^ 2 +
    (-325837226046953390953746919870041446581373109157329473474671053) * X ^ 3 +
    (-2786357387913420989712591105311434191395290769816082072812340359) * X ^ 4 +
    (15816029774736025637382624393839498708616942113490729363230799319) * X ^ 5 +
    (107010369239544132508421985084869211036255593080291144538007603459) * X ^ 6 +
    (-594079849498289138766428988173520895060247548893705693172565663775) * X ^ 7 +
    (-3643014232922842373618922137710149944527925111739940483887610212144) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (21900170990718352193666697161261303500790771094753304376741668498628) +
    (90567560078700182835677167896333829556642292566089358477673938814487) * X ^ 1 +
    (-679314932942689544439231813458320006982476848826841982074647555447771) * X ^ 2 +
    (-1636612682214167968217759398179677030814511698548597683902331756467758) * X ^ 3 +
    (18038851068466508587609634691579147163217824671522535810483042555544919) * X ^ 4 +
    (12989351457176163899114814525464589858499824759030968712907061097825645) * X ^ 5 +
    (-387025578682344985185532149798616694994029443081948674771530103843647089) * X ^ 6 +
    (328720053761924969717259737619676039655353226164111767564991678130753619) * X ^ 7 +
    (6351861321943856881390131467552955897894212820717164259299204579505188565) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-16156837354613292125405944807792752797428225487342777272787424474072951435) +
    (-69564433664467590773362515021513950986789804342403762731974046328589231309) * X ^ 1 +
    (362935096504657555582177283718606809524900391957877233520077866128623085155) * X ^ 2 +
    (236228580772731386108672118593699486437627008343860084581753010007990885366) * X ^ 3 +
    (-5066232794424114339895226023819972132818404183576576983628500385245769568945) * X ^ 4 +
    (7770929028844684357379197571953004725180251746699085629785554743921030869737) * X ^ 5 +
    (39446615149845537232951848935334778899915648581191250434951675186933381691240) * X ^ 6 +
    -((1 * 10 ^ 77 +
      68074889893569824185395107420329898860306675863136451986875925386392107984319)) * X ^ 7 +
    (-1764375775115869472604489249237332693719161066193308921241844926639078704223) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    ((15 * 10 ^ 77 +
      36067097817955248219104820247241749335528810258236951197660566978820800960038)) +
    -((36 * 10 ^ 77 +
      37152564645160790480587806149564264010331544531349906809315532297663794441937)) * X ^ 1 +
    -((34 * 10 ^ 77 +
      60913424894414457671161149263734800873418887113012185723268628876297635595261)) * X ^ 2 +
    ((357 * 10 ^ 77 +
      36736547246011917898648729298238138733368011955962350213155407654869045491557)) * X ^ 3 +
    -((652 * 10 ^ 77 +
      96270219687880649703393706909609109476099347311553190569200348586647246634969)) * X ^ 4 +
    -((676 * 10 ^ 77 +
      52991354244702400354702730986938062824529564711350926218714408664119458849189)) * X ^ 5 +
    ((5713 * 10 ^ 77 +
      94329088405090665233969238236248840752927961928355539728026614361686707081921)) * X ^ 6 +
    -((10971 * 10 ^ 77 +
      30751735605414586873315453193796309169565943025579930901007830549013072173801)) * X ^ 7 +
    -((1462 * 10 ^ 77 +
      17061487133622056584782636756595337527171509520103434600025331544678078961461)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    ((57374 * 10 ^ 77 +
      54451937242323637847522540606828480606977107857439214536688883877641081514055)) +
    -((144225 * 10 ^ 77 +
      11955755288213636173073888609993537275005566031056791801293341267737174275702)) * X ^ 1 +
    ((141226 * 10 ^ 77 +
      98622166627486287544868992450705027846860037187091501787812131606192861569457)) * X ^ 2 +
    ((176311 * 10 ^ 77 +
      06697252625012316629114286851280674292380661509219416349229641586009486064956)) * X ^ 3 +
    -((940228 * 10 ^ 77 +
      83894447355491448460551751338162230578642579434042736913438439600815464502552)) * X ^ 4 +
    ((1851106 * 10 ^ 77 +
      25518987871838879861892115468026027921460135456059640007945234134249555691815)) * X ^ 5 +
    -((2036158 * 10 ^ 77 +
      16822202786348453176519427424336715685083566254062705304250923489669789825183)) * X ^ 6 +
    ((492519 * 10 ^ 77 +
      29119895049153008808517183357331725894849761679622766849592090320892482025843)) * X ^ 7 +
    ((2967457 * 10 ^ 77 +
      52489168048690934957669115384955751569428668188642586618966966440471423617192)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((7044224 * 10 ^ 77 +
      28633810497284613855077513979658170528148430687187364508113050400112650385339)) +
    ((9420606 * 10 ^ 77 +
      55818285437565413739000522997766379055261972193444776371511982294172413087056)) * X ^ 1 +
    -((8325877 * 10 ^ 77 +
      93015771511255608769504203108091399502652129429934857643725889825596640978308)) * X ^ 2 +
    ((3979321 * 10 ^ 77 +
      61923751376064696209590541369650318534423807438882022093140314064013158900033)) * X ^ 3 +
    ((1417821 * 10 ^ 77 +
      64580485770547415347024810090528400406727533715094771616755577000056215430484)) * X ^ 4 +
    -((5221737 * 10 ^ 77 +
      39972520200202481452565071322292577979788865675267664115763825608262269746724)) * X ^ 5 +
    ((6101396 * 10 ^ 77 +
      62640551335681647217761651771479460142832847192412996977371478471364200518068)) * X ^ 6 +
    -((4596411 * 10 ^ 77 +
      24053655752148619762916868756981713606328913724297798594331176646914499967469)) * X ^ 7 +
    ((2275624 * 10 ^ 77 +
      65762433440687594447271878133198057724161406683739744780633407893061632910774)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((474421 * 10 ^ 77 +
      31552876892811664659692783603954639299805077000955688166967739042634798815949)) +
    -((354283 * 10 ^ 77 +
      36141774244423207687211475595326955480366885900105022449200260931540410388731)) * X ^ 1 +
    ((462831 * 10 ^ 77 +
      49784967951268076639091957960034092062260985800353909758259350031799151415407)) * X ^ 2 +
    -((291593 * 10 ^ 77 +
      83510691674215317656911240247826780386694215453019067430825811392471907131583)) * X ^ 3 +
    ((122735 * 10 ^ 77 +
      77225551582943245356599839644471756788238977734974590019383514326521570634712)) * X ^ 4 +
    -((34688 * 10 ^ 77 +
      21041559961148793465023468810871085651063297507928182151517707101338037566531)) * X ^ 5 +
    ((4822 * 10 ^ 77 +
      88812695428556729312135989569245726034096288098361861867538390508320978542391)) * X ^ 6 +
    ((1432 * 10 ^ 77 +
      02966535242340428439315606297040627777824540012756375852837281122562992798980)) * X ^ 7 +
    -((1690 * 10 ^ 77 +
      34165229779978002194433431974065995915507031495673377335084726088705576891460)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((1065 * 10 ^ 77 +
      78532558399975255554941720451790492327306613554579734065550911912915613291632)) +
    -((495 * 10 ^ 77 +
      45295925634943315657035327934062677833552368424196386178639829779856983968579)) * X ^ 1 +
    ((149 * 10 ^ 77 +
      32380971054456662616454051203862536790788473316264330550775667157061526167666)) * X ^ 2 +
    -((13 * 10 ^ 77 +
      89228772105880555830723948809862312311738758529644738280934941142141008464616)) * X ^ 3 +
    -((10 * 10 ^ 77 +
      60960864393374150147721758748200940535113511690717306629480857155617264842312)) * X ^ 4 +
    ((5 * 10 ^ 77 +
      51392479071935435911854060980812949235567604237062237173708377013413660488810)) * X ^ 5 +
    -((1 * 10 ^ 77 +
      03025053297758315256391965843024808029177545533388836823748913004132061552187)) * X ^ 6 +
    (-5994870230145218970898303967833898142331103914455639064312677757194715997902) * X ^ 7 +
    (6818537088303898842549966660460350283140752237493596686947280910804924283236) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    (-1053709393416417435235150318484752555769782049595872839564489176771312975955) +
    (-82507243331107607165473748331847493201541913625481393786895345053809753759) * X ^ 1 +
    (41374374112401311902079972917082888375720710098638246660063797986764249789) * X ^ 2 +
    (-1682377194215396082099633343934374984354507180796557444280637930961338304) * X ^ 3 +
    (-720573009644417465041810158188771048716096609549852652859494159011530472) * X ^ 4 +
    (50069686114853978127344013098715649425543567643812849054796806976294431) * X ^ 5 +
    (8735897298274439003088088330760374143820614918409639917154955674308076) * X ^ 6 +
    (-306491793783312129583923035698351227867521179203935611256893529691170) * X ^ 7 +
    (-77579049274704822673328883312621157854912020130806561194288257572062) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (-3915715212139916269173624244710743530343263340717563751102819948684) +
    (-88977657638699178230279235610285946481211479012962554309711440017) * X ^ 1 +
    (-1001590473094742898646514190032351003828347067192308775529633228) * X ^ 2 +
    (-5401091073909977514595671325603464545247147483276252572297885) * X ^ 3 +
    (-10951803911364188009279245487341125870522319615501414190437) * X ^ 4 +
    (7983905631365538305773319325003630552793578648724819490) * X ^ 5 +
    (49998103415894063664873357528875182277304533934102696) * X ^ 6 +
    (37439564869412174190534318618978678032618909507717) * X ^ 7 +
    (4844600412791684923357378086175323535828147149) * X ^ 8
  )

 def recurrence1ShiftTerm3Row1Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    (48652893221569354017241034267996760629028) +
    (3848129419579903282009754498552646) * X ^ 1
  )

 def recurrence1ShiftTerm3Row1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band1 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band2 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band3 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band4 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band5 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band6 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band7 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band8 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band9 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band10 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band11 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band12 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band13 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band14



































































































































































































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band1
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band10
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band11
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band12
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band13
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band14
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band2
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band4
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band5
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band6
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band7
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band8
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row1Band9


