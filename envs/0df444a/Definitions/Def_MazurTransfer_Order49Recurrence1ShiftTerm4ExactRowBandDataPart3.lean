-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart3
-- name    : MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart3
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:48:42.266275+00:00
-- url     : https://prove2.me/theorems/a41407a1-4c7e-4a55-9967-e016cd5ec890
-- title:
--   Exact first-recurrence ShiftTerm4 data: part 3
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for ShiftTerm4 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 4 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0

namespace MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



























































































 def recurrence1ShiftTerm4Row3Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (342992257042605952141812593926686855660) * X ^ 1 +
    (-832474243731504501939955053919756720770272) * X ^ 2 +
    (-1918928424112106456842493538078022575393645948) * X ^ 3 +
    (673389784301728637204991128976288890083439913513) * X ^ 4 +
    (1406031786650407708770893185986806445546278633429) * X ^ 5 +
    (-6505922419478246864743959487430135812981544276976497) * X ^ 6 +
    (103231980598126133517758162317949659014957503263520275) * X ^ 7 +
    (10551505496616077439485470166612427707912988147567255765) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-72373346319113951045660530193409867632922109542323126664) +
    (-7437204466474578710723626590068290754559745513955263966614) * X ^ 1 +
    (-9664204860881401887160496876745096372652796023319776974977) * X ^ 2 +
    (2859071793277860902800604503936751765726071298887117098272432) * X ^ 3 +
    (11100040795336182410525427702455450553721558033067753377027443) * X ^ 4 +
    (-486110680922649575163010705137815816663663020012155242333629457) * X ^ 5 +
    (-5887504910334194219371485672038687656584175628592836510446206972) * X ^ 6 +
    (82502213895905217404268194198486217638463611488591796218627658283) * X ^ 7 +
    (679669784465145819635274673641358285075212545041372128857573148637) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-4078861436633878632326490536304238000014226575783680179297620261503) +
    (-103552997977436248341920320477541867130086231277128843863865905995087) * X ^ 1 +
    (380713251808446015801759079318258587792030956709162857949806310334594) * X ^ 2 +
    (6717808396191023283364820829397156337029456964154863698115082433318789) * X ^ 3 +
    (-8552153262255427530697216952986540114496727490060189686402404575198414) * X ^ 4 +
    (-447610949014369365270814404592979402531993543155134887344002528412357083) * X ^ 5 +
    (400720186678456343669843617185066545519587716598192861778427076091631822) * X ^ 6 +
    (20672889106742702535555174402229479820314925909115064446766558665306981271) * X ^ 7 +
    (-11413795779173592148527916259464848489252259676032253384727457118385294225) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-833706471856406189325742728856942912937697198647416331942813316903942185192) +
    (658322427626785784870123622045026608509492091290690913739877274456091342519) * X ^ 1 +
    (27759313917614524489432019757972121328152350817231204854425657461420400098628) * X ^ 2 +
    (-36322773646815549634396332554237617299707463687371822470902378994054271467708) * X ^ 3 +
    -((7 * 10 ^ 77 +
      74764655463380324075888893475329773096713603117819219379714877760767207913090)) * X ^ 4 +
    ((16 * 10 ^ 77 +
      11728237423944474860140510101097108237172993790208755453187855048523012784610)) * X ^ 5 +
    ((178 * 10 ^ 77 +
      76108967573453064103392290381817173344560394701593453036000139496828769658044)) * X ^ 6 +
    -((566 * 10 ^ 77 +
      74209035777474261415101114325522966498960940572550401160049686939876972470904)) * X ^ 7 +
    -((3234 * 10 ^ 77 +
      03304959164172413763233095212689326546724345754054792298935506203439945374300)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    ((15589 * 10 ^ 77 +
      40428600134920752322406619019890363176500457745385276998441355197365382342314)) +
    ((41146 * 10 ^ 77 +
      28106812492499197711367637962702529296608735083426986100785283751240175922093)) * X ^ 1 +
    -((339192 * 10 ^ 77 +
      72201971397050620684917939976890774833120465186461815358804205633927004897897)) * X ^ 2 +
    -((187075 * 10 ^ 77 +
      31152732713018686766107503375270429938803063140426204857374915679288869671150)) * X ^ 3 +
    ((5703547 * 10 ^ 77 +
      95119594009108966123109269310346444056148837212006263065050514342162453437002)) * X ^ 4 +
    -((6567886 * 10 ^ 77 +
      91187965612678671450272845907954095396986775712357482181959491944415019106977)) * X ^ 5 +
    -((69871467 * 10 ^ 77 +
      32203771569294787051179385879151986496030167671970896749292356632325773974017)) * X ^ 6 +
    ((212683836 * 10 ^ 77 +
      01866217129090983680527847146626588527315377304232615689131678892417552119224)) * X ^ 7 +
    ((498779668 * 10 ^ 77 +
      83634542659285654597277505169521150151043719901016107113276750946846669758418)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    -((3517706557 * 10 ^ 77 +
      68890259518658895318996244736543250360694903076231386340086263725024022518369)) +
    ((1175374812 * 10 ^ 77 +
      12912052628843516726819203067143936658853939738866100980063971318867621960798)) * X ^ 1 +
    ((35898527685 * 10 ^ 77 +
      49251892377900682042474357643433338007201746355812264463760052659429961033474)) * X ^ 2 +
    -((86415735246 * 10 ^ 77 +
      79430317396675542693291747262917481158698787153722019192387176702114504345919)) * X ^ 3 +
    -((168733297251 * 10 ^ 77 +
      70060252118558651799891886820893138061464710503567045787769238383010047367341)) * X ^ 4 +
    ((1170942558233 * 10 ^ 77 +
      80130968043247685820327109278701575099964163016668776001781372016400988461056)) * X ^ 5 +
    -((1109883310061 * 10 ^ 77 +
      75226030340960381456235407799296232777406340870267636309294901583706468006302)) * X ^ 6 +
    -((7289684411326 * 10 ^ 77 +
      59636562164180164665281566489033120477581510828325893235997298946983843400255)) * X ^ 7 +
    ((25663432217311 * 10 ^ 77 +
      82371508227144172957441319147451536728764926249791269864063673619919905989588)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((5741559824367 * 10 ^ 77 +
      93220534301864644946178214210377154317701994452996752200355718119010532273142)) +
    -((168189561944859 * 10 ^ 77 +
      52014675183882737030855057023854263479163459235011500459649728467517146309877)) * X ^ 1 +
    ((447602111479200 * 10 ^ 77 +
      96650453301695729991580602765565974336928036105985936750812690711032593546196)) * X ^ 2 +
    -((45819473455453 * 10 ^ 77 +
      86312782914709182765026423961230721594969208839109200553212414958410074246522)) * X ^ 3 +
    -((2531148396595554 * 10 ^ 77 +
      09558709266361534838406605308856469689464111650278776138460389747569928771004)) * X ^ 4 +
    ((6641123147864006 * 10 ^ 77 +
      09268100938017735066480802478311395448715425774780829711723932528773121979551)) * X ^ 5 +
    -((3806712040071625 * 10 ^ 77 +
      23257980770518054397512689882258400756061534097558996675239269501767063646364)) * X ^ 6 +
    -((22242629731318035 * 10 ^ 77 +
      11486023559038384469267024885752269678548345896278234170775742242446947477518)) * X ^ 7 +
    ((74178165079809521 * 10 ^ 77 +
      14505538805652304823071157753007261469015555204295131658693772775730505079451)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((99035830496245863 * 10 ^ 77 +
      28825572307288863157534062312659398701785851596477296967252056788721552452834)) +
    -((26987014485680583 * 10 ^ 77 +
      73670149781905491747275729636654313126940961157886752478335248205635718350095)) * X ^ 1 +
    ((411104100260923313 * 10 ^ 77 +
      38088974297401774218906530982013874058550904245275335455551417079021597195190)) * X ^ 2 +
    -((951090331991987230 * 10 ^ 77 +
      33924345212556787952944463374172419029153483335305222217383099625220830015547)) * X ^ 3 +
    ((1202745343071995349 * 10 ^ 77 +
      33927585696464268201516931175038450804030634384261480521371035515800430613480)) * X ^ 4 +
    -((554687580642363059 * 10 ^ 77 +
      65561112270733542833529528951614939054904846972893213036847778085344856500422)) * X ^ 5 +
    -((1255254705166781775 * 10 ^ 77 +
      61930167526915630346105510717935901122515521663020801389838503099872771535138)) * X ^ 6 +
    ((3661627623985207033 * 10 ^ 77 +
      50188225236209919025173016088722699149018334737245853560740791429338251380851)) * X ^ 7 +
    -((5375617134184261988 * 10 ^ 77 +
      83391601624906220230466554760656750523771530415581329793416824650680735717546)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((5195934365976894013 * 10 ^ 77 +
      30981859196425096928818716578560506842196385037919877362030004639885390310474)) +
    -((2943260387899217436 * 10 ^ 77 +
      78943879304505673542234631101998553197472177794500557938985365055283589940624)) * X ^ 1 +
    -((307590444866758899 * 10 ^ 77 +
      88442003209750373119716310513118274062414949787955751348977534936620008097415)) * X ^ 2 +
    ((2949724623758184895 * 10 ^ 77 +
      24980158143833589666823676232868985514387263540598405532109843480434860759883)) * X ^ 3 +
    -((3918876657250070962 * 10 ^ 77 +
      72833553058566638784065549328563401372634157374604074822076815471021778322822)) * X ^ 4 +
    ((3250875152958529392 * 10 ^ 77 +
      85253155902623199918937688666055608276291026025145664297916294437517862888260)) * X ^ 5 +
    -((1791997267555362463 * 10 ^ 77 +
      40319753193606693724107647900328792035899342362552538173207762583496881512716)) * X ^ 6 +
    ((467840584038612752 * 10 ^ 77 +
      60692219223896995375320266876618377530567464818006509888869273886004842961297)) * X ^ 7 +
    ((253153437815185879 * 10 ^ 77 +
      84753098433950295017411732546913030285599376421592456957931204546806875279896)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    -((411280989192841102 * 10 ^ 77 +
      53201003967274985098221219980072902460161939478076796013624205641595190843894)) +
    ((285863412905304577 * 10 ^ 77 +
      64296598757515460691720014457697020759849142659214105337618034772403836745745)) * X ^ 1 +
    -((121756992213643099 * 10 ^ 77 +
      80697478659124368153885938377367919790302883789183536860537289676181001914113)) * X ^ 2 +
    ((23686606955660157 * 10 ^ 77 +
      25600861064635479755519065159199307218776603387125062610345742386905810285655)) * X ^ 3 +
    ((8847070767748013 * 10 ^ 77 +
      40575215374144673506656052255470926192069825126923226707851324129952134422441)) * X ^ 4 +
    -((9819440298650826 * 10 ^ 77 +
      26126713260672075714029736620172063602273166470102822888408966441994671438474)) * X ^ 5 +
    ((4222983520537407 * 10 ^ 77 +
      69962707692135921459171115428762895332700032148559109343927823726857383569373)) * X ^ 6 +
    -((843383488964409 * 10 ^ 77 +
      10918786625382431213672747228185914501562598809018217608881264679080240976753)) * X ^ 7 +
    -((109696299359388 * 10 ^ 77 +
      71890230574595854429559037510118272447120503414744281199877984055050441033400)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    ((133695590886938 * 10 ^ 77 +
      27427000734375624018960682379616812219099428593815881667313972646156396300825)) +
    -((40170464469345 * 10 ^ 77 +
      73986952415764455255238073407432826241387793914026349694831659444765474366218)) * X ^ 1 +
    ((2860637742926 * 10 ^ 77 +
      10834095234121546515963141535888895427717428287908859285461793012171301786887)) * X ^ 2 +
    ((1884448115865 * 10 ^ 77 +
      63079664009196544440085851497421660610723984619245279986137338118588281116584)) * X ^ 3 +
    -((644795970206 * 10 ^ 77 +
      60918154938150205954966473422874194515018785506146190798298245627556016877319)) * X ^ 4 +
    ((47339823375 * 10 ^ 77 +
      62513002038354844166055800705877525942965439106230026025897910015961894056820)) * X ^ 5 +
    ((18026607908 * 10 ^ 77 +
      32274925223111714118524879917742136736698126163998423908739191485465369024498)) * X ^ 6 +
    -((4266839705 * 10 ^ 77 +
      82337092097224605251171781832368356558778409318009524087672145123895960541227)) * X ^ 7 +
    -((20859134 * 10 ^ 77 +
      37892615798699511324274503364930096206232466251247337831490765560391306502819)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    ((97514478 * 10 ^ 77 +
      88717628843074817481334509235566499283627701447696753214285057547901578108062)) +
    -((4331621 * 10 ^ 77 +
      63411519056759583069478055942953701642065474141659462491157624047698411339557)) * X ^ 1 +
    -((1271314 * 10 ^ 77 +
      46354684721027893323480256918494829608543157219603143695411626761035724419639)) * X ^ 2 +
    ((29408 * 10 ^ 77 +
      92387836409889451216761948499242972959234475857010411871231372281187005422843)) * X ^ 3 +
    ((11128 * 10 ^ 77 +
      65405585569422641854197281018625887997140503389543868203612646513397878879417)) * X ^ 4 +
    ((604 * 10 ^ 77 +
      63708377937326903401416442765820629569144867894744612974548124529757481886973)) * X ^ 5 +
    ((14 * 10 ^ 77 +
      37792868545032802231286402618092097490360368815104030924655955455602234761495)) * X ^ 6 +
    (16806541073069689090716236789618717704991132205429253196671219988071393720250) * X ^ 7 +
    (94346912429282041407119650895955218694204536614596167117454194827981574566) * X ^ 8
  )

 def recurrence1ShiftTerm4Row3Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    (204785925803259690624927468422123602785457524955994046639991618527057064) +
    (-109204709296801237121099753523185127374868117418003474834345052824244) * X ^ 1 +
    (-904901937223248356909239150476518429457300711286662559543665988862) * X ^ 2 +
    (-749570046974281169426090258569731159987629206088276335855013262) * X ^ 3 +
    (-113753821928133072628173358949718521302575230622341600897111) * X ^ 4 +
    (-1602037911391712169382624399879908341513689469119220938) * X ^ 5 +
    (-337324564341960571048241864258870165436383703158) * X ^ 6
  )

 def recurrence1ShiftTerm4Row3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band3 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band4 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band5 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band6 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band7 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band8 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band9 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band10 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band11 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band12 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band13 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band14 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band15























































































































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band10
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band11
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band12
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band13
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band14
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band15
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band4
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band5
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band6
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band7
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band8
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band9


