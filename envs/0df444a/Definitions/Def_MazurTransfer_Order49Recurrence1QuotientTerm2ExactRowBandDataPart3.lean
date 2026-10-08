-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm2ExactRowBandDataPart3
-- name    : MazurTransfer_Order49Recurrence1QuotientTerm2ExactRowBandDataPart3
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:47:16.547809+00:00
-- url     : https://prove2.me/theorems/f97d4348-42b0-4d54-87b0-e20b58282413
-- title:
--   Exact first-recurrence QuotientTerm2 data: part 3
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for QuotientTerm2 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 2 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm2ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm2ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0

namespace MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

































































































 def recurrence1QuotientTerm2Row3Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-100334615861956318467425914651946709577479) * X ^ 2 +
    (430933746749529980927241430864449086009810752) * X ^ 3 +
    (-29008126435488162240903799920522554657355801372) * X ^ 4 +
    (-16802159879561736873469747532024897683273532656084) * X ^ 5 +
    (1561663798158415335807596885136836153164608442518429) * X ^ 6 +
    (-43101427193518624815689853016365412660754113118789240) * X ^ 7 +
    (-1134577589373361659005786596686416381930378696256918788) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (108615495445129509473223561728320908530049801272791570247) +
    (695204191848200106106977083466507738307406640347464523735) * X ^ 1 +
    (-83379089036307783616657766559219021656558251539579678757625) * X ^ 2 +
    (-767856651467126727599594488000595902723924785945480670354955) * X ^ 3 +
    (29959621120200587492715590139206667818684898261436796545397837) * X ^ 4 +
    (302537646544830280781528336343137603405642795463493679199427787) * X ^ 5 +
    (-4424395835569125607925084125508699459657105542324091975789130070) * X ^ 6 +
    (-88032507459888442326448692663452148873349100595875238798762741453) * X ^ 7 +
    (678158399720649572000800701168452888720814643442686846122058509243) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (9534318818340170693921282837584832720438250069591780234814701905636) +
    (-24978800852541845274029557871104470332055287242095934357724486923517) * X ^ 1 +
    (-1207674431730347119199390655857284574436963851365084872469535627622602) * X ^ 2 +
    (2839171249006801573060695575073802348272115302405545833479660537461916) * X ^ 3 +
    (78412553790782587384209525875622559163079752121287598719925912955600312) * X ^ 4 +
    (-71451129040861653601796285729990261475729836392935885749263832002916773) * X ^ 5 +
    (-5164594474061299861656595810052963713635352186856091888632687009419757824) * X ^ 6 +
    (5523644357128589009050989740255020067169147606188334863724516645798806727) * X ^ 7 +
    (250271676788227269079325561377716504641908472476649797839538512153505053897) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-291957950286664009405973009407401281824574034504843480995184659684298122057) +
    (-10579210442248000835934622040433026716335102670777633343924723186391401770813) * X ^ 1 +
    (17366065630277661101071199025640228071036075392624870451506330189322596602333) * X ^ 2 +
    ((3 * 10 ^ 77 +
      71187103371392406673421606613735477620792236377791039957656336713912923442892)) * X ^ 3 +
    -((8 * 10 ^ 77 +
      60873152115244589489935143172652789394906200519955268368177267780437238838132)) * X ^ 4 +
    -((108 * 10 ^ 77 +
      51792568934466268849340625600063761707080597345940998624224864536412443441838)) * X ^ 5 +
    ((348 * 10 ^ 77 +
      66479619610814998686804343122902285726976267406613735009591947663789586844931)) * X ^ 6 +
    ((2598 * 10 ^ 77 +
      94124795562279011647636917833883812086273111642227195159325135167185975044925)) * X ^ 7 +
    -((11585 * 10 ^ 77 +
      12304652052106129666543249901360237353406169310280346048206425458587511621626)) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    -((48341 * 10 ^ 77 +
      26038715465057777805155533259198650683976280880599625707068228852246630372452)) +
    ((312921 * 10 ^ 77 +
      21078172475400718730269721899595423831959741332287112436235562156502164952271)) * X ^ 1 +
    ((612908 * 10 ^ 77 +
      36347228673980953568560573113774942387812268821783126757177802453549078909109)) * X ^ 2 +
    -((6860754 * 10 ^ 77 +
      37104304410593078622855633077424656083839022286541530829613034293260373704450)) * X ^ 3 +
    -((1877919 * 10 ^ 77 +
      28466612279776577698476719073460037164879907251421868460337182938119688532994)) * X ^ 4 +
    ((119663306 * 10 ^ 77 +
      23324874431015913912388224848290179718801527151480179517404891840340202523451)) * X ^ 5 +
    -((144242605 * 10 ^ 77 +
      30541642467324902889737822602732813417412052201027926645095082821368341620315)) * X ^ 6 +
    -((1584650642 * 10 ^ 77 +
      42374470166262700051220222461363154391155042557392547108250636443042232600032)) * X ^ 7 +
    ((4524268171 * 10 ^ 77 +
      51932798830466247330372985934650398549578308850008162596765255890999566942667)) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    ((13814479078 * 10 ^ 77 +
      53541608997883585967490047314141013784297269841731809538682161132224734967646)) +
    -((80002574885 * 10 ^ 77 +
      10757067317968580616567907321854085730536566921805709698965947632789010280977)) * X ^ 1 +
    -((25207463721 * 10 ^ 77 +
      23302495038371587584075009648759323209918473264652410360794144085524066777389)) * X ^ 2 +
    ((938662045697 * 10 ^ 77 +
      95088712534806641114524579876275183796131689065906736937227484669572547426307)) * X ^ 3 +
    -((1464055064025 * 10 ^ 77 +
      21657964206527544305325965282426554485954721318026606883179755651788421980836)) * X ^ 4 +
    -((6546260600555 * 10 ^ 77 +
      20623797246524569378077426301989385460521307326713527998938702211332619479665)) * X ^ 5 +
    ((26506046114647 * 10 ^ 77 +
      98869841583959634875733596165462949964660131490357194952568222746563935135099)) * X ^ 6 +
    ((4589208394427 * 10 ^ 77 +
      34800129612417391742011910270483605808748593175519842921943845013576872431205)) * X ^ 7 +
    -((229983756124822 * 10 ^ 77 +
      54909400900830279438288313614708757866813645637450498699237650086043481599773)) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    ((449533448902609 * 10 ^ 77 +
      66949391943574965947434153516875752637912694863793280439576733173264604337372)) +
    ((723498703894318 * 10 ^ 77 +
      13129060915564886740047411002202205196569054261633055488769178236529733610604)) * X ^ 1 +
    -((4703418374996160 * 10 ^ 77 +
      53364798380236572740454468968546222142285594721108534107340128081303773403553)) * X ^ 2 +
    ((5858043015348712 * 10 ^ 77 +
      61783761474602578947637132531350489114174132764672782153936512907029699915801)) * X ^ 3 +
    ((15210584106468433 * 10 ^ 77 +
      08413859209532904252074859368500236072275799946465624953208203164634988377615)) * X ^ 4 +
    -((68369301598814762 * 10 ^ 77 +
      47840241375739567533657232927756773059139983124204076289800459283710177963592)) * X ^ 5 +
    ((79233319107987273 * 10 ^ 77 +
      49059157350697127282965133558166765183717719021059316571287211093222084880177)) * X ^ 6 +
    ((149355134524915633 * 10 ^ 77 +
      21763056715909465946027467112125931949326118209234409214988321883179021321035)) * X ^ 7 +
    -((713505045433846044 * 10 ^ 77 +
      12845252972436780071206539555745258560589497595279417352822684716202165119893)) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((1062324261071585599 * 10 ^ 77 +
      01994038269737089466131573446063060206542219623263967289465806148861335810078)) +
    ((239564992416616689 * 10 ^ 77 +
      16503811867371686957732699487603538350244990070200312088859158130368828801354)) * X ^ 1 +
    -((4290375592790026875 * 10 ^ 77 +
      03801040670781241883032973871513285144754314611547692061684969811547048174189)) * X ^ 2 +
    ((9142297412877619634 * 10 ^ 77 +
      80797796983256167071245051776839677482154537376168406116095667912160271266489)) * X ^ 3 +
    -((8414249060640546397 * 10 ^ 77 +
      72271507396039813236727831363926643798976466156463303666794335132066245373583)) * X ^ 4 +
    -((4748941421768491090 * 10 ^ 77 +
      91762566240509659130077065145980915892788774979575011979257527014476980893840)) * X ^ 5 +
    ((28772068883137938318 * 10 ^ 77 +
      91633534084622742056238861099679659547672799993087829559088593971874366971555)) * X ^ 6 +
    -((48107140454984027294 * 10 ^ 77 +
      43951056088341671015818618341282188975859047763095970914545415641363971896138)) * X ^ 7 +
    ((40902142681625947421 * 10 ^ 77 +
      56156757946576925222198802958380616419920594945523254943041981519333431332819)) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((1723485411736996603 * 10 ^ 77 +
      70377911861604995195432671196893892695182869370013387208392931203721475089728)) +
    -((61711437211031029533 * 10 ^ 77 +
      69282130033898531270160295362287089097617918480238310037482453854210229262394)) * X ^ 1 +
    ((102469019780088817901 * 10 ^ 77 +
      94253708457302622971713340373098451058195570498229860753153680931913961899121)) * X ^ 2 +
    -((96358462997099662307 * 10 ^ 77 +
      41623884671767721268090818809599728153627157149195928445249939115115696406409)) * X ^ 3 +
    ((47133758180987943159 * 10 ^ 77 +
      10279453619454639485568466076046724747952779879375371010416866404682057659607)) * X ^ 4 +
    ((13736739152483380204 * 10 ^ 77 +
      77234598261183130549008422310845416935974735821387370212335910834247036445930)) * X ^ 5 +
    -((52641221956707753283 * 10 ^ 77 +
      45738024250764690356782555692309088094557874112710221745524840447578111688434)) * X ^ 6 +
    ((57050743828846680628 * 10 ^ 77 +
      75347593091887423701729828194259246039368897276425172680923901005764329828702)) * X ^ 7 +
    -((37898611470416234282 * 10 ^ 77 +
      78186316454365645609244417089023021401495819856431469972548871505937904874921)) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((14624089751838272244 * 10 ^ 77 +
      43198696591291194871103208261593027398829537570075886029261629120256012184680)) +
    ((147727885251307708 * 10 ^ 77 +
      28766723201127172024587272145726640350340789256887156035033046044998606605040)) * X ^ 1 +
    -((4847053546114369514 * 10 ^ 77 +
      03459870672119536819874499848013963142454809143097746269706528128225581210149)) * X ^ 2 +
    ((3967941788056510768 * 10 ^ 77 +
      63832154917824675352403665465904986216379882711107630458614926909994035050640)) * X ^ 3 +
    -((1926505042430145899 * 10 ^ 77 +
      20845222996781777561902159118902520663012941993975369113155864233029876961898)) * X ^ 4 +
    ((619680939569367964 * 10 ^ 77 +
      17555843943970714250526818383690045797639960215227396716223009968281919004966)) * X ^ 5 +
    -((117596945818424467 * 10 ^ 77 +
      33101554725369963257882203071825429490490261665246607480111476417291446683456)) * X ^ 6 +
    -((3325290776669445 * 10 ^ 77 +
      17994095677712101398690367656438054397938930815672199148879811605655219444176)) * X ^ 7 +
    ((17729513344083493 * 10 ^ 77 +
      40424792538985751884399941718362620655352036133244218580050724144063061550921)) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    -((13788397644405215 * 10 ^ 77 +
      04024690139210490200083728223261527245723333447065568971187288340774452411586)) +
    ((7626708158578727 * 10 ^ 77 +
      07417627050699717804426180459217934316010973794365802460504177386929338432058)) * X ^ 1 +
    -((2771940250734562 * 10 ^ 77 +
      54836890097325483301885548733285997426360901582424304293360794521875179733989)) * X ^ 2 +
    ((439893175201998 * 10 ^ 77 +
      25515995146073217376125053877018700901589728483126960478815130541141690960251)) * X ^ 3 +
    ((127805714095991 * 10 ^ 77 +
      73905553824416092015317815789826323351649748681263850547521459241555373856358)) * X ^ 4 +
    -((94575757876031 * 10 ^ 77 +
      11958846455963825461814038911426488322405566010909951555031945299057436034577)) * X ^ 5 +
    ((21563754722125 * 10 ^ 77 +
      45216252992110642310695417980039148502749908536104345557286371289084013752595)) * X ^ 6 +
    ((148396897857 * 10 ^ 77 +
      09199240100858498768837304748893260816052630076941100954714053453078410597329)) * X ^ 7 +
    -((1203904458694 * 10 ^ 77 +
      92230292332729188485629705717661308999386875256072180615504337220477997930688)) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    ((224085452667 * 10 ^ 77 +
      22747211694236217810450701921776065880047381401932048930163555243401584321403)) +
    ((10125537553 * 10 ^ 77 +
      46848647335438709278669294807708788941432255584609721855626055665609194748322)) * X ^ 1 +
    -((8038413915 * 10 ^ 77 +
      60942475819601959498165198271228921767795506178636579674396343825308362383085)) * X ^ 2 +
    ((449716977 * 10 ^ 77 +
      73377233897175750807037524406812533625036173640067210090706118761428974229208)) * X ^ 3 +
    ((136788756 * 10 ^ 77 +
      87087797944077125360351127246887955065446602324006655278578884395323222938096)) * X ^ 4 +
    -((11411549 * 10 ^ 77 +
      49809867670969159311691843890837220813038001301026816919775190880709481797046)) * X ^ 5 +
    -((1705443 * 10 ^ 77 +
      05480527627349905352031233802076471684288351184253643722124324842147299801975)) * X ^ 6 +
    ((73654 * 10 ^ 77 +
      07477758103007094429943008488223843684900324380169781305406036847455600757926)) * X ^ 7 +
    ((16185 * 10 ^ 77 +
      73042778414561495759813467149024642848363622288705557957545470002180271082758)) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    ((799 * 10 ^ 77 +
      99066587891331837284710253558814305381829566244646915137743964834484043921541)) +
    ((18 * 10 ^ 77 +
      01918394944636421110799242406766461676042096830330632987348292423472210825599)) * X ^ 1 +
    (20191968833410389717830257642081037049213344160621089813644929748799369198899) * X ^ 2 +
    (108602126034687287662216483112387190088627120428148229822085836256856209588) * X ^ 3 +
    (219742096292006321128921526354867581562956454735527656267208703148871809) * X ^ 4 +
    (-161063002458311991159408008925611340100478352839427153179310828969625) * X ^ 5 +
    (-1004337252738789430788918186207190279604641364095420271768924013313) * X ^ 6 +
    (-751706000104839194422203693686514615945819204776186557466831447) * X ^ 7 +
    (-97260150707443911501335913343963801799855753424737764245576) * X ^ 8
  )

 def recurrence1QuotientTerm2Row3Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    (-976747453683103993720216834715910993530577636443643903) +
    (-77254406311655023207748613958959914197122612762) * X ^ 1
  )

 def recurrence1QuotientTerm2Row3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band3 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band4 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band5 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band6 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band7 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band8 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band9 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band10 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band11 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band12 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band13 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band14 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band15 +
  MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band16









































































































































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band10
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band11
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band12
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band13
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band14
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band15
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band16
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band3
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band4
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band5
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band6
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band7
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band8
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2Row3Band9


