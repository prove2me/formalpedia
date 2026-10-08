-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm0ExactRowBandDataPart3
-- name    : MazurTransfer_Order49Recurrence1QuotientTerm0ExactRowBandDataPart3
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:36:04.726925+00:00
-- url     : https://prove2.me/theorems/b14b525d-b55c-4298-ac90-6d37f486dac2
-- title:
--   Exact first-recurrence QuotientTerm0 data: part 3
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for QuotientTerm0 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 0 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0

namespace MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (23263300686750827374779947751436751583) * X ^ 2 +
    (511661014690923818076740469814742146029595) * X ^ 3 +
    (26352361577489657064721105887905099280666489) * X ^ 4 +
    (-153460917870001655394532858979571836946124951084) * X ^ 5 +
    (21198742033888534447480592807943036394285954885230) * X ^ 6 +
    (181829797086488013426769931480053969227186581334959) * X ^ 7 +
    (-100143240797371318648002880121439297700179960498621026) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (146081298824828842698077091214977197418440403343414926) +
    (140611980953711297102155849348436176748660579367097111021) * X ^ 1 +
    (1200723505986744848814900435124278882492443894048018853132) * X ^ 2 +
    (-82518362344260868942102031988545848395559763919273188373896) * X ^ 3 +
    (-1310188514169955937547457935260318960030146142268403509333945) * X ^ 4 +
    (17180994281678755249090178124012191161024282736796314917719181) * X ^ 5 +
    (509550296025752616892437313281583991064255936752237787555097995) * X ^ 6 +
    (-499734093992074670841423226709890740393647396661105231937557048) * X ^ 7 +
    (-94061999620568742033873901262669893382128209362744645796801052135) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-406302957642650002217149093462198834178688329080185840477193841199) +
    (10671633329543771976062247162472982122447747401397374887400862577858) * X ^ 1 +
    (77612403915719727416690690196855508424640941167484337860923706929286) * X ^ 2 +
    (-753464895603205468989581940052406717335522348283230721134406634255451) * X ^ 3 +
    (-8759021479483736323932294093100885332527595358861603519714760753002905) * X ^ 4 +
    (43639788320105296004709346010683177824752999008370759665143463291197096) * X ^ 5 +
    (624116495351718406960320769535921663542382913237613001336049251837332630) * X ^ 6 +
    (-1772083940788942262417978640351341928020556743129633253755588113634704172) * X ^ 7 +
    (-36468055676464061565886626502248965241339082935195982312403742388079148085) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (73850138466582618578689127865540806590072333167294592199163000876926241366) +
    (1668675311735206914299728486773742440909133502807654327333591618383364251597) * X ^ 1 +
    (-2938787180931835510497801054275291031671344048914205598204905462629785135689) * X ^ 2 +
    (-64693420285129924840130852924432758442139555316262244093331741149254836834170) * X ^ 3 +
    ((1 * 10 ^ 77 +
      26384379954610144717187985731923777412139562263843846447078392112750200204143)) * X ^ 4 +
    ((21 * 10 ^ 77 +
      01061885028912731329637169976929498590865596656239782125611934854148783080345)) * X ^ 5 +
    -((51 * 10 ^ 77 +
      74896821735415919624863684188074273394766536452138646818418953250559532353737)) * X ^ 6 +
    -((571 * 10 ^ 77 +
      02875661694364858928576600270872685130785226413489950806034866466581319862359)) * X ^ 7 +
    ((1869 * 10 ^ 77 +
      45850129575992200809453914502327168284467399696480049626038512380311114002360)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    ((12695 * 10 ^ 77 +
      44548232516836334976960148805087934431286170552094016865336380246272019393566)) +
    -((57255 * 10 ^ 77 +
      23386424685652163817378674345225500561678522844384033288053507531890017898246)) * X ^ 1 +
    -((217376 * 10 ^ 77 +
      02091071721394017836359864202586565118258536307660270225824902161751981668006)) * X ^ 2 +
    ((1449860 * 10 ^ 77 +
      26149833111561729686367297036966754605658723058126706471619145067985147099174)) * X ^ 3 +
    ((2399543 * 10 ^ 77 +
      82396608173287100095636025960329428185848286513214206937087223638571953182917)) * X ^ 4 +
    -((29885057 * 10 ^ 77 +
      07753151066596951679773275264955680496152790442611812410874419474541394715298)) * X ^ 5 +
    ((950581 * 10 ^ 77 +
      40534942289395271333623963855003182257462319048018300466800346755854550897762)) * X ^ 6 +
    ((486251534 * 10 ^ 77 +
      64138294965664302413341622846488626484896444428715409993142451165859058321497)) * X ^ 7 +
    -((771012949 * 10 ^ 77 +
      01277254346727391883296297059439729206207850563688198791962637613088489182714)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    -((5829893436 * 10 ^ 77 +
      98730444467831734084808088268236359479361128829931379767905122888051656119384)) +
    ((20422577438 * 10 ^ 77 +
      83557333209507773678959269231560045453226152361200490140886357798601111483123)) * X ^ 1 +
    ((40396491601 * 10 ^ 77 +
      17344166363489332402622223998388597641482940336291536641180530586417202252976)) * X ^ 2 +
    -((324976289304 * 10 ^ 77 +
      01742714374031170732455797742597712965143439350007376586442802630222528413697)) * X ^ 3 +
    ((131963532487 * 10 ^ 77 +
      19984190366606407038463853904114623054897938676382557164307464179690155496411)) * X ^ 4 +
    ((3352494155952 * 10 ^ 77 +
      62370022706151700933525865033522171383408562961137769600601154147775712589316)) * X ^ 5 +
    -((8006433019436 * 10 ^ 77 +
      31116906125523697890763817522137725626263973743099359970952198470983700194360)) * X ^ 6 +
    -((17196148945136 * 10 ^ 77 +
      12710967590720049953062863727331562107889009339611353319139485525196299771298)) * X ^ 7 +
    ((111499290810980 * 10 ^ 77 +
      14957975242836345253313900415300179445904637833082573045981710820806070487386)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((83855277500536 * 10 ^ 77 +
      92334728575443614578568498289546123781554263850138123038246480230794299554712)) +
    -((762313076963080 * 10 ^ 77 +
      50783778037000785362581580630516079072538611169678959865891588123804512207476)) * X ^ 1 +
    ((2371507684738974 * 10 ^ 77 +
      47543397215996536497410622908443711788463535580357864119033328684446309934930)) * X ^ 2 +
    ((383927532522196 * 10 ^ 77 +
      40704585927881229846584316386773013259784664479401096548890049890161252066908)) * X ^ 3 +
    -((17824836282459800 * 10 ^ 77 +
      14793743185999928788198559775508996383780886304371753989108338942251964048844)) * X ^ 4 +
    ((39267922606494204 * 10 ^ 77 +
      27276055469013983207270262228454743011474236882130856998362867245348527891668)) * X ^ 5 +
    ((19199697533342822 * 10 ^ 77 +
      89392212655664263303278909927312128535343536919592349933851872466996167822270)) * X ^ 6 +
    -((278743542807535434 * 10 ^ 77 +
      14362483347349032712521392325991012876609811444486657671938302345542121495152)) * X ^ 7 +
    ((569691398002946818 * 10 ^ 77 +
      14685234592738912569933917368667741045459642374637615334215285343690822845413)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((49156278391686922 * 10 ^ 77 +
      34163420316581156241407546973246468777761778294706150277645408302729770161566)) +
    -((2851107952009638937 * 10 ^ 77 +
      41006496015959206458240731270460605699803180084143186791232182839659971972802)) * X ^ 1 +
    ((6751425996108625631 * 10 ^ 77 +
      99246261532974346226129381404981308150280646347690210061114121596610696704990)) * X ^ 2 +
    -((4798972080573227065 * 10 ^ 77 +
      65924974301623890487494691452426475327684575486667756480378822127661709050674)) * X ^ 3 +
    -((13621474300846856527 * 10 ^ 77 +
      12271634018827659344662996572384901375171989804359885291112909079558412776576)) * X ^ 4 +
    ((48654641473485647166 * 10 ^ 77 +
      61884512242899354696586600229356960269755810748772215696035714196029999979660)) * X ^ 5 +
    -((71693215353110819067 * 10 ^ 77 +
      26491170212143687974945651619796441324213350449109748953467198032755037355156)) * X ^ 6 +
    ((29651444787949949066 * 10 ^ 77 +
      60222220127369483391176890289908921336525111942158520011763814261516329828406)) * X ^ 7 +
    ((107678399650799841341 * 10 ^ 77 +
      98551875785439793193937806182879827789629053162593547069196036035430061415863)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((284437202930638335478 * 10 ^ 77 +
      32317412707124570150769541168632057335089814933651477708282698909364577634559)) +
    ((354913116237553557623 * 10 ^ 77 +
      92764424537109229571028128538135909623052948194127744011640504765621611386984)) * X ^ 1 +
    -((186190904770512812406 * 10 ^ 77 +
      05254468519711595063379474731548527637443520310933661418101852495797470614030)) * X ^ 2 +
    -((198838109394189475658 * 10 ^ 77 +
      64197176642778280587380949850779399045126672513073936607434506534200533089293)) * X ^ 3 +
    ((586689563168884705324 * 10 ^ 77 +
      40553324420688211941359649533250452205474154734543586529694241302126820708107)) * X ^ 4 +
    -((720372167804589575420 * 10 ^ 77 +
      41999185852975238167722008208355409612006857469754542897608565238496664176133)) * X ^ 5 +
    ((513654699556616838063 * 10 ^ 77 +
      01124138283416180111737103219431924994177323931942008829772984803608353192801)) * X ^ 6 +
    -((124890231087794675966 * 10 ^ 77 +
      30415454067658530628972116256108136162202406797451218968961987378344166939974)) * X ^ 7 +
    -((186066084786297741269 * 10 ^ 77 +
      73888867047075815550437783463272021927738069819868061842477355209131726348463)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((273324120115789726946 * 10 ^ 77 +
      33723110932768803464310336335907413369450355781354664292435303435641723278916)) +
    -((187152474461780199242 * 10 ^ 77 +
      82128890611062008648609494533308524807765753152539276575521723635805606059443)) * X ^ 1 +
    ((74616753675719226341 * 10 ^ 77 +
      74633440152717848506330420912791648253528695774769340206068740471832634724676)) * X ^ 2 +
    -((31584693923966612512 * 10 ^ 77 +
      99234130237784046284409801103229821521512796679037994086444847615810149066888)) * X ^ 3 +
    ((49892745272960673598 * 10 ^ 77 +
      73258712334651544064998730763447337227906934869248411390848070081569456930812)) * X ^ 4 +
    -((71936440731857898089 * 10 ^ 77 +
      21681637678774447050462098388311443168835220309623180338418962263196045694572)) * X ^ 5 +
    ((63133167730487449469 * 10 ^ 77 +
      55924582665145871141156808962276852243289333952907687732380939066922900326339)) * X ^ 6 +
    -((31732473872481619041 * 10 ^ 77 +
      37759209972301058849697273890082059000706006668491358714330081140327070907593)) * X ^ 7 +
    ((2606840824237953248 * 10 ^ 77 +
      74880470540572055016736992717643282745842468068717236102019370996774436996419)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    ((10561268926647858455 * 10 ^ 77 +
      83618311709949048017613365199827912193206167455685149886191508708236099441282)) +
    -((10327136975128041212 * 10 ^ 77 +
      99570233960537699657068168732029663077687776431105073192243632806687592598049)) * X ^ 1 +
    ((5371951697291262195 * 10 ^ 77 +
      21219339773752813768856519252850392660155336745920566288592701357143097108128)) * X ^ 2 +
    -((1494934975751418825 * 10 ^ 77 +
      68807583589295434442484921887495589681242932430895317366454634321138289300008)) * X ^ 3 +
    -((76865792931552670 * 10 ^ 77 +
      45035809979781930427193227811925394507582493932297150447655994980293765684535)) * X ^ 4 +
    ((297169205471788960 * 10 ^ 77 +
      69986533772738291388112710822456743008948088555700006199976122040695975228925)) * X ^ 5 +
    -((149822059068843025 * 10 ^ 77 +
      09276588592475358816988506455865756779732296899549155283035851877704394912371)) * X ^ 6 +
    ((37133738427994174 * 10 ^ 77 +
      45685161102280073078557950243234141407173354126894236053985006128494450633061)) * X ^ 7 +
    -((957940511922220 * 10 ^ 77 +
      26309448557423854874069626895403905500223969061531098866653795928450108542043)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    -((2781163997790154 * 10 ^ 77 +
      52672987054575451031346862849115405581197424857408008719119941384843467138245)) +
    ((999662851241923 * 10 ^ 77 +
      33192268347351477245360843958704460798518440332530163512340219135268296956178)) * X ^ 1 +
    -((124301709054619 * 10 ^ 77 +
      65651589870033295495560117464831113578189542596754186856382400327117503728674)) * X ^ 2 +
    -((18551194631491 * 10 ^ 77 +
      52485998544112007101308176547681429467851800998995209881251966624428438599924)) * X ^ 3 +
    ((8601872093822 * 10 ^ 77 +
      17904565915346017792293693234650193601953735089480019463168247680392480637353)) * X ^ 4 +
    -((658183886927 * 10 ^ 77 +
      03395000535950132753543183324506015571378146800261238852313651895773184752987)) * X ^ 5 +
    -((180906550532 * 10 ^ 77 +
      01262411577734736036819455955464189888983518365883979454110105677563402610008)) * X ^ 6 +
    ((28343146070 * 10 ^ 77 +
      39060156204477908466920778438287094760764811438649286076397267330311487855434)) * X ^ 7 +
    ((4388129552 * 10 ^ 77 +
      31258720283143783981853650121917370617935186997313217242259377825819708453540)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    -((963374355 * 10 ^ 77 +
      46010840165819904676546533487185075268370635701781213006894922826546854074116)) +
    -((93198690 * 10 ^ 77 +
      82214937940513837286764591627406392877694686998479858676551856622740611938039)) * X ^ 1 +
    ((24405759 * 10 ^ 77 +
      19264225501587390431558540819274196732687236162557949801446348611607345949934)) * X ^ 2 +
    ((1412607 * 10 ^ 77 +
      51740304679071638391066706757103030195273441835113839415707913885185077657867)) * X ^ 3 +
    -((342195 * 10 ^ 77 +
      30474056851368131849945250259548752398925989850633590410647321442327396967047)) * X ^ 4 +
    -((23071 * 10 ^ 77 +
      03747197943109556568454941802316872503131160496203702140329059156652007988246)) * X ^ 5 +
    ((1975 * 10 ^ 77 +
      72942000678772727024813741283777463277406568645369818873098910937276006282396)) * X ^ 6 +
    ((263 * 10 ^ 77 +
      26708588811543226886144445925443242472457615812832430151649469076548141777085)) * X ^ 7 +
    ((11 * 10 ^ 77 +
      30168587095058728794977354320051960906160103109736742137788237690628070827209)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    (23460820915769096186869036609799488129333753038692711306713615294021438590841) +
    (247982070620219148521327771729438382995341424676330479165155824220002135119) * X ^ 1 +
    (1265367622493494220355116090800522230878124270868941813109017372597155897) * X ^ 2 +
    (2361189741361044868954662921109215115666736598933658429405141155389487) * X ^ 3 +
    (-2264711480552482230590597746927070795496810922563127815995468546892) * X ^ 4 +
    (-11220709989797329607292320604813352622665383777296256461374979698) * X ^ 5 +
    (-7598401799353868885604938561595979356572682557695957055351923) * X ^ 6 +
    (-836031378252263893200126451402082936448021876194773696070) * X ^ 7 +
    (-5753790114424529156851959153126156044197379447210807) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3Band17 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 153 * (
    (-85383847357422223311455044221990481632559458)
  )

/-- Internal datum. -/ def recurrence1QuotientTerm0Row3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band3 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band4 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band5 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band6 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band7 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band8 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band9 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band10 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band11 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band12 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band13 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band14 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band15 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band16 +
  MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band17







































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band10
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band11
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band12
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band13
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band14
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band15
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band16
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band17
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band3
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band4
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band5
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band6
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band7
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band8
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row3Band9


