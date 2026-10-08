-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart4
-- name    : MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart4
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:01:40.85132+00:00
-- url     : https://prove2.me/theorems/4f4df0f0-b3f4-4594-b035-e5397471ef77
-- title:
--   Exact first-recurrence shift data: part 4
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for ExceptionalTerm5 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The original complete certificate proof timed out after 300 seconds; its actual failed job is retained. This genuinely changed package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original 33 shift-product row and band identities, normalized inner5 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0

namespace MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

















































































































































 def recurrence1ExceptionalTerm5Row4Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-1822089843566529845835520) +
    (348968190190370170651200144) * X ^ 1 +
    (-38565145513546715278845561527064) * X ^ 2 +
    (14819443263524306172167117755961824) * X ^ 3 +
    (-16694296403425400643628046713597779936) * X ^ 4 +
    (4507917008873753470252386383683694898416) * X ^ 5 +
    (-990955413988433770696721905838253580684264) * X ^ 6 +
    (124027746047585543380028416036976885227123636) * X ^ 7 +
    (-11133506234911541011800008871025380838337438292) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (675269852969489875867211266817795544999792296356) +
    (-30193146753404869070963642020369585732047566749352) * X ^ 1 +
    (994512265211686892996527049365014581515842911900652) * X ^ 2 +
    (-23152179596938056280305647406881473372807639260046152) * X ^ 3 +
    (-6949361167461892271444918667866531432080532746141436) * X ^ 4 +
    (45507536818798789738539478008414344493663819347634669772) * X ^ 5 +
    (-3385233725372727428678754184482293275926138512147656342762) * X ^ 6 +
    (158100423077478655733535820464785571990274445874725753907362) * X ^ 7 +
    (-5405878944339211269259250679515975101214405748840099084191864) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (141925763216794230469130088767048423722872292773553718260711564) +
    (-2904074974693639087511634256077019006759421009461342757872245706) * X ^ 1 +
    (45601829354052730390798744666655474274219689029607784055434847616) * X ^ 2 +
    (-503521850191317410749518973566793508537354825647519105976169676670) * X ^ 3 +
    (2237630897594172897359337643177739536787613129468281926644318768074) * X ^ 4 +
    (56275309388040889630103429512675879393706608476227468082343067697918) * X ^ 5 +
    (-1859068261650296520616669641145505358197643418140669494620228074977458) * X ^ 6 +
    (34112707902224505549443559445208387848364616922438790173243748308275882) * X ^ 7 +
    (-478296362428418877406241209520973157708448054184315240165449126678006318) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (5559264904878470803146798420930818248066196063254815517572517119716226746) +
    (-55473019445907287502949337372356893249561779205778480257239403445042638372) * X ^ 1 +
    (484334269198987316927382348033435907351110468162571924331674577068494683530) * X ^ 2 +
    (-3743409554019792519438810008927906032496194217363098558338691193265312846478) * X ^ 3 +
    (25804826522891401273268505729029101945722474610209050918474168664649840162120) * X ^ 4 +
    -((1 * 10 ^ 77 +
      59401786920936216341977876035918960148380973988303769991854330093034464727318)) * X ^ 5 +
    ((8 * 10 ^ 77 +
      84630224780614205878997290270743912243344770242912998143362854230944818000704)) * X ^ 6 +
    -((44 * 10 ^ 77 +
      13347438690581006969057967505607027694360877094579079482356339066936120708776)) * X ^ 7 +
    ((197 * 10 ^ 77 +
      58559708363555035960309484984154627209444740900606779701575961551090393712666)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    -((789 * 10 ^ 77 +
      56351951805146339130119173156439776736778501361892528781284782376310259823702)) +
    ((2782 * 10 ^ 77 +
      11455071902058195318060382940108948350002315986689787341735994419794407081202)) * X ^ 1 +
    -((8414 * 10 ^ 77 +
      23756455534168177282605604023642801082121754230741396691236686704142039147382)) * X ^ 2 +
    ((20418 * 10 ^ 77 +
      50715572560338499616326712572380739938387966305334297986058924094701896296928)) * X ^ 3 +
    -((30931 * 10 ^ 77 +
      76621110203079506649271418655978641093149252450140218881573336344716794531656)) * X ^ 4 +
    -((32270 * 10 ^ 77 +
      37145994544813430069242929741843667688970264778731865790625012458440453613144)) * X ^ 5 +
    ((496625 * 10 ^ 77 +
      99015766465968031136634027451298776727504234699360838662497567240198284203790)) * X ^ 6 +
    -((2517968 * 10 ^ 77 +
      15812942420710755783081313137873373664272556555215088574467049456135140944890)) * X ^ 7 +
    ((9629292 * 10 ^ 77 +
      04950896980862266811144950115953550842834582260178624071345454313943743967550)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((31273622 * 10 ^ 77 +
      93318446671683837857525466733190886598417127495598209963585448134824465681878)) +
    ((87176424 * 10 ^ 77 +
      96316563850232206711057431661680743286380073997821613696118772179163672582494)) * X ^ 1 +
    -((197562116 * 10 ^ 77 +
      13742378198830792346830229972728655700772364901309148115340671641451728538108)) * X ^ 2 +
    ((327673517 * 10 ^ 77 +
      92043747807419053844098945293334391299215962188660065124323006533829822929978)) * X ^ 3 +
    -((417295947 * 10 ^ 77 +
      98738187300133486927053370658939705950202385739137713085883812773200737367020)) * X ^ 4 +
    ((1463642628 * 10 ^ 77 +
      47469989602051278971461236848060147911345732498685464052477827009447139512264)) * X ^ 5 +
    -((9044692487 * 10 ^ 77 +
      57356015137844249757748208898556256473414353948202621184704267390175789666756)) * X ^ 6 +
    ((29068973228 * 10 ^ 77 +
      87053041342977254070478919693718793011761649181252316084463244600400649725772)) * X ^ 7 +
    ((5156190206 * 10 ^ 77 +
      41952613996567939147475620872206560815330690831501714508752546750402641521884)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((466243672529 * 10 ^ 77 +
      90344626025666267587056262169766631493281407985302526599593372905984069493756)) +
    ((1957073830362 * 10 ^ 77 +
      39684504134488184122398064663206634129626671296732513146261559359403371782450)) * X ^ 1 +
    -((1907845133652 * 10 ^ 77 +
      62403213120980835704462811741174838328735630377131699234614034978451328026440)) * X ^ 2 +
    -((18188262951095 * 10 ^ 77 +
      94024329209439789846487367162935117933593384717168603406653585135320678912170)) * X ^ 3 +
    ((103221572846733 * 10 ^ 77 +
      79923177385609998631093423127021055887880098097501882892878889227500100816622)) * X ^ 4 +
    -((219714198717757 * 10 ^ 77 +
      66790415534522156297335244769872503908310857866420621624761310132684215419174)) * X ^ 5 +
    -((282917866467984 * 10 ^ 77 +
      11539318980353596990391086674296533421050768694273657936508670387762247392116)) * X ^ 6 +
    ((3758689887049556 * 10 ^ 77 +
      27510396758349670250201443697127042638299174032731051951240241203831172157888)) * X ^ 7 +
    -((13293116305610625 * 10 ^ 77 +
      40926714689984647748803311118847915351101856771478364168858007017917750655364)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((18418092649219783 * 10 ^ 77 +
      88575593245555878189219090651141189345324495109680766830356274372807390563258)) +
    ((54117913210591467 * 10 ^ 77 +
      67866933240721558099785623090908431381175634329922741605072738713657669137074)) * X ^ 1 +
    -((417094133265953991 * 10 ^ 77 +
      30091547151893332827754989551205067650081041518586154805338654908212661165936)) * X ^ 2 +
    ((1330117106695098806 * 10 ^ 77 +
      24838532534024436909945032099081250208068179589257055196546508198699711067176)) * X ^ 3 +
    -((2122481894815051526 * 10 ^ 77 +
      73009580613805031236921699539909741155475889360791676883909312429545103073278)) * X ^ 4 +
    -((2090054539289985396 * 10 ^ 77 +
      03514735716025442715923994632235952803102804007181574217298574122611347254750)) * X ^ 5 +
    ((26850881458476516724 * 10 ^ 77 +
      02920807356915080227381728730214668722178093198767266637593641650185609648536)) * X ^ 6 +
    -((102575585626195427792 * 10 ^ 77 +
      87013663298320961350646563761464576060452088093376612119529301666613966210666)) * X ^ 7 +
    ((250898499611367418181 * 10 ^ 77 +
      45056077923679582122855289949847865961164476676305514210005416973624808086994)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    -((364072239652222461312 * 10 ^ 77 +
      98028377329138234906730631122916676534887732946882718246194307500811669184822)) +
    -((147872899282868645092 * 10 ^ 77 +
      47264828501146161064062343072717337559824263760740886552832774111275024905806)) * X ^ 1 +
    ((3138775528828436574369 * 10 ^ 77 +
      23432589381920746093296627011788183253899084265448617081058734707952030205272)) * X ^ 2 +
    -((13121262299195738198350 * 10 ^ 77 +
      02631395114782471586775275814569130059670366713896196809518057067926904660750)) * X ^ 3 +
    ((39277849604877298806926 * 10 ^ 77 +
      48911540513920835211773945151738221484936515384651264398605030155610462215108)) * X ^ 4 +
    -((97675941677484820835206 * 10 ^ 77 +
      82780633153183354171959270542363019664250757048778438581859935670365996326040)) * X ^ 5 +
    ((212689658387121849431108 * 10 ^ 77 +
      10774521317770497881018840244296656205594674374725412755803969574950016951962)) * X ^ 6 +
    -((416142404764632143623852 * 10 ^ 77 +
      32584617973299864026190576101989899950364966113846289411173103609854934994494)) * X ^ 7 +
    ((742714687598010511866089 * 10 ^ 77 +
      94238497716351372915641121770124665959682771731396411305292766627253980742364)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    -((1221080565378163383904053 * 10 ^ 77 +
      23671039070926738356125202276819737591092915739665810627937993118908775112880)) +
    ((1862038719922479161108967 * 10 ^ 77 +
      65120796132504478941818057780769850390645865345318091489485903123246918798414)) * X ^ 1 +
    -((2646995101149458569148616 * 10 ^ 77 +
      07924248305390985383140914676019444095555401797070608722626396368072224543194)) * X ^ 2 +
    ((3521462755412797308016955 * 10 ^ 77 +
      80154654332109223719865497336375480350390421676423238482980358998664222177602)) * X ^ 3 +
    -((4397738234345872889131528 * 10 ^ 77 +
      71845023780858262398819099851076987524630125156816793042493795873253551210958)) * X ^ 4 +
    ((5168278036915496237428740 * 10 ^ 77 +
      75229636204653408842118120207276656223287784456465218537562672211871023149170)) * X ^ 5 +
    -((5727339508928683327893191 * 10 ^ 77 +
      53310179796963953369538356570010247755875396136800214638214364957837556616644)) * X ^ 6 +
    ((5994867471249764250010394 * 10 ^ 77 +
      16899914900315259318193100410976483554097657536153772131604078182562935502102)) * X ^ 7 +
    -((5935157636052082839349312 * 10 ^ 77 +
      03584380345049156646329086930048271519644597214873937909148335521047949526656)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    ((5564348321732140441793390 * 10 ^ 77 +
      75403147338330915221084483582231896440314229240601823277690521139629854817634)) +
    -((4944691866083199685730901 * 10 ^ 77 +
      79754822938327332716242853908814898581321719597850601626172428456364201157138)) * X ^ 1 +
    ((4168110279927984158633239 * 10 ^ 77 +
      09602286375561851370829748315657979735415765043460409378653456489739748754246)) * X ^ 2 +
    -((3334802742211374588312782 * 10 ^ 77 +
      00179046391077325480260373502095240906495403257802074586693269416101408072476)) * X ^ 3 +
    ((2533461411343245072002453 * 10 ^ 77 +
      81370556358035594969361815832772090049045569426995931044476822534201476930890)) * X ^ 4 +
    -((1828018952673308914088228 * 10 ^ 77 +
      35399945000354335752630880110015823772044052125651300898566747301921470991860)) * X ^ 5 +
    ((1252865464749063044742763 * 10 ^ 77 +
      76422159448503178676834921502397400462577986580491413084533952362981464121210)) * X ^ 6 +
    -((815539264475393105459255 * 10 ^ 77 +
      57044267107120049400386244079508683246656659609008023016098295946984789898764)) * X ^ 7 +
    ((504061248367518159109250 * 10 ^ 77 +
      76141369031936945819194847057354304818946487294640773843974812177486264444788)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    -((295678998725852264404137 * 10 ^ 77 +
      68482116153156727302233978353032197785331683592111564563524808952078858739602)) +
    ((164503083834852970028232 * 10 ^ 77 +
      47852849641072299334827151084342483081286247546312782212189060966125477708436)) * X ^ 1 +
    -((86731384312467463655560 * 10 ^ 77 +
      47939285825859912822050040243222179142579765726280985604503182360923969404338)) * X ^ 2 +
    ((43288442619245503696921 * 10 ^ 77 +
      92041896901244386769176807841399018929891302111423222030612478880642712911960)) * X ^ 3 +
    -((20427556640480380768301 * 10 ^ 77 +
      07954570852126139129369912381579016630086762877874173570878075391708275045976)) * X ^ 4 +
    ((9100673697457533702789 * 10 ^ 77 +
      86646756951047232752774058692959888127768353959806340184725874692712015174204)) * X ^ 5 +
    -((3821320101470555173012 * 10 ^ 77 +
      29410175076457857493181038526420717039846476405698886051514016895444661235772)) * X ^ 6 +
    ((1509417326577122681284 * 10 ^ 77 +
      10580899883076074215444239216767883517634120428396723260749153130032697429932)) * X ^ 7 +
    -((559671977513836450087 * 10 ^ 77 +
      08611314949149157604860168606062764046160043022954698962524040675498560381476)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    ((194335251416409271593 * 10 ^ 77 +
      64046673053439876224042906805035561182187536474124798004105145702430025066354)) +
    -((63025177882911401249 * 10 ^ 77 +
      45444092828659743779452050669315406328070404021826334825262428419755296460800)) * X ^ 1 +
    ((19034705960494795026 * 10 ^ 77 +
      36607004858024460950919196864212947970364841000295428119954731198865502284472)) * X ^ 2 +
    -((5336214118397439562 * 10 ^ 77 +
      85263131527814424745113367423777055262556697781889367040820516757067977403188)) * X ^ 3 +
    ((1383574339958710923 * 10 ^ 77 +
      14118664125760274867188665214643789665339744007258044602839718177684020717426)) * X ^ 4 +
    -((330445039680591885 * 10 ^ 77 +
      23796266544954581926620436776147509327380329330576143456688772942814409229650)) * X ^ 5 +
    ((72369681915020736 * 10 ^ 77 +
      12725318255720468349319320998352784514219278663483186248284592923307835122716)) * X ^ 6 +
    -((14459637347815788 * 10 ^ 77 +
      07019717626223883625104850373025518071521542563569045048449629937050564996860)) * X ^ 7 +
    ((2620501700585481 * 10 ^ 77 +
      58849444980772143568227249945562145539301435579110076833432962054569322446106)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band17 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 153 * (
    -((427915811864008 * 10 ^ 77 +
      66688543976699217546406113067386296921661722939925730299255164821984104806662)) +
    ((62482152170709 * 10 ^ 77 +
      12076930574211122262351167488560797244070584961417764073155080226388443936148)) * X ^ 1 +
    -((8085459996566 * 10 ^ 77 +
      17633425820934037101221490366500109881719751448754373658094194915879572577806)) * X ^ 2 +
    ((917576468940 * 10 ^ 77 +
      04192309487304953493489341130129213381887057530590944458875533155036586150224)) * X ^ 3 +
    -((90183775703 * 10 ^ 77 +
      55361483159194786659299135074459087225368718020585182104465515012942907396490)) * X ^ 4 +
    ((7561148831 * 10 ^ 77 +
      34079181075146603838208717751238210339080292072388260445600682355608894100446)) * X ^ 5 +
    -((530823223 * 10 ^ 77 +
      43512625539469434122880253309189093939439749477688278224272186056645893810480)) * X ^ 6 +
    ((30488166 * 10 ^ 77 +
      44740268547040142443871593247955517492031513310094754493852897020207078796842)) * X ^ 7 +
    -((1390777 * 10 ^ 77 +
      90751511590196475443826244463348565197041054590462634408708042882705246741294)) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band18 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 162 * (
    ((48463 * 10 ^ 77 +
      03673466646748257601501151421156768735270324506353804775591506691796641803968)) +
    -((1222 * 10 ^ 77 +
      70630015690251231862111157423306504491509481429173454617394545064377071208688)) * X ^ 1 +
    ((20 * 10 ^ 77 +
      60685232821649036758665341269697376916280250993647841450887471417636960238044)) * X ^ 2 +
    (-19966378718147433009248579307722744314817466785370535215722594408945410408096) * X ^ 3 +
    (64620992816245816989944971634676115797704785547993079275482681636410487458) * X ^ 4 +
    (517405652475719001756647309460448932917883346837754106109063571646365994) * X ^ 5 +
    (-4533165553040056816889523203207090771938719670827437641307326575828784) * X ^ 6 +
    (5472004918059527142732071871836214164711014703038119244049168706518) * X ^ 7 +
    (39062517083962330288915834649319539644480143743786828685852741190) * X ^ 8
  )

 def recurrence1ExceptionalTerm5Row4Band19 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 171 * (
    (-135942627355222011075878349107524639901813042059693840962170368) +
    (160269998297796302645444847773658932845992468612180805646698) * X ^ 1 +
    (-73890808702695595508920452232373534731125562651947756410) * X ^ 2 +
    (11678628030957396816216709172225180021758820399468790) * X ^ 3 +
    (-493841686144408590434661464851703547309183504870) * X ^ 4 +
    (3781971301410454846115692547124370291496000) * X ^ 5 +
    (-2696788537294529318795848231602240960) * X ^ 6 +
    (18291155076232605597523991190) * X ^ 7
  )

 def recurrence1ExceptionalTerm5Row4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band4 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band5 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band6 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band7 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band8 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band9 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band10 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band11 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band12 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band13 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band14 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band15 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band16 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band17 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band18 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band19











































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band10
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band11
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band12
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band13
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band14
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band15
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band16
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band17
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band18
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band19
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band4
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band5
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band6
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band7
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band8
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band9


