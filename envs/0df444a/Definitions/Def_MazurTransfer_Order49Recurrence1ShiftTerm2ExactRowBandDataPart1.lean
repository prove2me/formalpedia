-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart1
-- name    : MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart1
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:44:58.789+00:00
-- url     : https://prove2.me/theorems/17f475a3-00dc-4b10-bb2c-4b24e9cb7d8b
-- title:
--   Exact first-recurrence ShiftTerm2 data: part 1
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for ShiftTerm2 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 2 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0

namespace MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

































 def recurrence1ShiftTerm2Row1Band1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (2823013859988627122896) * X ^ 2 +
    (-121781369108110543164652388) * X ^ 3 +
    (-267180664302601141371365548) * X ^ 4 +
    (22556740266702026433169962999420) * X ^ 5 +
    (-2282500617925222773100582491536490) * X ^ 6 +
    (-63550021814237932865917004682217601) * X ^ 7 +
    (7375191772041436274121046629694638523) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (150171186986051703929722311474113547717) +
    (-8316054930073677052404561803514361240832) * X ^ 1 +
    (-262393241991755681350802227914561038262719) * X ^ 2 +
    (3119135607127815370778798231435394072814574) * X ^ 3 +
    (199162015741354743236571305517920055751631875) * X ^ 4 +
    (893570556944024286760430894294699406713097437) * X ^ 5 +
    (-70482627770040898079518817289933655753818851895) * X ^ 6 +
    (-974141644804203556963774672630392950141284062777) * X ^ 7 +
    (10793381598671143129892753672782047053845026769004) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (321214111773953097977725841044829698799028032865226) +
    (72910584078861112531510584150490074800281282870908) * X ^ 1 +
    (-57162118454754998207697583097730609277276078536200158) * X ^ 2 +
    (-350100863326861647406313483494671429903852546550855928) * X ^ 3 +
    (6105169777786323082090048421768607593962061012251882390) * X ^ 4 +
    (72864270055646572148528166309135217558956493185360694211) * X ^ 5 +
    (-369196118270037593559866121496700900385691569466106977503) * X ^ 6 +
    (-8549123063901526994452375678618589839206917269963283284118) * X ^ 7 +
    (5572713825951232679263460428809898098895914580342125775224) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (682111491084126821685809821934674986047244600748685420706677) +
    (1316268955908172796855290525756838378375223831321031353785297) * X ^ 1 +
    (-42744818654862612681804716347088713968473212294083857868466389) * X ^ 2 +
    (-129433958495350271402759722687702594287407062799878511155259161) * X ^ 3 +
    (2003789221655602309972408670459532078052585773265930571504013756) * X ^ 4 +
    (8573104695878831440548956750444065146182980722923151970826019266) * X ^ 5 +
    (-86163816484289521787379531282608423939167399785395040703092095203) * X ^ 6 +
    (-351799490205398464881110383496036768122395873046090706158753566461) * X ^ 7 +
    (3052386815847621661297795309692388076640832873744596346821524973675) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (11722807315215524529685902732964084641715938564568247883410834830157) +
    (-100516327960591071400621117026805524433775032701370507119257162035975) * X ^ 1 +
    (-274953476449002648983262876328785513352213636809387165408009848290648) * X ^ 2 +
    (2859048428053273405366071661820662904763554100528764488450917840030894) * X ^ 3 +
    (4214290696719968871418045439247431750166664184079229301108204001484432) * X ^ 4 +
    (-70031426252756559007188730034225624502984912401179896520682593738099907) * X ^ 5 +
    (-4890396708123249554613657893532303242474902740660417287815485247901010) * X ^ 6 +
    (1395952481847177360909121791173593283667594190691852806972460603340422379) * X ^ 7 +
    (-1950726519442370737118757789854687950425601068177651832299069346783668362) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-21097210070491845686033839853468766024229287624498354366847007637257867826) +
    (67164045522353625939496905793358204643441391715525718901045824051198266970) * X ^ 1 +
    (200246280232066969246278621555682501529569444952217248323942048711027012422) * X ^ 2 +
    (-1331173570042692082363374258850965218111192296707249257567127879237906630995) * X ^ 3 +
    (-57730595181051722170712855323380899863133444526817113251532895697351757736) * X ^ 4 +
    (16785877543633864207763803417031545960438902000264797206284989871909633601221) * X ^ 5 +
    (-34881849732856748064720019546254720763838594056304348441448020895757499629521) * X ^ 6 +
    -((1 * 10 ^ 77 +
      09031899412103797761917799941972451005616420231142573167609650653868175936772)) * X ^ 7 +
    ((6 * 10 ^ 77 +
      07357904432993147320799740015630610443044967981947335558695625590322745483892)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    -((3 * 10 ^ 77 +
      41745518954219318211692111195470717853001967128669934984055625257562241213812)) +
    -((47 * 10 ^ 77 +
      48804013105914262677037228777063259993459880576289503103070915456368930247541)) * X ^ 1 +
    ((144 * 10 ^ 77 +
      14269293771033208847715724799211255164806986945339199156504608332817167197237)) * X ^ 2 +
    ((27 * 10 ^ 77 +
      79886696244594605287332611476954767901740801057656607408279707867272294462927)) * X ^ 3 +
    -((1159 * 10 ^ 77 +
      34496504555742283474243926561880204474026449700131338493017371143047664215083)) * X ^ 4 +
    ((2750 * 10 ^ 77 +
      44083896335660218650461222075124736624419097736368976349799266219370037219079)) * X ^ 5 +
    ((600 * 10 ^ 77 +
      91720230012325041429063469240428942995195924010279310543469303941071065457422)) * X ^ 6 +
    -((18596 * 10 ^ 77 +
      80184224888217256701080600919958192683891361221557138090505986748885830792104)) * X ^ 7 +
    ((45378 * 10 ^ 77 +
      37149108359201826083483354017855892758440524880522673960223905231844235245639)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    -((20069 * 10 ^ 77 +
      51614637434424213397151008564521144070062656831806989196995613929257750311900)) +
    -((172976 * 10 ^ 77 +
      87589576849511680418994173613329657334788368662365619665640446733894068430318)) * X ^ 1 +
    ((553030 * 10 ^ 77 +
      47531170677655702785431914710652255821462018736734160991186587234022940831266)) * X ^ 2 +
    -((736441 * 10 ^ 77 +
      97195549893853487338625179466776974397804783407281017815276100205068077388833)) * X ^ 3 +
    -((199751 * 10 ^ 77 +
      61630241837602472294899634097679466452837701528407879419961975935343844487932)) * X ^ 4 +
    ((3125139 * 10 ^ 77 +
      21025015157550693001888278400397693903748442157420834590015928072600866872099)) * X ^ 5 +
    -((7438823 * 10 ^ 77 +
      43335496415101704124738730472415801591017458724943348846939610588709122997686)) * X ^ 6 +
    ((9944418 * 10 ^ 77 +
      52285303873397819027120428857260638623177395433842201928381583734696492131613)) * X ^ 7 +
    -((5875950 * 10 ^ 77 +
      20717744804593735144511763616740747876947126875592691241102133857587942130340)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((7386598 * 10 ^ 77 +
      99801435167613809553608894466265144032676331529575786207101606295461873879849)) +
    ((26406830 * 10 ^ 77 +
      28211744966342760366731998118225460710328327035348834038360918903914414263103)) * X ^ 1 +
    -((41732159 * 10 ^ 77 +
      08320131032238894750537312615961125933901995039816030849682967822166267036750)) * X ^ 2 +
    ((43455951 * 10 ^ 77 +
      12653781579100654835849552829335270278564401415357147434382582256012327579836)) * X ^ 3 +
    -((28589040 * 10 ^ 77 +
      08508779502438238575604778763765152045433895294913704585703730883815549574643)) * X ^ 4 +
    ((3931344 * 10 ^ 77 +
      84154427411439232995918773407219039897815034345723968517215714434082973051521)) * X ^ 5 +
    ((18379744 * 10 ^ 77 +
      72697709480694715316289084795740812505684555063742851105306149111372419695614)) * X ^ 6 +
    -((28988720 * 10 ^ 77 +
      89398197061769052629672013987703900378433447935203313039081228426654405907151)) * X ^ 7 +
    ((26505675 * 10 ^ 77 +
      65736980611065161482470157479236963196595310908245838798901665033144507659767)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((16396813 * 10 ^ 77 +
      89735773368920599948338505211391207959938778977680401926386995389043187190968)) +
    ((5830429 * 10 ^ 77 +
      13007556779446027276322335553735325706805451652962455810983875666904165624841)) * X ^ 1 +
    ((805369 * 10 ^ 77 +
      15560358199270491233524775118813743347772318881024431937599183246673043320820)) * X ^ 2 +
    -((2998524 * 10 ^ 77 +
      12479062915677828392736070660126095096706947188157587992933231161386672445266)) * X ^ 3 +
    ((2505962 * 10 ^ 77 +
      30817518144399951593784282858184932322022306530486606639437462082885399574724)) * X ^ 4 +
    -((1271637 * 10 ^ 77 +
      36951688676465095490521556379859791186630579906673758593597928491893878983366)) * X ^ 5 +
    ((357969 * 10 ^ 77 +
      40017305143815715500789728392102704636895073967374051884979801132592298991832)) * X ^ 6 +
    ((34078 * 10 ^ 77 +
      17268971719642488041728869389349669552542169269184814666236115770098354160229)) * X ^ 7 +
    -((99877 * 10 ^ 77 +
      02320229313782286338443049400561635727095555818997801952551848039842397525180)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((57583 * 10 ^ 77 +
      07584592075587597755227326881044929746451180134387497199827043980888333488684)) +
    -((16841 * 10 ^ 77 +
      96498430030735170500571850471034676545187072439010083167153112914970936877856)) * X ^ 1 +
    ((188 * 10 ^ 77 +
      59096340847518243647362745215915671371091653112581759874729966154687557304889)) * X ^ 2 +
    ((2280 * 10 ^ 77 +
      07896894126265633269939390275344338108068702281005733433739042725497106289555)) * X ^ 3 +
    -((1066 * 10 ^ 77 +
      44432333819241477706570583600037405241524452524815622581438683957389848128865)) * X ^ 4 +
    ((184 * 10 ^ 77 +
      22877598977613998794293914274417005598705780991636540539056078794201789031767)) * X ^ 5 +
    ((38 * 10 ^ 77 +
      78790821121872090472249578568525114446211336913941556929876049504673573341685)) * X ^ 6 +
    -((29 * 10 ^ 77 +
      60391967468132618069109061476711643919985508258589750229699036029285754623776)) * X ^ 7 +
    ((5 * 10 ^ 77 +
      80346184101410661220765900513662421377488272391795475984706497333931323194013)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    (52591208391987639404125215075802425114674482993480256733415983548161844349047) +
    (-47623063317024191849499271916375964048871300869639843125393393861042320952258) * X ^ 1 +
    (6822329470990126777885849628451923037239110246022322528402763670601875124914) * X ^ 2 +
    (983332784485993931009964652657906006676079442399635707322395039256861961515) * X ^ 3 +
    (-401096413612251397127141181396511613727066853147603114208704528468746934499) * X ^ 4 +
    (13982305871613447789228243786780763951894110269181757630021179536362770834) * X ^ 5 +
    (9542796381898028588326490928515269903288525910377507955340634383355002732) * X ^ 6 +
    (-895589951524882636225688844015898125043022258187853904208180828118882571) * X ^ 7 +
    (-138375303411835069775982634046364004097466485264862214165147628457544068) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (14933624873275040531988872481625474986184969917574845663107965241936449) +
    (1692544050951817370490945528114215754926406357906606332029990524803495) * X ^ 1 +
    (-82851217659256041430733171813723831996726846375237040565214136728119) * X ^ 2 +
    (-15585556149541979124855696541227719691967642036421613822459436575573) * X ^ 3 +
    (-733950882802813856824723996230867053261442899981278876449496132082) * X ^ 4 +
    (-16020854433507362686281978530617369791223111972136634105139349346) * X ^ 5 +
    (-175035774395589043419737165134286668187249537366677054827501538) * X ^ 6 +
    (-917379671814228430352174262272575195771837085528195624192925) * X ^ 7 +
    (-1776989881886587750776593514361454310146563412158588386612) * X ^ 8
  )

 def recurrence1ShiftTerm2Row1Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    (1525910523184218255080912803998609098873903022174434866) +
    (8290622189416241351173444072892416698020236302934380) * X ^ 1 +
    (5841749207491585611820024822766068963980333019177) * X ^ 2 +
    (684598307820246460815299507027279964549228461) * X ^ 3 +
    (5468076192544158973724883565375171318100) * X ^ 4 +
    (173778787702898701719906118068158) * X ^ 5
  )

 def recurrence1ShiftTerm2Row1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band1 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band2 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band3 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band4 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band5 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band6 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band7 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band8 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band9 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band10 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band11 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band12 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band13 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band14









































































































































































































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band1
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band10
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band11
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band12
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band13
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band14
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band2
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band4
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band5
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band6
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band7
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band8
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row1Band9


