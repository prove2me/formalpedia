-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart3
-- name    : MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart3
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:47:30.993509+00:00
-- url     : https://prove2.me/theorems/25b6aad7-3aaf-4368-8b5d-918ae26029fb
-- title:
--   Exact first-recurrence ShiftTerm3 data: part 3
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for ShiftTerm3 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 3 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart1
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

































































































 def recurrence1ShiftTerm3Row3Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (24655426743745991193127295293430006807693) * X ^ 2 +
    (-106064413565266396758398661483208451487025643) * X ^ 3 +
    (7858744825548834355936099807454284271929607307) * X ^ 4 +
    (4081662107597091459363314134707197590432874089438) * X ^ 5 +
    (-412378336465670402183124734967392557091694315251611) * X ^ 6 +
    (13160081278506471061611679530087073346314230671098634) * X ^ 7 +
    (212637332967582006433474736267099816283282041465055578) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-28779466102215543654988521980342685865069811745886371161) +
    (7070923281009336657222808552014157860453527410181015591) * X ^ 1 +
    (22147589321140960090042956749840255287872913934217531515289) * X ^ 2 +
    (53303173850482950155473664269246038642955637978432897726186) * X ^ 3 +
    (-9027545279219749176670223562124008992603852814113226798659471) * X ^ 4 +
    (-29274362553905056984716045525313040311417711342714184823982137) * X ^ 5 +
    (1711410367313218026442459504229833888235943693412264637447865390) * X ^ 6 +
    (16237901155619216580165346857128681586239873197907493474751395514) * X ^ 7 +
    (-325335698240791001385356035235806309873071691655309535152384359277) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-1680188944840211811568842057768915096662481384830709280708493523867) +
    (22735526685554132677433999670825273241861282027897694290979684253489) * X ^ 1 +
    (305406055075412287961818180023480424129602391542313525194850079264046) * X ^ 2 +
    (-2556669434592121085368549976927057339080252505816157936128009265179886) * X ^ 3 +
    (-19514776165851589513196102721811423722857286244820691507341317353488538) * X ^ 4 +
    (132142853186603295282214779050190344951129850681844829367837815291319995) * X ^ 5 +
    (1446545551895386890684513586595279028573905735115797656545426916975905539) * X ^ 6 +
    (-8388790106576010791181459916188043125507774543202972527500542382968639104) * X ^ 7 +
    (-68983707070472182719636765578299705352349265076749233856689371140779510645) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (399453257034700315838254866514971523275458566240329874952606736155772366653) +
    (2849300121277942064169584400359316977633718849329524833595955794880022050739) * X ^ 1 +
    (-17691420606377018040061443887736011810849521385023928353293852302968867192739) * X ^ 2 +
    (-91460286615421020791477309792565505779385338333991383997366634732816685106732) * X ^ 3 +
    ((6 * 10 ^ 77 +
      73863849960924535326146584613803550210646788227870473300703534809936770693851)) * X ^ 4 +
    ((22 * 10 ^ 77 +
      52668162944864435782496750441224528609418860695708647122452262955052278561834)) * X ^ 5 +
    -((219 * 10 ^ 77 +
      20076109059607609157460652004295702816703588931066084954858633322761226587169)) * X ^ 6 +
    -((374 * 10 ^ 77 +
      52583206740322963393261699995074691914371929102946450979336611529761852382622)) * X ^ 7 +
    ((6007 * 10 ^ 77 +
      31049283851378738194920381739453533324965387949358524034347794491820331503941)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    ((1334 * 10 ^ 77 +
      82927717740030132926374414834883081542229939250503177294817262964968759559911)) +
    -((134663 * 10 ^ 77 +
      99390476695748576682665317834596917774816094237484969181405134918885537025303)) * X ^ 1 +
    ((158074 * 10 ^ 77 +
      36915768808143660895525862514919634397012528561773820695796662637669098573118)) * X ^ 2 +
    ((2390375 * 10 ^ 77 +
      30773245861163331702701260021660233984418810119084819629520015344415184250606)) * X ^ 3 +
    -((6481146 * 10 ^ 77 +
      89446936599778451153286557039443800247793209952531696616544423779886933442208)) * X ^ 4 +
    -((30828457 * 10 ^ 77 +
      95437020954039507829101389157144063967141788961243544151295400297279823828566)) * X ^ 5 +
    ((154202500 * 10 ^ 77 +
      88267735340813364247059255460068862607224871866797118738498957504128279912987)) * X ^ 6 +
    ((209888840 * 10 ^ 77 +
      10843475970822893546865228012845181321319084064818943534766791065399935951494)) * X ^ 7 +
    -((2563903937 * 10 ^ 77 +
      78488526481530493563311269314752501145352302508465628415846341920377736242082)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    ((1727340101 * 10 ^ 77 +
      71615679564328938010258763742327381134278289600101231664278087512239775096121)) +
    ((29410238258 * 10 ^ 77 +
      16149739626161466059252655593852884578424946794353535209264842596395388184826)) * X ^ 1 +
    -((76014360476 * 10 ^ 77 +
      85329859137418534496881517783252015736574802249037861846655325586412496411982)) * X ^ 2 +
    -((186322623561 * 10 ^ 77 +
      15653949734278813994757520749729231880359576113937314137711456784551775625068)) * X ^ 3 +
    ((1183806854560 * 10 ^ 77 +
      14725557018142694439961782639926691899466488158440015722862289656855560003825)) * X ^ 4 +
    -((525180253078 * 10 ^ 77 +
      98803425618010183955106700270188520587093473267509213396659600510083537371287)) * X ^ 5 +
    -((10235791558114 * 10 ^ 77 +
      49477318025731596049497549159966257697078976884179668432166271001451345330250)) * X ^ 6 +
    ((26672396936250 * 10 ^ 77 +
      29548646128130570845431485559156868413407165706253043145042070570500953174062)) * X ^ 7 +
    ((29108326166167 * 10 ^ 77 +
      63550598296610105552896764452273573447238962681545147549352521397994152050342)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((280961139430590 * 10 ^ 77 +
      18365698990828370179364445751690052520167119671894071173014644524793721288460)) +
    ((421640824793616 * 10 ^ 77 +
      56703433781995732481255883331482395978710536296979299545474965028198275159306)) * X ^ 1 +
    ((1037819726643936 * 10 ^ 77 +
      67732186179167779920044919785228624166372988961245949615945780840632689086172)) * X ^ 2 +
    -((5334950603371852 * 10 ^ 77 +
      32478555077276037987992610638415662464750214588258613913070783363873866344159)) * X ^ 3 +
    ((6302681157229050 * 10 ^ 77 +
      67964685988329688007687903495753789273980575850587995039431056516363257614017)) * X ^ 4 +
    ((16497705041757535 * 10 ^ 77 +
      53600988999799500092312253073525313681743204180589367031891495190073503637008)) * X ^ 5 +
    -((76606745081243369 * 10 ^ 77 +
      08151302661512354211936876808257625998558488354157263032859366967978318545410)) * X ^ 6 +
    ((106448782943277215 * 10 ^ 77 +
      40102458155443555330518585242488984210024201239425864312361682154160179574944)) * X ^ 7 +
    ((104979655389283714 * 10 ^ 77 +
      68822797755256486315176296073597963651196920650082486105961883476615103462597)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((754328563006963056 * 10 ^ 77 +
      41625147706545589901496774890938706244998666757153143217563323654675136296480)) +
    ((1494779374694805658 * 10 ^ 77 +
      69905461505712620180810123474632599809784291294461341980764235602926538668604)) * X ^ 1 +
    -((906174564937281721 * 10 ^ 77 +
      29802086597049363230808721456866942400386467333910970294142639096546277542890)) * X ^ 2 +
    -((3002752887372526000 * 10 ^ 77 +
      06979146399405553604879749138483857740258265009283716481231187142780586366812)) * X ^ 3 +
    ((10535345525839034816 * 10 ^ 77 +
      05342653119935547313777248896190529253730875584323630372016929279256062902998)) * X ^ 4 +
    -((17547193923958944606 * 10 ^ 77 +
      23602372347717715984724890316928480326905953913021666008145316021094503767284)) * X ^ 5 +
    ((15583500942944341845 * 10 ^ 77 +
      29899805864485997273888857415886563459940318548115615719069508707409410258654)) * X ^ 6 +
    ((2650252114595537517 * 10 ^ 77 +
      64882433412726155101621195841084142708187383904567853855185590101110184785556)) * X ^ 7 +
    -((35176847509666970638 * 10 ^ 77 +
      26824846138538884257896552476893941034256646232355085009359608616721075057875)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((67556208665273859440 * 10 ^ 77 +
      03744338659403208575251404563351973856070904255281833919895252388415900501238)) +
    -((80175853670147272016 * 10 ^ 77 +
      50720863061399533364390781192538212856403764713657109433601391988834092574389)) * X ^ 1 +
    ((62279278488802706101 * 10 ^ 77 +
      21869152072764522973379254318977632340714787587465078127659895978982402411818)) * X ^ 2 +
    -((21142015763832891486 * 10 ^ 77 +
      55593488676740342133401618341170204342014274070321208579669582465679292172508)) * X ^ 3 +
    -((22285709662208111543 * 10 ^ 77 +
      71290196157878685920163911642027288406748485616138310215279763232966181523386)) * X ^ 4 +
    ((47958155543706144923 * 10 ^ 77 +
      42177062238913635345407733411000076035259205785098667581372600958423941693941)) * X ^ 5 +
    -((49200458006333892892 * 10 ^ 77 +
      05951415814579842143828873134585506529881892805969832435098286333493519137778)) * X ^ 6 +
    ((33717109629263980520 * 10 ^ 77 +
      68664962601972947513447268148414049589695959881521973455261868795967649627883)) * X ^ 7 +
    -((14795292574369770572 * 10 ^ 77 +
      00353774628203255585026465121829191984893986697724870083143162455423405280878)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((1755463838568356621 * 10 ^ 77 +
      76679745677481008419752269493194389015704850595113344981386156721103060955775)) +
    ((3434279414403226543 * 10 ^ 77 +
      60451439362947405553470384625287252904173416474248637545822403596762600608484)) * X ^ 1 +
    -((3562198404580218115 * 10 ^ 77 +
      90678871233283822189525528495284132998142908529110878383403129411911146537876)) * X ^ 2 +
    ((2059566649230515007 * 10 ^ 77 +
      96778685663046362967190551958850386613919738457061145729579544710513600368847)) * X ^ 3 +
    -((814322411915336792 * 10 ^ 77 +
      41330433269390646563930976154463995557487189658462355610819033012131311207698)) * X ^ 4 +
    ((214723044032898778 * 10 ^ 77 +
      18057677116840770626773666441512889855027948125859481341848340758022358963471)) * X ^ 5 +
    -((23530510226012164 * 10 ^ 77 +
      81603343197243838887960411666610678609342107236363279307067354389182678620933)) * X ^ 6 +
    -((13321299655631473 * 10 ^ 77 +
      83552511475779141093575196296082001090018911628600918277605638223116993390128)) * X ^ 7 +
    ((12987195048429876 * 10 ^ 77 +
      33314192847577682976903059042985643532787289836792745778441479097865150917563)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    -((7676952043995676 * 10 ^ 77 +
      99629650031658194520851947265667174116877441506936330199441036105611673370902)) +
    ((3322135452064926 * 10 ^ 77 +
      75444566250143424851656737357909218920994613611042072726223666238826779161788)) * X ^ 1 +
    -((902836279539361 * 10 ^ 77 +
      95397487867510073410918747487333982155086442204206860829909491638783440670838)) * X ^ 2 +
    ((45761769393548 * 10 ^ 77 +
      56091586760046219762305944472822050578354064868861250222375486039993208469761)) * X ^ 3 +
    ((78640208421249 * 10 ^ 77 +
      13673724391965589129884227298216384771428428347582713831809724287413328687177)) * X ^ 4 +
    -((34920067051053 * 10 ^ 77 +
      31945033984959786607366904686485550815557472555853277262755229261831713724310)) * X ^ 5 +
    ((5693570242294 * 10 ^ 77 +
      23543016089243980685839194848361218132023317217727405699025379508652369246531)) * X ^ 6 +
    ((567975124917 * 10 ^ 77 +
      26509293015611611429078337970898519464427352011276141245358039367375393986852)) * X ^ 7 +
    -((424316561433 * 10 ^ 77 +
      41717751364197628557167258352756600122127527461828485177046445551738594663301)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    ((57366843050 * 10 ^ 77 +
      48877162103417766053260243341321998479882702112619749734643699512868888525016)) +
    ((6094299160 * 10 ^ 77 +
      19668696890453852822905293225397021725403291677546674900839419661436716539533)) * X ^ 1 +
    -((2415450400 * 10 ^ 77 +
      25006646866602321362897271199996929902173859861399482195179465274556705492609)) * X ^ 2 +
    ((71505598 * 10 ^ 77 +
      36573844940489491489485750374577299683223073056435345032584620345082491807012)) * X ^ 3 +
    ((42754018 * 10 ^ 77 +
      23968876858252305927800153247444183429860773556144517082104251838012289913023)) * X ^ 4 +
    -((2554450 * 10 ^ 77 +
      87120437879361467285001566648172035662796463289926405028667768432446962571482)) * X ^ 5 +
    -((507981 * 10 ^ 77 +
      34186919582805012589963788658968844812570631653557998729051204298719701210154)) * X ^ 6 +
    ((14791 * 10 ^ 77 +
      92020743631073209666764546328745370012654689322083799453088583137634153260700)) * X ^ 7 +
    ((4282 * 10 ^ 77 +
      15545952568442476362524099063113514631553858752756282274161497150561594279884)) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    ((219 * 10 ^ 77 +
      84322018511876803779474233691473045555104024526262884634046689765158772561235)) +
    ((5 * 10 ^ 77 +
      03027336959943930559686929386813074903482280834427529682631991422991496900817)) * X ^ 1 +
    (5682372032987320802744835447190044075852560688551549882550012263647367102744) * X ^ 2 +
    (30704019630144458324821771701383086416127425152934749201166866766971400740) * X ^ 3 +
    (62361146163458521131710999031872900433884034167677295676107526523993659) * X ^ 4 +
    (-45271920521716466380043778531289358884103160392556048506779341477956) * X ^ 5 +
    (-284445366438377098871420118171079552052331275452622696708537291389) * X ^ 6 +
    (-213077049116414745393247464930052475781603291598429330504925749) * X ^ 7 +
    (-27573682535060352356862914495803006200672082495393128896136) * X ^ 8
  )

 def recurrence1ShiftTerm3Row3Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    (-276916008102138012719115726470365754698144659690684768) +
    (-21902267619808197632955779176756605289792717461) * X ^ 1
  )

 def recurrence1ShiftTerm3Row3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band3 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band4 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band5 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band6 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band7 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band8 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band9 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band10 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band11 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band12 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band13 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band14 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band15 +
  MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band16



































































































































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band10
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band11
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band12
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band13
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band14
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band15
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band16
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band4
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band5
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band6
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band7
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band8
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Row3Band9


