-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm1ExactRowBandDataPart3
-- name    : MazurTransfer_Order49Recurrence1ShiftTerm1ExactRowBandDataPart3
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:40:21.93074+00:00
-- url     : https://prove2.me/theorems/4c590467-a480-457f-a2d7-f59e042eaf5c
-- title:
--   Exact first-recurrence ShiftTerm1 data: part 3
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for ShiftTerm1 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 1 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0

namespace MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-5716537617376765869030209898778114261) * X ^ 2 +
    (-125692027481840554502634443015385617882822) * X ^ 3 +
    (-5607575066457064904347841626220208264450675) * X ^ 4 +
    (37757387605643411162357260515122603166299483632) * X ^ 5 +
    (-5469387397290924097040438706648840112007253484001) * X ^ 6 +
    (-9448601410204218582675830270432601525804281949318) * X ^ 7 +
    (25013217609035908080450591676452717917313133709193027) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-204358827111057350947882768363292157174131295830822695) +
    (-34772241647329453131543101110639897063250617732250665221) * X ^ 1 +
    (-58501691745927541052945552899866238174133767993501706763) * X ^ 2 +
    (22971835757240017289033235487207415583712140812118915463928) * X ^ 3 +
    (191430916472558100723400860637453212514484561067058569565015) * X ^ 4 +
    (-6785202305124082482822894490955886811295137474775352717319984) * X ^ 5 +
    (-104289638365344875817635846474215883449602413189152421832819402) * X ^ 6 +
    (1023356125830694689081406035873776944080121084147408480824396851) * X ^ 7 +
    (24946087943678995529148287693400778365133278798440445284515484757) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-46760536652213080432263794578302312440270645016424306606084216623) +
    (-3701026406157087294149882532830984844901483875806460972746315848256) * X ^ 1 +
    (-5286050879818156966300176699374047089594626254802096850196757182857) * X ^ 2 +
    (344937847499663404226660432657086245324405344500223090348031124372897) * X ^ 3 +
    (1444863630800199675740765140810275800237683762985159432470593450100911) * X ^ 4 +
    (-25962664221713777028294695219339228595733698580149205422761092620456099) * X ^ 5 +
    (-128354924857996986855415161049662833976210897057235509800379207408643851) * X ^ 6 +
    (1407062721391325854373397006714058815916579894750409124022825746538440004) * X ^ 7 +
    (8844512844030799897552260734626667801610994599707661315485541029569773564) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-69555941279052245961427347236600243501584965242130294199847181177640393560) +
    (-423474978825202499845503115316821947060394127580138954812747311652408145933) * X ^ 1 +
    (2917688974015067947000891424835240813904526545601814501291822818193142803427) * X ^ 2 +
    (16366238119438354912436597663134809838739771992018694752746508184394883758519) * X ^ 3 +
    -((1 * 10 ^ 77 +
      12159225603460065586051433736551990598535232302716572028816923504580689353254)) * X ^ 4 +
    -((4 * 10 ^ 77 +
      92048800541317254954764060132759566626787561082314408187961908051102445850981)) * X ^ 5 +
    ((38 * 10 ^ 77 +
      30498567777344832767523838579771800824993000406322356749750334277422602742262)) * X ^ 6 +
    ((112 * 10 ^ 77 +
      21495721285606046492757656430600441885140270767221369869217825739607607996703)) * X ^ 7 +
    -((1142 * 10 ^ 77 +
      67625645086673352401376380723803757028783164809490654383851432246580216055714)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    -((1653 * 10 ^ 77 +
      16573431207179308077923486234079488387931762362851425337370344869463666298234)) +
    ((29034 * 10 ^ 77 +
      52981595832219461494672966703704150122617847843463162297874556975676814563372)) * X ^ 1 +
    ((422 * 10 ^ 77 +
      95468341351847041720593257340147875437060768901118678645074530609432985295884)) * X ^ 2 +
    -((606660 * 10 ^ 77 +
      00897311811402357612951023391023254442158409207462339813940863731434456201018)) * X ^ 3 +
    ((853616 * 10 ^ 77 +
      63628116643389650486419179546368369608680863425222336371138002892482190144608)) * X ^ 4 +
    ((9939736 * 10 ^ 77 +
      93094832647753243993468752738991069316099642978212550906734357964496850736628)) * X ^ 5 +
    -((30535311 * 10 ^ 77 +
      50683101324490502746699135726552988609834133045830099795296774012470736218280)) * X ^ 6 +
    -((113307979 * 10 ^ 77 +
      77813302218443797214782642017967345580291217375004223965078592543489290123067)) * X ^ 7 +
    ((668151567 * 10 ^ 77 +
      16001540810061133715044840221440957971806928022434925412486664272423195125875)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    ((482402018 * 10 ^ 77 +
      32112436333257062353830918255168024233922963735786959730011151898127095295760)) +
    -((10182233885 * 10 ^ 77 +
      57959441682589605890591518278862473224537893144817144352200922590615307913584)) * X ^ 1 +
    ((12868973285 * 10 ^ 77 +
      69240694419724514939439860197275653093201799770591701772315768999430501773643)) * X ^ 2 +
    ((102305109650 * 10 ^ 77 +
      80181738684860309742179525482515245687051199762970697550488960153560288110051)) * X ^ 3 +
    -((357187071306 * 10 ^ 77 +
      61455089807369774896365192792769465338843673026006560567263432434522974831474)) * X ^ 4 +
    -((419604922031 * 10 ^ 77 +
      68750138406754010782943536020717432136476769587552367607424713950480371634617)) * X ^ 5 +
    ((4704745448053 * 10 ^ 77 +
      91050867498631332380063297114943252408249100106104547983946818416875361486722)) * X ^ 6 +
    -((5876028679800 * 10 ^ 77 +
      69715569422090672640870236566837508603859973991591009969290990480516188388037)) * X ^ 7 +
    -((32466112560629 * 10 ^ 77 +
      29471044375610012326783143515809610556099482775856596079818155625234600946113)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    ((127110073130270 * 10 ^ 77 +
      47212490574446901251251226757381638453903709797806129339871119634668838250170)) +
    -((10120038915710 * 10 ^ 77 +
      36380440431398714804668007962151283683948931425918287457694074506649672391669)) * X ^ 1 +
    -((1026302053076433 * 10 ^ 77 +
      25770551999786446169755920404339808164786563549034467191217838205093683363305)) * X ^ 2 +
    ((2537441526780306 * 10 ^ 77 +
      03972739032460340286110745728464650573426575231780960748768771034265335075710)) * X ^ 3 +
    ((1425138059902345 * 10 ^ 77 +
      94153523058863213419598985657947749829291720220581417313807154653530036947154)) * X ^ 4 +
    -((21326209299948804 * 10 ^ 77 +
      27707267140245420512536364838909337675773023487407569921842983015227588385424)) * X ^ 5 +
    ((44189376568250830 * 10 ^ 77 +
      09285336509774312928873962589417818864907855720330260067171900441180870511833)) * X ^ 6 +
    ((20489908974531112 * 10 ^ 77 +
      80738446667306731218701300052914299217645855880368492147533580838351634230652)) * X ^ 7 +
    -((312040909942492543 * 10 ^ 77 +
      88931184665939626236156964965918118913875743556510560592525301334250640265743)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((698607273659644540 * 10 ^ 77 +
      48678122769043947290197904991036170565607882398068916812096823166647454087222)) +
    -((223725813502657815 * 10 ^ 77 +
      35813757920963296739760027163794608721571565677624370844491751853710352145215)) * X ^ 1 +
    -((2761111422762789115 * 10 ^ 77 +
      91693076658892871509195384580913979234373995960792251230397816656197970197084)) * X ^ 2 +
    ((8272082276104009169 * 10 ^ 77 +
      60934305035800450660526052467734585842058341199514776015157508183730410260454)) * X ^ 3 +
    -((10426973491703216999 * 10 ^ 77 +
      69190804460850276063180375400616255861168112901857233354290104540357197934649)) * X ^ 4 +
    -((3886022306545575155 * 10 ^ 77 +
      78316467897094699340003232817884799257351995781225442497948581292790946804096)) * X ^ 5 +
    ((45870811848643794286 * 10 ^ 77 +
      48557936231326796859623328961199061847960244164561635576159352268626936509031)) * X ^ 6 +
    -((105035823073289614402 * 10 ^ 77 +
      86941373842801897410110702273448668126754739858637675644842804707414110720894)) * X ^ 7 +
    ((135462233155450804135 * 10 ^ 77 +
      45122532589894345870054463810695755276285795092356699920161761417875030856180)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((73344910232090778887 * 10 ^ 77 +
      32158198481833070979122109837742945836296434806161234804368475620858315657356)) +
    -((110075977713605979182 * 10 ^ 77 +
      59531784166202006875368624164853157941497669117540687672516988426684485300794)) * X ^ 1 +
    ((358798735904555287350 * 10 ^ 77 +
      57227427147835600684859005850968183516457639851130411954196318990131480787815)) * X ^ 2 +
    -((542641590404055651573 * 10 ^ 77 +
      95245077357774876356914425067492045545304664653110621063591086866011540442802)) * X ^ 3 +
    ((541780308243256979535 * 10 ^ 77 +
      64919698677634225282900857462302536642244395810402065293984827278616443521482)) * X ^ 4 +
    -((342672124591926022926 * 10 ^ 77 +
      54925231089003022144529604490853460184003341290066011940831374988464978112457)) * X ^ 5 +
    ((56225088660737915575 * 10 ^ 77 +
      04417265462103076922965738411469076800273267611962950699396836104282096236052)) * X ^ 6 +
    ((165279616654898010133 * 10 ^ 77 +
      84845269534444971719494850921509002524899367978276221145832720623313340534838)) * X ^ 7 +
    -((239145245693022543546 * 10 ^ 77 +
      31609742499594147338362521770093803112910785993875812902022211916402553185654)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((193624106107181379157 * 10 ^ 77 +
      84318343121407621771570252032216821671983310462052707491026912403170120644075)) +
    -((115826962393843259503 * 10 ^ 77 +
      19297514694411423166185553281433581643877329200049012265765821100327387452239)) * X ^ 1 +
    ((70109611750880749791 * 10 ^ 77 +
      01048930179842997461524132493852378368114262985015428904312940309260959218518)) * X ^ 2 +
    -((62256413439230026269 * 10 ^ 77 +
      77583033696310829452397160031545668185528166399372142900066912454947674026234)) * X ^ 3 +
    ((63426781756724418842 * 10 ^ 77 +
      08589264363549366497636167187904999337828442124151520492209833210405768625255)) * X ^ 4 +
    -((51342702500862589087 * 10 ^ 77 +
      84554525935541203022072912161068803812349652317757788233568949636317970056036)) * X ^ 5 +
    ((27159005034343652482 * 10 ^ 77 +
      69239955411139466632801996830377218018171258272756699025669899499021211056564)) * X ^ 6 +
    -((4493237676963585494 * 10 ^ 77 +
      04424910652159154253275163192154926745529632191593759071372116852504521222667)) * X ^ 7 +
    -((7286310202288889092 * 10 ^ 77 +
      66217756635777923954972888368100332738570602644435778954181258590482042774251)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    ((8683852389188312763 * 10 ^ 77 +
      68596304342799596105148312828518493100530862949566455349940825466341189362719)) +
    -((5353181121116877160 * 10 ^ 77 +
      40513626060850356218005672337698203344443174397558573086518964407939547741718)) * X ^ 1 +
    ((2007679292600889925 * 10 ^ 77 +
      32705996681458443023917418069302090771505918859194468275906333620934307561726)) * X ^ 2 +
    -((282102080029435792 * 10 ^ 77 +
      05894752871326160741809514120663665486051806677287831804495302033568689132018)) * X ^ 3 +
    -((184306933692275386 * 10 ^ 77 +
      11724494067620729362804094836199568626077396454212466375972133852575469828442)) * X ^ 4 +
    ((152269080443956085 * 10 ^ 77 +
      54097582276240073883421276722881852130064969030302130823241194446581030498702)) * X ^ 5 +
    -((56542714350029757 * 10 ^ 77 +
      86546844725401151132901934370911142123720206573360783384736427645846901313025)) * X ^ 6 +
    ((9957383970764751 * 10 ^ 77 +
      39796850906500107637739486157465300959967177748405495547208825439882270855771)) * X ^ 7 +
    ((1099036641176611 * 10 ^ 77 +
      99013444373711364710950434610240627849926541135351654063969796901093127893574)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    -((1206466694348627 * 10 ^ 77 +
      75220202790027734517947907841418339272396640789931885641479592314859339830977)) +
    ((325180915214545 * 10 ^ 77 +
      72931421911708779403312592019986590764094703930220674932853198852671589019322)) * X ^ 1 +
    -((25614692745553 * 10 ^ 77 +
      48226575561035565302060209414105362698799247553418931344601707155277572434507)) * X ^ 2 +
    -((8748387525160 * 10 ^ 77 +
      49287862056303785426382175345750505493557008563893266490716736141030333657000)) * X ^ 3 +
    ((2641818673224 * 10 ^ 77 +
      42000833611021543269658578301538809077531592340169076751429396109018796707898)) * X ^ 4 +
    -((109485622772 * 10 ^ 77 +
      19870178354139888151235607546456730750127442001124406938016260494554469362283)) * X ^ 5 +
    -((60981958021 * 10 ^ 77 +
      98582907802703534668090153438182192209852585553691281461121992912923820463300)) * X ^ 6 +
    ((6088749918 * 10 ^ 77 +
      76877115760293608045878277087390587392854856691727223350077253247284612005545)) * X ^ 7 +
    ((1589829593 * 10 ^ 77 +
      08951746269653587076425468050086296115846950006294286958162025448189352991894)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    -((230593607 * 10 ^ 77 +
      43061265161872659636138122801189141546459057742421098072546708365050912096566)) +
    -((35484895 * 10 ^ 77 +
      24194724873454973851321880436610315165631031648479655446823885892672250049893)) * X ^ 1 +
    ((6281941 * 10 ^ 77 +
      92334265115730291594502537783221441635481293249721429057969288757030332759214)) * X ^ 2 +
    ((527179 * 10 ^ 77 +
      77478626210102190919168839976915641041273212563674626040671849588345176910666)) * X ^ 3 +
    -((87550 * 10 ^ 77 +
      43222566695045196017289338535415359302410300376041301452886126605657345250622)) * X ^ 4 +
    -((7241 * 10 ^ 77 +
      36633218781909655675225961393673384255671150707797601498734303497660671184671)) * X ^ 5 +
    ((460 * 10 ^ 77 +
      63729765158997225588343672615324564755036784646361413376898478114860477369994)) * X ^ 6 +
    ((70 * 10 ^ 77 +
      30122388326713678654339246374709950986620672817691497373385050665939241292462)) * X ^ 7 +
    ((3 * 10 ^ 77 +
      11345335201316731395133092976167258666560772125803078433861131030127398090655)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    (6555138998898513674349747737194786117622909506382464681639613958132108114046) +
    (69813014710603412909265478354709624225872925272767953082087272409918305744) * X ^ 1 +
    (357822453956880138054010766873620646740021269541080236513261152337652065) * X ^ 2 +
    (670295589249016083114908179648663864804126573137434561571576217382595) * X ^ 3 +
    (-637698435487692016737913617630481152662348447449354292339632774861) * X ^ 4 +
    (-3178206938058996593596834100125590223653544284770213949752500950) * X ^ 5 +
    (-2153884733497526087636903546445342646902410011243229724843048) * X ^ 6 +
    (-237019618883458897034095431680240424737556373715420840142) * X ^ 7 +
    (-1631247385916679346619656656046632902224270504832902) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3Band17 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 153 * (
    (-24207031864135638126121796542282327991743449)
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band3 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band4 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band5 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band6 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band7 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band8 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band9 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band10 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band11 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band12 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band13 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band14 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band15 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band16 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band17







































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band10
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band11
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band12
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band13
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band14
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band15
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band16
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band17
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band4
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band5
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band6
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band7
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band8
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row3Band9


