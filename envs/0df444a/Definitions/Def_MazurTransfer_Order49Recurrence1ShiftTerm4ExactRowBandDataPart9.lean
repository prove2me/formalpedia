-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart9
-- name    : MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart9
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:59:23.360112+00:00
-- url     : https://prove2.me/theorems/97849c9f-e9ea-40d5-8d9b-5648b1a31b7a
-- title:
--   Exact first-recurrence ShiftTerm4 data: part 9
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
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart4
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















































































































































































































































































 def recurrence1ShiftTerm4Row9Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    (4791337144615996697328395164961296815775680) * X ^ 1 +
    (-11578474327422726632577455993474332876585843556) * X ^ 2 +
    (-26928012360703221624166232071298218353025784940344) * X ^ 3 +
    (9122428975480633418375510908576230156913384802333740) * X ^ 4 +
    (115382639688493037123819843999507029761676682608970561) * X ^ 5 +
    (-89489317173079313518572784372435954303427986048421882209) * X ^ 6 +
    (498115052110887561877383748242846781701430491230014920335) * X ^ 7 +
    (150954603086133329123040276214718349458889291156612628511160) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    (610539547636582780078869774743726635069442618944811580206194) +
    (-94725514517764029276631515664224108943975370677838749329565350) * X ^ 1 +
    (-1156588219968479008336863524060764641145189164622988162834417322) * X ^ 2 +
    (25807176467853505385323386485447427444061987079110241775286073807) * X ^ 3 +
    (427034523504784768741943136122321937722579480075882095398919988217) * X ^ 4 +
    (-1528366704365820288206078304380243337631331296730519063469193045212) * X ^ 5 +
    (-96217855495180195604350084695765061806528120357695896395558080045047) * X ^ 6 +
    (5347301294282854447793040813748683202667413940597694336507236134952) * X ^ 7 +
    (8112157994696336112147622522172905329077368208983063987244547072959022) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    (51868111746644469435869137580688146226120196184166317663353529430662907) +
    (-737499204347067213049140470043765019435115375063153647468545022929078130) * X ^ 1 +
    (-3674875869186484816707801795415891739137301006578756744916927544942840689) * X ^ 2 +
    (28465965725288405999021387451840857770736441410222896361782922553825574394) * X ^ 3 +
    (300827732840845772831450153140560410574879363089871193259728286378005150464) * X ^ 4 +
    (-1401066681073403177881083604466720356900206838264850214269547163775036080354) * X ^ 5 +
    (-12442133277094764360277394484581131315929823116292869512264909128843752607842) * X ^ 6 +
    (43263258834392238066258384942718116449621398226756344259216262043188821961028) * X ^ 7 +
    ((4 * 10 ^ 77 +
      70195407805603403240384262106755245462596921585185132311817372043917657660008)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    -((15 * 10 ^ 77 +
      51648447144390798790329926105006399191610410474619494196522949510936131767460)) +
    -((128 * 10 ^ 77 +
      83314896275799254641516537980156666287566107355438866094684150850144819102618)) * X ^ 1 +
    ((482 * 10 ^ 77 +
      70058933290234468198999262446700612660403502833128757936003616373715333077341)) * X ^ 2 +
    ((2834 * 10 ^ 77 +
      72701704631302172988136852372111988610732016079877707006859533059474868938253)) * X ^ 3 +
    -((13813 * 10 ^ 77 +
      43126923198080937579432296832655788173949937808295408504878593901286151664986)) * X ^ 4 +
    -((44121 * 10 ^ 77 +
      75362316116872551937932351889833743625200001783347365774114271473063234676637)) * X ^ 5 +
    ((327195 * 10 ^ 77 +
      42900284229704282576481927985282577315944400803011763499005214704074283032451)) * X ^ 6 +
    ((340185 * 10 ^ 77 +
      94994117993883653816173628875190208247273584330942804274153138940050641163422)) * X ^ 7 +
    -((6105748 * 10 ^ 77 +
      21783665177197941733896746473217846836684057656284436599104749982793987952182)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    ((4826803 * 10 ^ 77 +
      45322253075411329220026934464249461167772004708940025857697862234835017895009)) +
    ((82431097 * 10 ^ 77 +
      36810367584743753819956518576622730841740347460095843837215892488119833756772)) * X ^ 1 +
    -((223306046 * 10 ^ 77 +
      00688392569985068345255233478193606658133163812873675101767316619018169929604)) * X ^ 2 +
    -((639696364 * 10 ^ 77 +
      26560730443178473026441243292807697133295971391700189615869022628084043210483)) * X ^ 3 +
    ((4078020739 * 10 ^ 77 +
      12095153342962195997869886925054280472347122360528847510882742188120425323228)) * X ^ 4 +
    -((1324350467 * 10 ^ 77 +
      05781623157460597927090394331683601859887552921830543162017295781358450194893)) * X ^ 5 +
    -((41551575749 * 10 ^ 77 +
      75854630763250990670201633493380618107186005847839365876519870937437179468488)) * X ^ 6 +
    ((108198883316 * 10 ^ 77 +
      48469720510090593688514625320939164353088618646581133266977985687209298833019)) * X ^ 7 +
    ((148122490990 * 10 ^ 77 +
      08692438252903264028187362058375634568587185911187092067403538923947297647556)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    -((1333461838017 * 10 ^ 77 +
      67723249979677764317339318547074061821560728102706943136733900485364869569236)) +
    ((1981589711440 * 10 ^ 77 +
      87023097055229845525336616899908682922567786174081449889859644945840750903062)) * X ^ 1 +
    ((5739616971873 * 10 ^ 77 +
      30429760827189704293392255186182378633695455349743830454049962409387210009666)) * X ^ 2 +
    -((29204490978642 * 10 ^ 77 +
      15889872398222567817391190091976870584170583220773251949909716184046584575085)) * X ^ 3 +
    ((34040256573690 * 10 ^ 77 +
      17623897120555261878376298985722938532794552569587678588153536054513895415076)) * X ^ 4 +
    ((103340463003782 * 10 ^ 77 +
      57822504966992640290835905769419174229791076512053576350396721052834360752987)) * X ^ 5 +
    -((474863639723808 * 10 ^ 77 +
      38630656885969928900929502146662126864363467075248140590459258858280408540573)) * X ^ 6 +
    ((653168096292012 * 10 ^ 77 +
      21610799656976453632905884754284938315961707404944523686201716385829791085259)) * X ^ 7 +
    ((782568601605314 * 10 ^ 77 +
      00638706475170273686570318702128487559891715828594528658341662536892537333385)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    -((5228399713920716 * 10 ^ 77 +
      39057999679590298240591965264229025830817789822934812329144362072672920157548)) +
    ((10239766583565634 * 10 ^ 77 +
      03173577952890695275250168187373871999713815738951055038749880754259004696636)) * X ^ 1 +
    -((5401782900713743 * 10 ^ 77 +
      26763354929387330697362205019840705813360774302943398776492642240607203616273)) * X ^ 2 +
    -((24157406846047160 * 10 ^ 77 +
      02259364265102043105288008709735429413636406719169138073565441785731417080886)) * X ^ 3 +
    ((80351686314737146 * 10 ^ 77 +
      79919408638693825104449021819657006658636442210864929860568664412361086347545)) * X ^ 4 +
    -((130219417523829971 * 10 ^ 77 +
      28665559436286581689519478476107369142976514043293284156517282793482268046946)) * X ^ 5 +
    ((107076811221492466 * 10 ^ 77 +
      37745791125411227942117658977035452598469082554427471025147577415806955975506)) * X ^ 6 +
    ((44825685317179355 * 10 ^ 77 +
      95736731181141311142804705099216133807265151998942787360578799731012302934163)) * X ^ 7 +
    -((304526420259453564 * 10 ^ 77 +
      15623537816400940737231257170581106902674538161883563854321390049022639934305)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    ((550761695426263640 * 10 ^ 77 +
      87258368730050218130385299628190020339182059564404855765117272742317290316043)) +
    -((625696792113621290 * 10 ^ 77 +
      44130877806464863911335264123356117648452049064856448867388697923773852425782)) * X ^ 1 +
    ((451351909907393517 * 10 ^ 77 +
      11724863464666416884171674137157917152814064900259295943277860304363591948806)) * X ^ 2 +
    -((100186687100997758 * 10 ^ 77 +
      46162481461436322997569307193075236931599710694318559416090990404910414440383)) * X ^ 3 +
    -((248898477263108867 * 10 ^ 77 +
      98481513230425351517367820164496283110070814465155733512361759347911191327952)) * X ^ 4 +
    ((434901476227195043 * 10 ^ 77 +
      45352837600783659519750819455481204180644003934138385039685606184127956581876)) * X ^ 5 +
    -((414208641254396267 * 10 ^ 77 +
      55664903798982713141707512400144751817590929786829767400283549680089561761948)) * X ^ 6 +
    ((261738817783066988 * 10 ^ 77 +
      56495667584024409004422069988702853109399092643329357442685371749173787013524)) * X ^ 7 +
    -((93244275652800689 * 10 ^ 77 +
      16631468484922507033862511579909999856403136870009132266641098165837672612877)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band17 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 153 * (
    -((14348280459666946 * 10 ^ 77 +
      80900572886370802582558370953888562667567294645312030595261497290624744870618)) +
    ((49024922357197083 * 10 ^ 77 +
      88803124760219310260052248964621649931446516741294367617899163298750241406424)) * X ^ 1 +
    -((39562772301341031 * 10 ^ 77 +
      53550485310456703000184367539425011390313275522711957382725098116023424249649)) * X ^ 2 +
    ((18953605703264740 * 10 ^ 77 +
      84424654694182327114011339648517263300689701659024432374411568985233035751937)) * X ^ 3 +
    -((4685338003738453 * 10 ^ 77 +
      59433743576307489623143520869713459231911913165368366178536892276986954040382)) * X ^ 4 +
    -((803984844850888 * 10 ^ 77 +
      57856036721492366127924064481012169370240571411144659435382965457435032319494)) * X ^ 5 +
    ((1388980956620382 * 10 ^ 77 +
      27107114261515907264195241624942411213574420596885013264678498816055677365849)) * X ^ 6 +
    -((672233326666655 * 10 ^ 77 +
      06786503302039526010030554786638586403112202949112244544183539391593396434315)) * X ^ 7 +
    ((154213319387239 * 10 ^ 77 +
      11951977385885353906744881301002767550868611809601297419413412361384356361068)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band18 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 162 * (
    ((10754095134989 * 10 ^ 77 +
      40550503262827122061899590094597185126593825356576724155716204276505703249152)) +
    -((21261305676929 * 10 ^ 77 +
      35448819621987217994303544726013213553967560312803214450997656310806766505055)) * X ^ 1 +
    ((6998751091955 * 10 ^ 77 +
      53235394149678066175489096827700933471498432067498620988508950004700824933149)) * X ^ 2 +
    -((588015202068 * 10 ^ 77 +
      66050966701771637659049926065246003915596507187876926942777851934774114154233)) * X ^ 3 +
    -((326188058275 * 10 ^ 77 +
      69888887193263575706848849762821926475851512464417691050868975940403921695388)) * X ^ 4 +
    ((118778560784 * 10 ^ 77 +
      86529788000240529414090629397090526620046187118184874045840811379862553454479)) * X ^ 5 +
    -((8557295721 * 10 ^ 77 +
      58472922829915821010748220411272204402412171805442503294545931174315113658663)) * X ^ 6 +
    -((3745936905 * 10 ^ 77 +
      72972854966849311110443107478269635169443275511047370569531141389221304631876)) * X ^ 7 +
    ((862832317 * 10 ^ 77 +
      42532472767566454781193106392081833655250731756412810836345245103993476761267)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band19 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 171 * (
    ((21540352 * 10 ^ 77 +
      46904166929977092519998094646638129717845131342064972237223420353210032267318)) +
    -((24133349 * 10 ^ 77 +
      92303577429213884657177559536052157717397641135338628581843879734669290111976)) * X ^ 1 +
    ((679986 * 10 ^ 77 +
      43691437012734895496550941920548898639139247140351435980108824017089966832092)) * X ^ 2 +
    ((416367 * 10 ^ 77 +
      00567683114798628989030168370355131510736529777721613014516715187526760123904)) * X ^ 3 +
    -((6176 * 10 ^ 77 +
      25216870009359535531630318964109365800857841202759505478930917375620794288610)) * X ^ 4 +
    -((5199 * 10 ^ 77 +
      47588820802714034789319689011813230715025563985954180510290092264726305274938)) * X ^ 5 +
    -((228 * 10 ^ 77 +
      62196100881324491419505795901100424478940435939196594224746172578972238017621)) * X ^ 6 +
    ((23 * 10 ^ 77 +
      28020497026838919781461233718006406024073021316446095066653921563879139725860)) * X ^ 7 +
    ((3 * 10 ^ 77 +
      29680693032971927862830115422650463694595054169312356416279620397315382417321)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band20 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 180 * (
    (19233887984145550739274997180731774241719073267310462355285561267169580601485) +
    (682381272990533091262018620368610691151336322671924745653787769657327641800) * X ^ 1 +
    (16189583721949437146384161848495417634684949691674613341150274481776742079) * X ^ 2 +
    (265759413007880754206819839826806467124874554379191506793094599363424885) * X ^ 3 +
    (3043597928260734837291533677301893992638806757414617356430001733086913) * X ^ 4 +
    (24065231554138022461702787091821196791267601054803802337917772162125) * X ^ 5 +
    (126935482028491070797802599620626518898688980412618140333967357015) * X ^ 6 +
    (410666842881082154665118133560838471653722952648372261629396874) * X ^ 7 +
    (619071120598426335139009033510993397733302136958349337622582) * X ^ 8
  )

 def recurrence1ShiftTerm4Row9Band21 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 189 * (
    (-420943580067702723257073621002770312991490574704845054597) +
    (-3124134036354504270149399446363722299546247984105941349) * X ^ 1 +
    (-4360914371558684852139731665372219854505917531849879) * X ^ 2 +
    (-2247639652119206015820010406274428119197395191624) * X ^ 3 +
    (-300729629115739563837555720780437525203366377) * X ^ 4 +
    (-4178229927531772510687575613233324557462) * X ^ 5 +
    (-879584349214275641246695997931326) * X ^ 6
  )

 def recurrence1ShiftTerm4Row9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band9 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band10 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band11 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band12 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band13 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band14 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band15 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band16 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band17 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band18 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band19 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band20 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band21



































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band10
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band11
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band12
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band13
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band14
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band15
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band16
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band17
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band18
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band19
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band20
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band21
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band9


