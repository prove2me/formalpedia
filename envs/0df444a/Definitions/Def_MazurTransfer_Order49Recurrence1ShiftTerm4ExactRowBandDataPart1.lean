-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart1
-- name    : MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart1
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:45:44.70634+00:00
-- url     : https://prove2.me/theorems/d8c2f4c4-5e88-4eb4-8edc-9b3265dc9137
-- title:
--   Exact first-recurrence ShiftTerm4 data: part 1
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for ShiftTerm4 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 4 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
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































 def recurrence1ShiftTerm4Row1Band1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (7364383982579027277120) * X ^ 1 +
    (-18035110003567710256111504) * X ^ 2 +
    (-40816806264844390872313299856) * X ^ 3 +
    (15374972965945621570113734382224) * X ^ 4 +
    (-249962159274712537901182138155332) * X ^ 5 +
    (-152667724590619956976285559353282540) * X ^ 6 +
    (5141561172741179660921741680523314856) * X ^ 7 +
    (300157019973307421820930534417316260226) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-7439773800730354728482075031403013976933) +
    (-343826627133684481194880254892869829103574) * X ^ 1 +
    (2983901997771851426767406096890943701948707) * X ^ 2 +
    (226268275641092028708811027093366631116718668) * X ^ 3 +
    (375999367642867054446851582335342259016931645) * X ^ 4 +
    (-75016410127775366868887923833398395071744430748) * X ^ 5 +
    (-718349138953077698724450107836620049650150765757) * X ^ 6 +
    (13982161649848578925893048665545263883779749498678) * X ^ 7 +
    (240199627143897959649453299256397069821413303919497) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-1111947462186679272015043576896132036228591165446560) +
    (-44317452786848212380832707899296844274495924563911190) * X ^ 1 +
    (-70428607349858212521138359060413157867345031986476538) * X ^ 2 +
    (5215135769372837464390035856206953648112692644464922832) * X ^ 3 +
    (28449989011523397513152978730237052358324130197922142837) * X ^ 4 +
    (-407805425788780252178652318206496373909346821767876796477) * X ^ 5 +
    (-3609094766362712724067225013218226818968898021784943313497) * X ^ 6 +
    (20037562166408803163939672879256497024012082040647012312027) * X ^ 7 +
    (313741836273398054457059008994763823642514732872756856730530) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-843995535925003545447710209267028032389369688618604380384683) +
    (-17193660354768329274557406269640757555438929908217272933407924) * X ^ 1 +
    (11565953056963992791694309272496403947013598594760378211047319) * X ^ 2 +
    (858508909213965739862826149689451449410665765486810431819404877) * X ^ 3 +
    (-332248328575467181574460479252923453684472032219178413879352262) * X ^ 4 +
    (-30871276546470311914612062697346803921877469937809609940107136046) * X ^ 5 +
    (2071455833146616467400215767646154876241541807209483725387590006) * X ^ 6 +
    (1009169892804898574329476424113192055937516879697644944727634548422) * X ^ 7 +
    (-549906000955144411535424262032910726576324233521566183542149943826) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-26523498973415664554584002200367999785148633384345906761744270970300) +
    (32869503228974150543991981066043051685125171832225118008329792839239) * X ^ 1 +
    (585352907484607353149085596009309946908172629801453369457753016729337) * X ^ 2 +
    (-1356248228370374634494570762576043922727626761895776878334124327546151) * X ^ 3 +
    (-10000543455033136515556429243290689464912329186726867374997322674590085) * X ^ 4 +
    (39139430378817612765466796865512361636780917651119880781529089448877597) * X ^ 5 +
    (115379666411092108375559420914693371831047117310923078100063224835800585) * X ^ 6 +
    (-828814970776787807965587759191851278881382857038690581047105732763449668) * X ^ 7 +
    (-322226352204793732985949509845063736602557540628413334723755486111068057) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (12533323894438269966669175580804255465529878964471118593355411721112013180) +
    (-19977126259107466137638227123135612471227299606303810130961214056156159210) * X ^ 1 +
    (-119170802401745098618214285840617781971117852281462526981908344320980168202) * X ^ 2 +
    (490734713981600435433613059592378748834124861059988393026093719338812279360) * X ^ 3 +
    (276592923131619419277485655385681548380615809699611850209441144030672967534) * X ^ 4 +
    (-5840126414354546812369140354465362179813679817714875914503194821843506424880) * X ^ 5 +
    (10685115527686221051634687135561587261693048263335568881542770335026890825749) * X ^ 6 +
    (29843762029560167173631304870872069552304394262721122516464070226030462846287) * X ^ 7 +
    -((1 * 10 ^ 77 +
      66502218010805502411088170947270908482628386710106461923601072005657936907258)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    ((1 * 10 ^ 77 +
      59303367701961959122518611596470350314514115065682848408720480107116644509157)) +
    ((9 * 10 ^ 77 +
      05296566803752427241556533306167730449491817140171045820155958371744699463755)) * X ^ 1 +
    -((34 * 10 ^ 77 +
      51682033739879227654733535980052174762908014749292829679339627790896721086836)) * X ^ 2 +
    ((26 * 10 ^ 77 +
      00157309940558442461482099150871034762853555818570649161122582430122602528193)) * X ^ 3 +
    ((154 * 10 ^ 77 +
      31900969593164389860614455935289920306719666610818960336893431923741263075635)) * X ^ 4 +
    -((556 * 10 ^ 77 +
      84523297680225959023997307294368146193995764828002385001406285426880079289105)) * X ^ 5 +
    ((598 * 10 ^ 77 +
      24162881327337314050709347688531721689571883503941813047180093774346309374664)) * X ^ 6 +
    ((1304 * 10 ^ 77 +
      20656431793113805515259751728153090823299694438498634025648451602498433071490)) * X ^ 7 +
    -((6294 * 10 ^ 77 +
      54520531472116022649669305654441302964029979613568954317825027262010065094918)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    ((10836 * 10 ^ 77 +
      19936161428378709941252746517262548030711772095162480430161100487477923058996)) +
    -((3047 * 10 ^ 77 +
      52379121330784059490757007641286380415356188599299194321841997871202079723670)) * X ^ 1 +
    -((31859 * 10 ^ 77 +
      11330794337243094654955434134094464788693049606590308345804526774289060768188)) * X ^ 2 +
    ((92079 * 10 ^ 77 +
      80867986536790128880813371190209304379652043913340867181227753392797082437499)) * X ^ 3 +
    -((138125 * 10 ^ 77 +
      93548868983313398521444680784799682179678769635182544451564462191486714593192)) * X ^ 4 +
    ((99252 * 10 ^ 77 +
      34789410937493259191230988602204986796784920717416211433273998436770343665360)) * X ^ 5 +
    ((75715 * 10 ^ 77 +
      47684911260630956108735884445873235615045960950803704417345400200008879681899)) * X ^ 6 +
    -((352498 * 10 ^ 77 +
      01571282086295066278734970265310984863998167997676403828260467860934104397343)) * X ^ 7 +
    ((596587 * 10 ^ 77 +
      69091830115175990120784095120610921926825101845082046802128069464852158388441)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((648252 * 10 ^ 77 +
      15692696661790832537718543785072390604077871670498309948860644975246669983348)) +
    ((441926 * 10 ^ 77 +
      51034903002019729710252862274380002042403859719607852288267160471730631918449)) * X ^ 1 +
    -((67772 * 10 ^ 77 +
      14380615112319680685882998587193753034934727275611778689218660385048887416296)) * X ^ 2 +
    -((285351 * 10 ^ 77 +
      26016546260230744523298650588636708053250025266701928507995520548148375954373)) * X ^ 3 +
    ((459759 * 10 ^ 77 +
      15685280031447786716167282494717874423174250434857260733397366326769705590364)) * X ^ 4 +
    -((423048 * 10 ^ 77 +
      49198154832425544533974846429787958628334455839707970327550317474734598782316)) * X ^ 5 +
    ((259649 * 10 ^ 77 +
      01994738033141329183947844899212503919312683617938031382262744262457679502770)) * X ^ 6 +
    -((87891 * 10 ^ 77 +
      43117116782906700793797751160241086821338384621199692721822163582303472121976)) * X ^ 7 +
    -((18154 * 10 ^ 77 +
      45630298910518814821878958130037667259294546161424023724501629170296128363377)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((50347 * 10 ^ 77 +
      36151275743874850282856712951066176456992959388213661817210893806508601047390)) +
    -((39478 * 10 ^ 77 +
      76834356616802175511678587787126267452266953789056546524858460684582672722019)) * X ^ 1 +
    ((18597 * 10 ^ 77 +
      17459880023144952830500689586217637176433910097315220570953994792227292706771)) * X ^ 2 +
    -((4515 * 10 ^ 77 +
      50665898106281863009369285312189868138904777192254153868622067312893194913108)) * X ^ 3 +
    -((806 * 10 ^ 77 +
      55340533076386431242821366334656754982074670681019368410752981332774863062737)) * X ^ 4 +
    ((1349 * 10 ^ 77 +
      27233267146070246583620023138894241128540563580544422310387857162494759972076)) * X ^ 5 +
    -((650 * 10 ^ 77 +
      52868216113457017461523412113671262876894745081360843663214956146485573242965)) * X ^ 6 +
    ((151 * 10 ^ 77 +
      27015405903110930234443832174092909991410322945894116607815352326327526201010)) * X ^ 7 +
    ((8 * 10 ^ 77 +
      15592588130812394039653456734508052830338418368786551039968603800253934139231)) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((19 * 10 ^ 77 +
      57257031353901208466357165946239108898466224689672043548196038452466206457178)) +
    ((6 * 10 ^ 77 +
      64320325756424218274261508086539098843754655665867078061624159608717732784607)) * X ^ 1 +
    (-65341668307889460878801401051981074902573286243827507282972827306840150597474) * X ^ 2 +
    (-26789585795720814040006577014036298612605833435952116681008898625217301415196) * X ^ 3 +
    (10715020282425487197760291653217038855322743202177556207051358179679156495916) * X ^ 4 +
    (-988099325077931036128931536444428556561607709870762567026287648174689593260) * X ^ 5 +
    (-272300113853548270542238309092633714919829798409720621088980541769202375858) * X ^ 6 +
    (74460877237103033834735109051950396835480630244401745828555455545278315330) * X ^ 7 +
    (-616196362008112858162481440690184726338424934784664766895146719978928025) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    (-1658285903734932587924351648594078035327915337059517071333978343541461854) +
    (89147678712403682108405677395165387224490683736074707211861973710473690) * X ^ 1 +
    (21939484522813048883704396639995558472566046157193225661527438204965592) * X ^ 2 +
    (-638081846620373314100111872873029222488221014685555599014200369604217) * X ^ 3 +
    (-201975046856112064585427274997312976937820081537507367214296147288945) * X ^ 4 +
    (-10775216485571398055164632258438059786527594531054946309120983061046) * X ^ 5 +
    (-254382746944850265838768137763826172354971574764253077229444911698) * X ^ 6 +
    (-2962739109578692844566985848091593723263030515289802408990374599) * X ^ 7 +
    (-16597784622358032497984595118795258881013886666590701421709073) * X ^ 8
  )

 def recurrence1ShiftTerm4Row1Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (-35968444312211787223995313570268630207147856270477712833734) +
    (19281689255414347159039357086849134315816359009371843901) * X ^ 1 +
    (159065763722523163037325166871246083333931984880417533) * X ^ 2 +
    (131707993645254199926944630078587373339706179287628) * X ^ 3 +
    (19986200266289718933581076452485299870337259600) * X ^ 4 +
    (281470854963457713709393027781538682351108) * X ^ 5 +
    (59266401202097991148094079066049588) * X ^ 6
  )

 def recurrence1ShiftTerm4Row1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band1 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band2 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band3 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band4 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band5 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band6 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band7 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band8 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band9 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band10 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band11 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band12 +
  MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band13



















































































































































































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band1
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band10
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band11
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band12
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band13
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band2
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band4
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band5
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band6
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band7
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band8
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band9


