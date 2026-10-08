-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
-- name    : MazurTransfer_Order49Recurrence1NormalizedData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T01:49:58.831004+00:00
-- url     : https://prove2.me/theorems/8c41a94e-1c38-4b2e-9a44-206650efe748
-- title:
--   Exact normalized first order-seven recurrence data
-- statement:
--   These are the original fixed rational coefficient polynomials and their finite arithmetic blocks for the first order-seven pseudo-division recurrence. They define data only. The six normalized polynomial identities and the conversion identities from the original coefficients are separate proof obligations.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 source headers and attribution retained. Exact kernel type dependencies of29 original first-recurrence identities select244 pure definitions in four original data modules. Complete Lean AST ranges preserve every original mathematical definition. Every exported value is compared to the original in Lean using only standard axioms. Resource options and compilation suppression commands are removed at exact Lean command ranges. Named downstream consumers: the29 original normalized and conversion identities, the six first-recurrence inner identities, and the full order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1SourceData. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 1 certificate: SourceData

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1Source0Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (1) * X ^ 3 +
    (-77) * X ^ 4 +
    (-1181) * X ^ 5 +
    (741) * X ^ 6 +
    (95279) * X ^ 7 +
    (-772464) * X ^ 8
  )

def recurrence1Source0Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (3222128) +
    (-8636434) * X ^ 1 +
    (15939042) * X ^ 2 +
    (-20695126) * X ^ 3 +
    (18939622) * X ^ 4 +
    (-12491384) * X ^ 5 +
    (7213570) * X ^ 6 +
    (-5733840) * X ^ 7 +
    (5624303) * X ^ 8
  )

def recurrence1Source0Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-4405352) +
    (2405086) * X ^ 1 +
    (-886465) * X ^ 2 +
    (206818) * X ^ 3 +
    (-24787) * X ^ 4 +
    (637) * X ^ 5 +
    (-209) * X ^ 6 +
    (98) * X ^ 7 +
    (-5) * X ^ 8
  )

def recurrence1Source0Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-1)
  )

def recurrence1Source0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Source0Block0 +
  recurrence1Source0Block1 +
  recurrence1Source0Block2 +
  recurrence1Source0Block3

def recurrence1Source1Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (21) * X ^ 3 +
    (406) * X ^ 4 +
    (1589) * X ^ 5 +
    (-93457) * X ^ 6 +
    (708841) * X ^ 7 +
    (-2769417) * X ^ 8
  )

def recurrence1Source1Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (6825462) +
    (-11412394) * X ^ 1 +
    (13386751) * X ^ 2 +
    (-11239305) * X ^ 3 +
    (6871774) * X ^ 4 +
    (-3086608) * X ^ 5 +
    (940373) * X ^ 6 +
    (-65296) * X ^ 7 +
    (-125181) * X ^ 8
  )

def recurrence1Source1Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (67522) +
    (-8743) * X ^ 1 +
    (-3269) * X ^ 2 +
    (959) * X ^ 3 +
    (-14) * X ^ 4 +
    (-14) * X ^ 5
  )

def recurrence1Source1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Source1Block0 +
  recurrence1Source1Block1 +
  recurrence1Source1Block2

def recurrence1Source2Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-91) * X ^ 3 +
    (-2331) * X ^ 4 +
    (38542) * X ^ 5 +
    (-250488) * X ^ 6 +
    (878003) * X ^ 7 +
    (-1917251) * X ^ 8
  )

def recurrence1Source2Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (2824976) +
    (-2915535) * X ^ 1 +
    (2121469) * X ^ 2 +
    (-1083838) * X ^ 3 +
    (410326) * X ^ 4 +
    (-149079) * X ^ 5 +
    (62594) * X ^ 6 +
    (-20265) * X ^ 7 +
    (2884) * X ^ 8
  )

def recurrence1Source2Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (161) +
    (-77) * X ^ 1
  )

def recurrence1Source2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Source2Block0 +
  recurrence1Source2Block1 +
  recurrence1Source2Block2

def recurrence1Source3Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (14) * X ^ 2 +
    (728) * X ^ 3 +
    (-8477) * X ^ 4 +
    (39032) * X ^ 5 +
    (-108654) * X ^ 6 +
    (198100) * X ^ 7 +
    (-242060) * X ^ 8
  )

def recurrence1Source3Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (204596) +
    (-124124) * X ^ 1 +
    (53942) * X ^ 2 +
    (-14567) * X ^ 3 +
    (812) * X ^ 4 +
    (868) * X ^ 5 +
    (-210) * X ^ 6
  )

def recurrence1Source3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Source3Block0 +
  recurrence1Source3Block1

def recurrence1Source4Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-98) * X ^ 2 +
    (707) * X ^ 3 +
    (-1372) * X ^ 4 +
    (-322) * X ^ 5 +
    (2912) * X ^ 6 +
    (-2450) * X ^ 7 +
    (1442) * X ^ 8
  )

def recurrence1Source4Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-1799) +
    (1274) * X ^ 1 +
    (-294) * X ^ 2
  )

def recurrence1Source4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Source4Block0 +
  recurrence1Source4Block1

def recurrence1Source5Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (7) * X ^ 1 +
    (56) * X ^ 2 +
    (-406) * X ^ 3 +
    (994) * X ^ 4 +
    (-1239) * X ^ 5 +
    (791) * X ^ 6 +
    (-203) * X ^ 7
  )

def recurrence1Source5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Source5Block0

def recurrence1Source6Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-14) * X ^ 1 +
    (49) * X ^ 2 +
    (-35) * X ^ 3
  )

def recurrence1Source6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Source6Block0

def recurrence1Source7Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (1)
  )

def recurrence1Source7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Source7Block0

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder2Data. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 1 certificate: Remainder2Data

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1Remainder20Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (1) * X ^ 2 +
    (21998) * X ^ 3 +
    (1213258) * X ^ 4 +
    (-6591719746) * X ^ 5 +
    (887174420015) * X ^ 6 +
    (10898850087779) * X ^ 7 +
    (-4242577921555076) * X ^ 8
  )

def recurrence1Remainder20Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-9044841330557190) +
    (5905879565633563356) * X ^ 1 +
    (73367409398595165996) * X ^ 2 +
    (-3131219520021488355261) * X ^ 3 +
    (-66505908255265167228909) * X ^ 4 +
    (409155522983929358223454) * X ^ 5 +
    (22027542795128115872321226) * X ^ 6 +
    (76735418560623238749227979) * X ^ 7 +
    (-3234018323272692008644959524) * X ^ 8
  )

def recurrence1Remainder20Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-29738389409425638678174724443) +
    (253887039826360477352885637974) * X ^ 1 +
    (3839461295707575052402511711145) * X ^ 2 +
    (-7632953412497286154928754530167) * X ^ 3 +
    (-325902109613993235482591511158062) * X ^ 4 +
    (-54189002951574352392486001446389) * X ^ 5 +
    (17939832588070721406987746062937250) * X ^ 6 +
    (31826313445941491054485986255887620) * X ^ 7 +
    (-849488679231132760490374031074814762) * X ^ 8
  )

def recurrence1Remainder20Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-1614355931044266796217772307414613716) +
    (31358151232828134232489089258528740581) * X ^ 1 +
    (59173772590237271321614902242554864604) * X ^ 2 +
    (-1037909449069702050995790634079279527234) * X ^ 3 +
    (-1165280355746439384243786350455420790049) * X ^ 4 +
    (28927249338570910072158119743920309724861) * X ^ 5 +
    (3724415618239167221623117838218836606730) * X ^ 6 +
    (-681578237840065642926261228656071824770362) * X ^ 7 +
    (762752762879364689572744288733998737444098) * X ^ 8
  )

def recurrence1Remainder20Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (12747758848377365623179496199857217975063094) +
    (-33644919694007791905306165608311761387256527) * X ^ 1 +
    (-170616046135731321807523659719437449607831382) * X ^ 2 +
    (854731750744759183117612048451503577686718350) * X ^ 3 +
    (1070589103141380188990437600705938082237411849) * X ^ 4 +
    (-14533737069505132262481138493185774319227901666) * X ^ 5 +
    (14847492001852093904509154446647689144549047900) * X ^ 6 +
    (155606299034522954166844058198548068896279977537) * X ^ 7 +
    (-519630700961647778633579607877224146206648309539) * X ^ 8
  )

def recurrence1Remainder20Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-598801835612111105880235198090447628712531519493) +
    (6947902940277472273331017092804828544810974028139) * X ^ 1 +
    (-10475530471061913847079100899254638337734396287104) * X ^ 2 +
    (-40332554873310579622123872668669900409407948080662) * X ^ 3 +
    (193107590045649299339279328984668292960892819799483) * X ^ 4 +
    (-149432665535261992857347330551770721950842375691980) * X ^ 5 +
    (-1133497054982079041065679089970365931806088756989147) * X ^ 6 +
    (4040747699608870687257985013647732806121074286902738) * X ^ 7 +
    (-2785848571080064457962537035628974255157624433659535) * X ^ 8
  )

def recurrence1Remainder20Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-18687086537014865119121801645888755694124474167125176) +
    (66681838947911016521021237852219792660730576150126032) * X ^ 1 +
    (-74259866442592643309907716195443028789570438134352762) * X ^ 2 +
    (-147265800657316553789244740368621751889157008294390057) * X ^ 3 +
    (755349943097198560274645640023835200357276309089105499) * X ^ 4 +
    (-1379867726824908573819612208907630171932514084636054614) * X ^ 5 +
    (621725971190563657393235315757192056596706225030493894) * X ^ 6 +
    (3459292504659497610979380743349758433450163007452524369) * X ^ 7 +
    (-11110284307128431035158933978291100334801954980947472146) * X ^ 8
  )

def recurrence1Remainder20Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (18090386868971818456858662029614161681345717082226652170) +
    (-15778242959145104133485300167950379020342628991290237379) * X ^ 1 +
    (-3178960320396938136119349815210378601274709185668604937) * X ^ 2 +
    (36416415138398479956000701682694083607585734323956960547) * X ^ 3 +
    (-68730293687975869875107587708993249866577186534605683258) * X ^ 4 +
    (80288771384155327696477068622320292133380775283507804161) * X ^ 5 +
    (-61687727358641659015289991008485945807169000866643639069) * X ^ 6 +
    (22622649723594544532826141549412266534983169558561402188) * X ^ 7 +
    (14915691153763092973853852477020507767130725417493824916) * X ^ 8
  )

def recurrence1Remainder20Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (-33394678553273738523894447672201797175806248079960824229) +
    (31217689682422219822285482974369168030034942981141275460) * X ^ 1 +
    (-19675967917793710704235343250800850601613615115738019326) * X ^ 2 +
    (10745817826620269598676200057421220998636038861351205476) * X ^ 3 +
    (-8281322558401235238033851106880737444484475822509353739) * X ^ 4 +
    (8874202635339496410647718336739457874613827537931241641) * X ^ 5 +
    (-8171004906960062150958281833795327043585118995535503793) * X ^ 6 +
    (5142430892918680930903256032716510315963633132641078831) * X ^ 7 +
    (-1554480341109496625004429488308674062741406305645410850) * X ^ 8
  )

def recurrence1Remainder20Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    (-736087488191373628403549815668351514898023125492160919) +
    (1332657498309766410093961889457493240678510755788979622) * X ^ 1 +
    (-950964642855568595917937148463566556455742041776139030) * X ^ 2 +
    (408293016549124941092699581346964679441895603795325958) * X ^ 3 +
    (-83054877363276582153572517801866795997624065665320178) * X ^ 4 +
    (-23045195150113390851533850503264632732698437216591192) * X ^ 5 +
    (27180003515099636736288757639539073556892684559618223) * X ^ 6 +
    (-11482509351260787881775076202547517529217615946686081) * X ^ 7 +
    (2403877461037195963346376424656155043888088425166875) * X ^ 8
  )

def recurrence1Remainder20Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    (85446096580397680979268746891364634839534831385470) +
    (-230300761212428877959999864514542636268972701952935) * X ^ 1 +
    (71047281503988594395292188314575685858281974979711) * X ^ 2 +
    (-7242965276005198687250854010145591748681377657456) * X ^ 3 +
    (-1609474925545182656633135617398099675121374668988) * X ^ 4 +
    (594888352697172539251946829237087330057928808919) * X ^ 5 +
    (-35682081868816433525662072854424923464803899505) * X ^ 6 +
    (-13080880038331164717498911381112159427479572402) * X ^ 7 +
    (1682596274192633024084773447547225160481835569) * X ^ 8
  )

def recurrence1Remainder20Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    (329041432510035751706973504730628132940569628) +
    (-59718794864614781855680443009507852961443027) * X ^ 1 +
    (-7173045799197579454731740761038147002347352) * X ^ 2 +
    (1560530508013868545100650132777578578566977) * X ^ 3 +
    (107596482591299095251211202323863114511740) * X ^ 4 +
    (-21835855329074871209439970786676218209063) * X ^ 5 +
    (-1613170450578754187113664875608047773491) * X ^ 6 +
    (121420420245797158958065078024853838771) * X ^ 7 +
    (17117395763730572988598898971842175952) * X ^ 8
  )

def recurrence1Remainder20Block12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    (744894209253773091908300182564263888) +
    (15560161622173073532254368820081712) * X ^ 1 +
    (165026199140154693898992949889670) * X ^ 2 +
    (843753345028747037362040919139) * X ^ 3 +
    (1577196414728952886234267757) * X ^ 4 +
    (-1507245375088838010731695) * X ^ 5 +
    (-7487522096003555795152) * X ^ 6 +
    (-5072148110737246025) * X ^ 7 +
    (-558110085407786) * X ^ 8
  )

def recurrence1Remainder20Block13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (-3841078186) +
    (-57) * X ^ 1
  )

def recurrence1Remainder20 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder20Block0 +
  recurrence1Remainder20Block1 +
  recurrence1Remainder20Block2 +
  recurrence1Remainder20Block3 +
  recurrence1Remainder20Block4 +
  recurrence1Remainder20Block5 +
  recurrence1Remainder20Block6 +
  recurrence1Remainder20Block7 +
  recurrence1Remainder20Block8 +
  recurrence1Remainder20Block9 +
  recurrence1Remainder20Block10 +
  recurrence1Remainder20Block11 +
  recurrence1Remainder20Block12 +
  recurrence1Remainder20Block13

def recurrence1Remainder21Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-23) * X ^ 2 +
    (991446) * X ^ 3 +
    (34314719) * X ^ 4 +
    (-182010007593) * X ^ 5 +
    (12713487257368) * X ^ 6 +
    (809774120213950) * X ^ 7 +
    (-24940064428596179) * X ^ 8
  )

def recurrence1Remainder21Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-1511187499165252688) +
    (-1401006467656754001) * X ^ 1 +
    (1057485838428164119588) * X ^ 2 +
    (14904717066199156916092) * X ^ 3 +
    (-230250439109250632924208) * X ^ 4 +
    (-7159433264249329204390444) * X ^ 5 +
    (-800944141195000428913534) * X ^ 6 +
    (1336715720568965017819040794) * X ^ 7 +
    (9371219754866468327646862794) * X ^ 8
  )

def recurrence1Remainder21Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-152159977597680694262199235725) +
    (-1476675698552842302366816083544) * X ^ 1 +
    (7423831494855042805865550540966) * X ^ 2 +
    (166980362579297990515818353437658) * X ^ 3 +
    (-338050950523730163560503266156439) * X ^ 4 +
    (-10229350116733897326878981007695336) * X ^ 5 +
    (-2125560260375172499905965264154931) * X ^ 6 +
    (563370211501071328312802386841574086) * X ^ 7 +
    (268943619019748947580124367300453358) * X ^ 8
  )

def recurrence1Remainder21Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-22337226396841398490007237712497405760) +
    (-16302087361960395159433645119209771205) * X ^ 1 +
    (782884778513075620609733485006308898812) * X ^ 2 +
    (169100928911810487969607712933238095601) * X ^ 3 +
    (-22434483518242757074625435655352319831718) * X ^ 4 +
    (12149129729855203374463191490851350845219) * X ^ 5 +
    (537688842212710594891401914117782804026329) * X ^ 6 +
    (-866296460575465796670455267867388753669369) * X ^ 7 +
    (-10178800343993652398732960755834833985355521) * X ^ 8
  )

def recurrence1Remainder21Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (30845305703298606992929688144684386050348722) +
    (138143825322861061374501546913615689092833736) * X ^ 1 +
    (-744345593375753309946174316548546440583310611) * X ^ 2 +
    (-895207211253094452398187469388442171570590165) * X ^ 3 +
    (12602628389526258851354891566204867902883476569) * X ^ 4 +
    (-11789716434675680598066479227024573301751833031) * X ^ 5 +
    (-139165872516838418896158854667393896510709872301) * X ^ 6 +
    (432112768142442353814148894616481470942321809786) * X ^ 7 +
    (648401638615966186456668747610539522190161225558) * X ^ 8
  )

def recurrence1Remainder21Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-6037767278326563296666525835768529343305035119745) +
    (7319164040280728673013255566132109193578495146294) * X ^ 1 +
    (39376151809298759682298403303322297574478351376786) * X ^ 2 +
    (-158544148055671054942981428221540990703068279312848) * X ^ 3 +
    (63358724873144633399933389938629023169622069684614) * X ^ 4 +
    (1064558347078202935519998281089920262378412868830515) * X ^ 5 +
    (-3146619741164609779553998395203135504539567542823798) * X ^ 6 +
    (876307759424208137110477158844935261665956234512959) * X ^ 7 +
    (17552225484796966209684620157723463839167888348993832) * X ^ 8
  )

def recurrence1Remainder21Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-51060801395036558645419750914266778279505713183364077) +
    (38708632590349550038909320209836313832035801399688659) * X ^ 1 +
    (156122700235894541215359928419238137620803549708792141) * X ^ 2 +
    (-595906504110546317847580435390630519293736106243862022) * X ^ 3 +
    (908998126415325120637565211799562731984882044711349612) * X ^ 4 +
    (-51871866980317366272367580474309106861221427576714072) * X ^ 5 +
    (-3125222676151354777987688904098109556790764257035467612) * X ^ 6 +
    (8245603275267371716190936967846421293904322573578120047) * X ^ 7 +
    (-11860302118566559246669520438814952811433639321036215419) * X ^ 8
  )

def recurrence1Remainder21Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (8258351480991784408067572220378167800052511981920027684) +
    (6339784595116002229604274733098828450965141109605473566) * X ^ 1 +
    (-28791247917155730095191731668190079515844489164587793391) * X ^ 2 +
    (48304516639352681316629944664412575412448947881980741219) * X ^ 3 +
    (-52531240047776006889528378892265661634330595770235940584) * X ^ 4 +
    (36645672164894523053962831347859804107942099887637523889) * X ^ 5 +
    (-7711495254258528833921041862212817265626987881284362859) * X ^ 6 +
    (-19868974027110136494621511363444536279163445865749406305) * X ^ 7 +
    (34112584794954398266833056348304426407178408948479890064) * X ^ 8
  )

def recurrence1Remainder21Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (-32375243055288744739408246882573607354938322171631554325) +
    (20708736458340767299850218004237134122253863187163857273) * X ^ 1 +
    (-7829781767072193790940614855451749192419440213868793672) * X ^ 2 +
    (-576856191188187954714640719003699400531614494547848943) * X ^ 3 +
    (3555925959456983574221159675035807265379863913865233933) * X ^ 4 +
    (-3108456926656432728504324865398422107582029442310965890) * X ^ 5 +
    (1626590872137609006190680264567211411675349780746126932) * X ^ 6 +
    (-481557911681160080760038815346420927989652033326333172) * X ^ 7 +
    (-27628561411336868244991961003430565766835296129033560) * X ^ 8
  )

def recurrence1Remainder21Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    (122554917084065300320853867687274009809457937145411774) +
    (-73602963982873250007940517693601404642619624498649232) * X ^ 1 +
    (22403057824211929525907520032123867309614792448565037) * X ^ 2 +
    (-677576951413359118440884308755013409422520100772299) * X ^ 3 +
    (-2839128411816168015048852376996962813972555961860067) * X ^ 4 +
    (1387738389012733836035583938650539472586594932267953) * X ^ 5 +
    (-253453885906353008237761915978949606214749541567482) * X ^ 6 +
    (-46006234319931267767611476462716704253784042788995) * X ^ 7 +
    (38405088775242791785444052145651662155661340450784) * X ^ 8
  )

def recurrence1Remainder21Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    (-7861858706611913241008138397025016936982623538323) +
    (-607134815894910500975852149592281370663107412836) * X ^ 1 +
    (623068481933135245171317251061364802624893518330) * X ^ 2 +
    (-93293421963792147238755174843943741047526616373) * X ^ 3 +
    (-12329058152593188306493045475100783041995331638) * X ^ 4 +
    (5339749916684606161901804394069140621433038988) * X ^ 5 +
    (-207268398832040207310409423826418713155088422) * X ^ 6 +
    (-125889998764741537441282873874599122737960653) * X ^ 7 +
    (12289823024352319415238577752859155764127964) * X ^ 8
  )

def recurrence1Remainder21Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    (1821472109026745853271440556631226373021314) +
    (-203715578909439757211547426606478810966882) * X ^ 1 +
    (-22496275929643517102918964098425632497513) * X ^ 2 +
    (1144241126005859139820446988485301202837) * X ^ 3 +
    (210462081499466225006966235727856020684) * X ^ 4 +
    (9870924355153883672137796042767009143) * X ^ 5 +
    (215088728471684776815229998500189364) * X ^ 6 +
    (2347813443240803839127253112182995) * X ^ 7 +
    (12298617856096924713735520959259) * X ^ 8
  )

def recurrence1Remainder21Block12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    (23812113619150826247011739581) +
    (-20468171030108376511660993) * X ^ 1 +
    (-111124234857222285699352) * X ^ 2 +
    (-78293151035390302222) * X ^ 3 +
    (-9175063979244366) * X ^ 4 +
    (-73283682580) * X ^ 5 +
    (-2329) * X ^ 6
  )

def recurrence1Remainder21 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder21Block0 +
  recurrence1Remainder21Block1 +
  recurrence1Remainder21Block2 +
  recurrence1Remainder21Block3 +
  recurrence1Remainder21Block4 +
  recurrence1Remainder21Block5 +
  recurrence1Remainder21Block6 +
  recurrence1Remainder21Block7 +
  recurrence1Remainder21Block8 +
  recurrence1Remainder21Block9 +
  recurrence1Remainder21Block10 +
  recurrence1Remainder21Block11 +
  recurrence1Remainder21Block12

def recurrence1Remainder22Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-4313) * X ^ 2 +
    (18508415) * X ^ 3 +
    (-1179368522) * X ^ 4 +
    (-726119201869) * X ^ 5 +
    (64443948614929) * X ^ 6 +
    (-1634796781931808) * X ^ 7 +
    (-53104121001510770) * X ^ 8
  )

def recurrence1Remainder22Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (4429251272553627031) +
    (44894677717832501843) * X ^ 1 +
    (-3305729713116580021438) * X ^ 2 +
    (-44370403879186022184327) * X ^ 3 +
    (1038308847642591349427606) * X ^ 4 +
    (15998025457352783001220174) * X ^ 5 +
    (-100565161540304756843088699) * X ^ 6 +
    (-3838383077263422427097601024) * X ^ 7 +
    (10609409481487786287893449330) * X ^ 8
  )

def recurrence1Remainder22Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (357912551995618314750281664824) +
    (928321599646397579187788779389) * X ^ 1 +
    (-39010431621283220839231554468746) * X ^ 2 +
    (-44113655110558033415564496971977) * X ^ 3 +
    (1998385302311546909527456011604480) * X ^ 4 +
    (7168047773872259887036010762730379) * X ^ 5 +
    (-120219085005287976859016785080841404) * X ^ 6 +
    (-272065361572137179529501208609249331) * X ^ 7 +
    (4809921067274839057864714570624963506) * X ^ 8
  )

def recurrence1Remainder22Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (10977775776437172250288677711940278903) +
    (-182892475529011048951487063637634553314) * X ^ 1 +
    (-225651086921399577429239301721385471573) * X ^ 2 +
    (5594738952022077263553172674468414526285) * X ^ 3 +
    (1277630644490436651545302781724918563567) * X ^ 4 +
    (-143971490148075201103356211213635554595906) * X ^ 5 +
    (141516256736775030680012138512082832312497) * X ^ 6 +
    (2934737362609721978989121199535211802940135) * X ^ 7 +
    (-6992542448096665025565927640957960661978556) * X ^ 8
  )

def recurrence1Remainder22Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-44072802935403696670155203768536842732121167) +
    (192741970197878757144563539088813369313968168) * X ^ 1 +
    (378998640258419723632070884120051362325277745) * X ^ 2 +
    (-3579749608066737552394659611752271346887827974) * X ^ 3 +
    (1470706088616565346583942807448141460401188945) * X ^ 4 +
    (43883561445677244621270552241179903867916776540) * X ^ 5 +
    (-107804191716905270671379301045017348646752444777) * X ^ 6 +
    (-272368018417738155386465688834341829656727182307) * X ^ 7 +
    (1744552560514683292522850401633464103487164073490) * X ^ 8
  )

def recurrence1Remainder22Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-1198159366924519362911282886347893563461138591211) +
    (-13522380586587904137675170102049123376972642598255) * X ^ 1 +
    (42291960744969586573911774792841144736581005599284) * X ^ 2 +
    (8750926432463064317977843549196908261718546612891) * X ^ 3 +
    (-344058533433772745293613097758239454232314009302575) * X ^ 4 +
    (793414301057079276958444135752994668657004652391566) * X ^ 5 +
    (286105840767256631723520274510890065023572362924729) * X ^ 6 +
    (-5647611372358746763496541225068797862088473076319126) * X ^ 7 +
    (12919974019283142044299163386735064499292846351870647) * X ^ 8
  )

def recurrence1Remainder22Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-3359642529712813552784602758031437157300360833007150) +
    (-55264383613182431624803628335662273260436933996676443) * X ^ 1 +
    (160256410638548767738242077468342234931330147932565108) * X ^ 2 +
    (-187699197498287563968038848157611949857405459666624355) * X ^ 3 +
    (-125530495858012148433203924611989214856807873955938686) * X ^ 4 +
    (978196998031577665015792587746535197881512952913834490) * X ^ 5 +
    (-2098753766765376407345665535213072040606392112829547991) * X ^ 6 +
    (2509200902385440664953022249445148973518340614987880093) * X ^ 7 +
    (-960911468360702951128952679877965771978837619685617985) * X ^ 8
  )

def recurrence1Remainder22Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (-2955020422515185124782343060600033722414367750058355978) +
    (7885431843716856959097308802487289055487254456220717047) * X ^ 1 +
    (-11095624211693200169626657433590882947061261860714791864) * X ^ 2 +
    (10271392080142350163400890538150244156413129354716463194) * X ^ 3 +
    (-5380934413382372225945705328385940434925030704175890371) * X ^ 4 +
    (-1106074003431348533038327988318116756271265310580429811) * X ^ 5 +
    (5947980221735283329079546034089217488608089251159226427) * X ^ 6 +
    (-7326604306273382998540856475689939289657453030792291754) * X ^ 7 +
    (5705497207972873863741156262146288455918503051039592232) * X ^ 8
  )

def recurrence1Remainder22Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (-2931457099463060316626122280353009607683105193437588786) +
    (686483490383149098892806185938995976957503070727261056) * X ^ 1 +
    (392237688207879363919257997622336249148473105005286291) * X ^ 2 +
    (-564991016999692029446018764889757617938403701678078705) * X ^ 3 +
    (366584368401704101976277645531771262385353107940980624) * X ^ 4 +
    (-157372325343559923726323337127466549384192698639398583) * X ^ 5 +
    (45386360278023680013645700893079549808710348930548432) * X ^ 6 +
    (-6678185887679113978879893779456996358285735532600831) * X ^ 7 +
    (-1617129208214525261381795868878109914024559996222055) * X ^ 8
  )

def recurrence1Remainder22Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    (2065896304835761649251943716831980866030577957515476) +
    (-1331274173456511907919438594725763820832158714577799) * X ^ 1 +
    (632998791593481447936066519187729024708835012469759) * X ^ 2 +
    (-196557836642283534697047644211206516321439411057301) * X ^ 3 +
    (20563020833383032925395632527410479791988032434095) * X ^ 4 +
    (13102113428101739796171669897021044885004664461850) * X ^ 5 +
    (-7166161881916544493302082240165449128387975205734) * X ^ 6 +
    (1389497926404098434424065074976543906675101571844) * X ^ 7 +
    (66396338492958840384238440883040076839006179064) * X ^ 8
  )

def recurrence1Remainder22Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    (-89078533405378437777254629262643671836316543284) +
    (14273231565335481826853527373072799059188163149) * X ^ 1 +
    (1018240205477540412855822089176105472928755355) * X ^ 2 +
    (-550456158562506653336621803130388165662931223) * X ^ 3 +
    (24059355725455180799042198705904480461043314) * X ^ 4 +
    (9544487399330554757158676424051318793601079) * X ^ 5 +
    (-689559839019331475392630310000210966082902) * X ^ 6 +
    (-116373663553683193134387288647362283835662) * X ^ 7 +
    (4276345107771543602977611056688013695730) * X ^ 8
  )

def recurrence1Remainder22Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    (1048169345467189834459223669999805388521) +
    (52670107788284021450360302716996142061) * X ^ 1 +
    (1194637032435987553021206513879586759) * X ^ 2 +
    (13434993855594595313200186766745995) * X ^ 3 +
    (72409407582781145483944263813939) * X ^ 4 +
    (146759985850387230726504100304) * X ^ 5 +
    (-107108246602948219627108488) * X ^ 6 +
    (-670159624643932408123725) * X ^ 7 +
    (-501779026264199559586) * X ^ 8
  )

def recurrence1Remainder22Block12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    (-64927904208095868) +
    (-652050755124) * X ^ 1 +
    (-51573) * X ^ 2
  )

def recurrence1Remainder22 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder22Block0 +
  recurrence1Remainder22Block1 +
  recurrence1Remainder22Block2 +
  recurrence1Remainder22Block3 +
  recurrence1Remainder22Block4 +
  recurrence1Remainder22Block5 +
  recurrence1Remainder22Block6 +
  recurrence1Remainder22Block7 +
  recurrence1Remainder22Block8 +
  recurrence1Remainder22Block9 +
  recurrence1Remainder22Block10 +
  recurrence1Remainder22Block11 +
  recurrence1Remainder22Block12

def recurrence1Remainder23Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-60) * X ^ 1 +
    (144992) * X ^ 2 +
    (337210200) * X ^ 3 +
    (-114233123413) * X ^ 4 +
    (-1446040827081) * X ^ 5 +
    (1120623009347098) * X ^ 6 +
    (-6226391170151878) * X ^ 7 +
    (-1890393992552803819) * X ^ 8
  )

def recurrence1Remainder23Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-7664712791670880689) +
    (1186110264949517701774) * X ^ 1 +
    (14495384085042601774868) * X ^ 2 +
    (-323012681716189718208053) * X ^ 3 +
    (-5350675907080725328279101) * X ^ 4 +
    (19081312682070323987420769) * X ^ 5 +
    (1205027831713483381382352925) * X ^ 6 +
    (-54569879067551627558148355) * X ^ 7 +
    (-101571790718327454660827242646) * X ^ 8
  )

def recurrence1Remainder23Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-650549405351974257520118427995) +
    (9227650503192677672918781534744) * X ^ 1 +
    (46104552010704738459147239845351) * X ^ 2 +
    (-355895040729730830597860482259151) * X ^ 3 +
    (-3770195349740932032386184257945046) * X ^ 4 +
    (17502796376348235058891317421237394) * X ^ 5 +
    (155940408479648275346173351208713541) * X ^ 6 +
    (-539992111689709489806039449053330902) * X ^ 7 +
    (-5891690741671953724981053994148980820) * X ^ 8
  )

def recurrence1Remainder23Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (19364984958319004293618854497598764168) +
    (161459061594926880905641512579200311762) * X ^ 1 +
    (-602614607404782543474794065438144304736) * X ^ 2 +
    (-3554003684411565316456393508546234911994) * X ^ 3 +
    (17255211102769595505069781743533790106948) * X ^ 4 +
    (55384268122777797849118807530568108578721) * X ^ 5 +
    (-408975986341552459375411106638462660105392) * X ^ 6 +
    (-429472406512399769223982788343766418493177) * X ^ 7 +
    (7636922589519785821039428126710304963391474) * X ^ 8
  )

def recurrence1Remainder23Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-5972615649185960823655997056577502238520819) +
    (-103196802034186994620357192376772393313934948) * X ^ 1 +
    (278531489455583671983182498987984801222166978) * X ^ 2 +
    (802671472616779569307783777750692615093839523) * X ^ 3 +
    (-5095472275444967680452415046527764847424531289) * X ^ 4 +
    (1616550411635808977878116633631418844750306089) * X ^ 5 +
    (51990963322906723698998517920121619253352666777) * X ^ 6 +
    (-134953349921645771473991539178865612758973748641) * X ^ 7 +
    (-186243573966169544428262160522130926648718617077) * X ^ 8
  )

def recurrence1Remainder23Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (1666429559828701409885735644943615103733639282975) +
    (-2466916198420109254297779917252601204358032259112) * X ^ 1 +
    (-7193139565494378284995111613989859487638048123699) * X ^ 2 +
    (36471586247137802510340750755657550865252238338051) * X ^ 3 +
    (-42344753845482499724650697994842686063694746861454) * X ^ 4 +
    (-129417700013243732828864495397861779997637217283505) * X ^ 5 +
    (592882251057240725870784756053567465215899867346951) * X ^ 6 +
    (-813491307248877463559718692386536313840641770494930) * X ^ 7 +
    (-981393607761442560978477872434481245809405708939563) * X ^ 8
  )

def recurrence1Remainder23Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (6528414277076057223769874840538652984052724118938262) +
    (-12769021039988110628010405073972212117566839200854058) * X ^ 1 +
    (6710727525884742257164468557671762523932017203572218) * X ^ 2 +
    (30175747630459063031095711692767385422885342369621140) * X ^ 3 +
    (-100248785764461368577107612512630767697897557742058640) * X ^ 4 +
    (162413156184027760713153186952743394367606631091432890) * X ^ 5 +
    (-133590640082852617628624946301179103567220806508211600) * X ^ 6 +
    (-55673262195842482703446022644446419291453166881173181) * X ^ 7 +
    (379361394804245037899965367824579083277847555619049027) * X ^ 8
  )

def recurrence1Remainder23Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (-686623311988715580285156571990752862180113043652979055) +
    (780972389252802949479690830881112451831860821719407528) * X ^ 1 +
    (-565007106884647134434957499720230902141386345251579967) * X ^ 2 +
    (128285820961084225455490897714271781640264571770333288) * X ^ 3 +
    (307039001341708743292866630993907577620549133022106270) * X ^ 4 +
    (-540472668043227544901564871029126882753385776539977491) * X ^ 5 +
    (516912697505258064725658443400572658051263163444854079) * X ^ 6 +
    (-328582041573588224747298523953274430364919446483101658) * X ^ 7 +
    (119023298000490316931922150843289794983990553606648252) * X ^ 8
  )

def recurrence1Remainder23Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (15764024619483439326093495308983445835761470859004150) +
    (-60110943040894486198742741258328108783002759133650284) * X ^ 1 +
    (49212362666451763724724451742959451554558004333520726) * X ^ 2 +
    (-23922300774913644624801096610556066181099864130444627) * X ^ 3 +
    (6148808417178414816994974845600455137044668236983729) * X ^ 4 +
    (830245972089719503095319268574266026478437444563336) * X ^ 5 +
    (-1678360061583332653851771133247003577297695703634195) * X ^ 6 +
    (839159059157663174522296883868759738485717148535281) * X ^ 7 +
    (-203349744888727517211709358660650029083115727665296) * X ^ 8
  )

def recurrence1Remainder23Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    (-7140027856396353107780592363086475355669233733768) +
    (24851537352247083860767221184131530805323720822241) * X ^ 1 +
    (-8747969004708684199605992861862970138447612526507) * X ^ 2 +
    (926599088367198945920418698771499128199733035260) * X ^ 3 +
    (336721822876300553696392160754947126360892447982) * X ^ 4 +
    (-141326484419013466682318415823838359102645815341) * X ^ 5 +
    (13779964434773641076795436769502131326743233685) * X ^ 6 +
    (3490413213896667872921484488540653929129509249) * X ^ 7 +
    (-995591552697449920616804017169423479210992753) * X ^ 8
  )

def recurrence1Remainder23Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    (11753883545940184043689853651614097074310681) +
    (22019885059282066352198371338729758987417033) * X ^ 1 +
    (-1241360921762821318591252624819852067585689) * X ^ 2 +
    (-292540411516541400976854683925085011124788) * X ^ 3 +
    (8991237744046789505603825182565214706852) * X ^ 4 +
    (2730140599159216551065616103945835624732) * X ^ 5 +
    (144957512445012928435501885822570771046) * X ^ 6 +
    (3415621928189986890998128674465258779) * X ^ 7 +
    (39742507950836905779404512839757906) * X ^ 8
  )

def recurrence1Remainder23Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    (222522177019934397987749429416808) +
    (482011122008097505290949836698) * X ^ 1 +
    (-258756034495996674981616083) * X ^ 2 +
    (-2132096922036802698650356) * X ^ 3 +
    (-1765206011740968795608) * X ^ 4 +
    (-267857578388844983) * X ^ 5 +
    (-3772299553634) * X ^ 6 +
    (-794294) * X ^ 7
  )

def recurrence1Remainder23 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder23Block0 +
  recurrence1Remainder23Block1 +
  recurrence1Remainder23Block2 +
  recurrence1Remainder23Block3 +
  recurrence1Remainder23Block4 +
  recurrence1Remainder23Block5 +
  recurrence1Remainder23Block6 +
  recurrence1Remainder23Block7 +
  recurrence1Remainder23Block8 +
  recurrence1Remainder23Block9 +
  recurrence1Remainder23Block10 +
  recurrence1Remainder23Block11

def recurrence1Remainder24Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-4484) * X ^ 1 +
    (1844025) * X ^ 2 +
    (3515040321) * X ^ 3 +
    (-437160397729) * X ^ 4 +
    (-30208061652185) * X ^ 5 +
    (1782788153023498) * X ^ 6 +
    (75891265047055987) * X ^ 7 +
    (-1201518328513847068) * X ^ 8
  )

def recurrence1Remainder24Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-65646022796329222704) +
    (-337144865784472729422) * X ^ 1 +
    (26993499243638401662348) * X ^ 2 +
    (200113653847991665364200) * X ^ 3 +
    (-1731033120215705441743047) * X ^ 4 +
    (-87249910341251524126232233) * X ^ 5 +
    (245658066250066217208463354) * X ^ 6 +
    (6122558870452026951957834792) * X ^ 7 +
    (54895998869065053760926250741) * X ^ 8
  )

def recurrence1Remainder24Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-761593636281390880971590410869) +
    (-3481706658519367446286379590379) * X ^ 1 +
    (21083279719613282317534843566219) * X ^ 2 +
    (366155791030503869533800181563968) * X ^ 3 +
    (-995548660916269458131140851756424) * X ^ 4 +
    (-15850906589950836393883262015590003) * X ^ 5 +
    (11305178887891113532147551672536495) * X ^ 6 +
    (653378206831544942846275668563282656) * X ^ 7 +
    (-128962834558277521146661286351655984) * X ^ 8
  )

def recurrence1Remainder24Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-19964503768396229430711371608755978186) +
    (-919451315218442547947728140666856922) * X ^ 1 +
    (526180748310193457410819886811775418595) * X ^ 2 +
    (-117040313349008727634316589506249842791) * X ^ 3 +
    (-11573839367349732358281411554026148918924) * X ^ 4 +
    (9159932449270445531476273128321321702802) * X ^ 5 +
    (212028110350396528738533651857411112191845) * X ^ 6 +
    (-348412100404979138215482684611103879238099) * X ^ 7 +
    (-3089012035874903642467874332463622276635518) * X ^ 8
  )

def recurrence1Remainder24Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (8787953787800057138534507392612999025079156) +
    (32298868767447754344864573417396398055540391) * X ^ 1 +
    (-158956189353983597640140225968330405329202570) * X ^ 2 +
    (-159946346627034111492081833052243935085826347) * X ^ 3 +
    (2053117137312446097252905665708171293294955350) * X ^ 4 +
    (-1692827534970199296655865543170820237029316689) * X ^ 5 +
    (-17328442228565544484785993690729563650850253531) * X ^ 6 +
    (46882454155572735710251684103067266472037240530) * X ^ 7 +
    (60699672912375196361252975647329068625681778521) * X ^ 8
  )

def recurrence1Remainder24Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-492964048180503567794237322887238239808056091730) +
    (535034283561283993430861041226970857196747060306) * X ^ 1 +
    (2318639987710616732879835244395478339063614734231) * X ^ 2 +
    (-8340536903252677298548724493654868460098424907864) * X ^ 3 +
    (4076918239957814399829082024624735469727184086254) * X ^ 4 +
    (37356252392369544133903144701282118686545444589085) * X ^ 5 +
    (-104159695137006962784475162704718105817439999544319) * X ^ 6 +
    (58164678579912948160930285935213101064005480685185) * X ^ 7 +
    (320673134121474499950016185509383657477202553957550) * X ^ 8
  )

def recurrence1Remainder24Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-966410230161405973775927755796471384338588517172481) +
    (1057521205019777592525830018825566490236496451057365) * X ^ 1 +
    (742127755010771180546078381774652053372379927188243) * X ^ 2 +
    (-4785959974880926339643565685229096339862358294612527) * X ^ 3 +
    (8760490003044905330957105454623115941276373458917434) * X ^ 4 +
    (-8203512958915321638917069527219780641033470636605772) * X ^ 5 +
    (124873650185766338123408195979723000643560020942470) * X ^ 6 +
    (13137889188370020679157083869417823052352801227592109) * X ^ 7 +
    (-24260889690025450128779071629645492560555871074703942) * X ^ 8
  )

def recurrence1Remainder24Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (26214602613453567649132125504002244590507094605348433) +
    (-17819254933458328320669253465733783739288751672154723) * X ^ 1 +
    (4325601937530417313343374923753902307504119361121808) * X ^ 2 +
    (7085160897111292059077791287867026927987327952014566) * X ^ 3 +
    (-12241834034897506887363455958967121012693100190156582) * X ^ 4 +
    (11415768083294728785940734875671568824441361346817452) * X ^ 5 +
    (-7445759028232835325223788537982047007543276937229425) * X ^ 6 +
    (3219440258276007637241900872819713062091450575441678) * X ^ 7 +
    (-355308909916774060665370153856512577405243427200776) * X ^ 8
  )

def recurrence1Remainder24Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (-855610967830138214679424247973466442497801794595178) +
    (919773290386774278560369110956023102289357227011826) * X ^ 1 +
    (-535092720771623363396985167307577928365692065974083) * X ^ 2 +
    (180092494351645424091732349753438665506657826740768) * X ^ 3 +
    (-8425469595670461199404319368098727400289044590510) * X ^ 4 +
    (-28226822940414173111034757461886101215568527671949) * X ^ 5 +
    (16873132029904715975144283624084105259274856352785) * X ^ 6 +
    (-4470227893646445815672202856041563204717756135371) * X ^ 7 +
    (41103553665028866702092783573336178371067872994) * X ^ 8
  )

def recurrence1Remainder24Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    (391988867676424019441773103447860968897246402867) +
    (-125515986126920090053261260794941424373115036152) * X ^ 1 +
    (8766011014486695941776157846266783124975520055) * X ^ 2 +
    (4405610885467658215728651561274847243551785183) * X ^ 3 +
    (-1108541808326678930214575740370730576125023045) * X ^ 4 +
    (1168967674723539927797550980063930000826216) * X ^ 5 +
    (28253243546566767172168785893940385861585496) * X ^ 6 +
    (-1543504786611669941401850724286147096140207) * X ^ 7 +
    (-403947522433154763994537377347421116546424) * X ^ 8
  )

def recurrence1Remainder24Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    (12319330366236617959699752080407913790123) +
    (3998392909408417154375212108573971126095) * X ^ 1 +
    (220383357605673005449700582181334082101) * X ^ 2 +
    (5397653765049896892328607975682692166) * X ^ 3 +
    (65698345123983352604138413107212789) * X ^ 4 +
    (390118339111116952445252584220795) * X ^ 5 +
    (939164548290806025064203691306) * X ^ 6 +
    (-215132251974574146416121296) * X ^ 7 +
    (-3936944843241963325483716) * X ^ 8
  )

def recurrence1Remainder24Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    (-3878580211389726856884) +
    (-755768532071763755) * X ^ 1 +
    (-16728815392683) * X ^ 2 +
    (-9250026) * X ^ 3
  )

def recurrence1Remainder24 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder24Block0 +
  recurrence1Remainder24Block1 +
  recurrence1Remainder24Block2 +
  recurrence1Remainder24Block3 +
  recurrence1Remainder24Block4 +
  recurrence1Remainder24Block5 +
  recurrence1Remainder24Block6 +
  recurrence1Remainder24Block7 +
  recurrence1Remainder24Block8 +
  recurrence1Remainder24Block9 +
  recurrence1Remainder24Block10 +
  recurrence1Remainder24Block11

def recurrence1Remainder25Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-8) +
    (-4584) * X ^ 1 +
    (58202904) * X ^ 2 +
    (-13173586573) * X ^ 3 +
    (-826150121927) * X ^ 4 +
    (152811697040613) * X ^ 5 +
    (1321979052167081) * X ^ 6 +
    (-239337682022022144) * X ^ 7 +
    (-4010384813694609235) * X ^ 8
  )

def recurrence1Remainder25Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (140981990055572131702) +
    (2708132833691499223520) * X ^ 1 +
    (-11117019750973116692969) * X ^ 2 +
    (-1038032059894976781868696) * X ^ 3 +
    (-1516553408964565706773563) * X ^ 4 +
    (113435219738758599710588858) * X ^ 5 +
    (1281528474945542949359844633) * X ^ 6 +
    (-10949556985199660678063311825) * X ^ 7 +
    (-125392070547471792509348429414) * X ^ 8
  )

def recurrence1Remainder25Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (215558598921243747288171008522) +
    (10589490421697306581022864221125) * X ^ 1 +
    (2185427701132490215696739421726) * X ^ 2 +
    (-509558385722369015881141643744004) * X ^ 3 +
    (-973972135415319263109760588480179) * X ^ 4 +
    (20888946531069052727010274247959325) * X ^ 5 +
    (48030170025326506913702104280824156) * X ^ 6 +
    (-676296360117176906042635167860569831) * X ^ 7 +
    (-1590442759177347388958151340464345290) * X ^ 8
  )

def recurrence1Remainder25Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (19132701444277355709761164775195411393) +
    (34285205475050473373020125037058876286) * X ^ 1 +
    (-466785756737243618782844261631760400715) * X ^ 2 +
    (-412588225219251476476316758306081249061) * X ^ 3 +
    (9692705499083531167630753290409160783478) * X ^ 4 +
    (-2380408842837340426918169537663901078116) * X ^ 5 +
    (-163589430880070156827029618454308988307158) * X ^ 6 +
    (252102819302740101766946367034325092681392) * X ^ 7 +
    (2069187720024328570227264006657291355787421) * X ^ 8
  )

def recurrence1Remainder25Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-6686117133490773997916420110131588575194757) +
    (-15713983361751386062903313597586957964997198) * X ^ 1 +
    (108107639108100048200385184492677540844180312) * X ^ 2 +
    (-20984404370839676984211613442320871622164412) * X ^ 3 +
    (-1099916178960450575915685818529555687157919662) * X ^ 4 +
    (2396380361633016720239785833367126775002379437) * X ^ 5 +
    (5210269669951627349681283239449495527787077121) * X ^ 6 +
    (-31726243031577828134638573492632902354471093984) * X ^ 7 +
    (27161067309970447311973679620919266785043335179) * X ^ 8
  )

def recurrence1Remainder25Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (178205050773421933199244930914495314572679868757) +
    (-596676247251947916726407473354347441926711917636) * X ^ 1 +
    (217432829839310336002817984518166135227832232782) * X ^ 2 +
    (3120093033409065786758827883803080316430806655045) * X ^ 3 +
    (-8665970048652318840432392931146127238888078672941) * X ^ 4 +
    (4536997018687278322071825226880515848890525143295) * X ^ 5 +
    (30849558643173766701288435074088248503281094991097) * X ^ 6 +
    (-95220340007489739605214981707878241588414868276620) * X ^ 7 +
    (106536583640868574405256960339526933228721070489684) * X ^ 8
  )

def recurrence1Remainder25Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (93164830782748409651416769751500784564105781779151) +
    (-578627282538253583321543106577877607366906622185027) * X ^ 1 +
    (1092445794418350991227293304062352945919761085569406) * X ^ 2 +
    (-1010285970366236261311586117768254048794953317061497) * X ^ 3 +
    (-214009112868664380275346632408479348707168575965346) * X ^ 4 +
    (2355888510834570221982904312471436476951726541414062) * X ^ 5 +
    (-4213993205963876886713791483973426125072084952402930) * X ^ 6 +
    (4374189055099625082866580706568063519555735942802816) * X ^ 7 +
    (-2426562057443760437955479795717455422957310538712072) * X ^ 8
  )

def recurrence1Remainder25Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (-547879151578059857926911438579520090404041947816918) +
    (2795730063013252313772849604653854918973775121773327) * X ^ 1 +
    (-3262110651062154797891480141719997226909503679611118) * X ^ 2 +
    (2229408024555610605875320579090371052347830568858257) * X ^ 3 +
    (-782020535002471299227450895820569521667112384018964) * X ^ 4 +
    (-181307121752543769113092165260465525831938245452680) * X ^ 5 +
    (451941038044837849384065317876121764680852616234936) * X ^ 6 +
    (-317279331924508839779158647612370746188168316281419) * X ^ 7 +
    (118291409856805654155265315825055214060283244115820) * X ^ 8
  )

def recurrence1Remainder25Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (-9067085802950879916402351125455550792960048428609) +
    (-16752041284191756224890747636760189106858007365013) * X ^ 1 +
    (10467065061107254327435430760433350574226355396713) * X ^ 2 +
    (-2776079750871447450040554150772889836624742403460) * X ^ 3 +
    (3807677038252640414310368810121093925398743568) * X ^ 4 +
    (254735917876843325547217135374763303741153870467) * X ^ 5 +
    (-79970716861673357875251224597009651876784519597) * X ^ 6 +
    (5086554838729128011357916514757208966931108845) * X ^ 7 +
    (3002133683565988392458948980633539621521290947) * X ^ 8
  )

def recurrence1Remainder25Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    (-733117506467283953626185539260366384756126532) +
    (-3671711776486332869099310649452547803580870) * X ^ 1 +
    (19844078368367647479805269940340036920130269) * X ^ 2 +
    (-1019998825567616745605344467509616177727522) * X ^ 3 +
    (-300251147139026137458381741843066253390545) * X ^ 4 +
    (8331610236584716832086290155981013157605) * X ^ 5 +
    (3122163349981012136172833905772391019781) * X ^ 6 +
    (183377772338127822273190994703138876095) * X ^ 7 +
    (4809272671110001400826091023037899395) * X ^ 8
  )

def recurrence1Remainder25Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    (63506625011524370119277185841139399) +
    (418819725802625644021293199369765) * X ^ 1 +
    (1197901248587625823394131256191) * X ^ 2 +
    (309822799767340730668764003) * X ^ 3 +
    (-4534798300274140721268369) * X ^ 4 +
    (-6000547169591553991323) * X ^ 5 +
    (-1661458723421419362) * X ^ 6 +
    (-62108676656411) * X ^ 7 +
    (-84879584) * X ^ 8
  )

def recurrence1Remainder25 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder25Block0 +
  recurrence1Remainder25Block1 +
  recurrence1Remainder25Block2 +
  recurrence1Remainder25Block3 +
  recurrence1Remainder25Block4 +
  recurrence1Remainder25Block5 +
  recurrence1Remainder25Block6 +
  recurrence1Remainder25Block7 +
  recurrence1Remainder25Block8 +
  recurrence1Remainder25Block9 +
  recurrence1Remainder25Block10

def recurrence1Remainder26Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-606) +
    (-264384) * X ^ 1 +
    (656868640) * X ^ 2 +
    (-43610885488) * X ^ 3 +
    (-7907413645917) * X ^ 4 +
    (237849108519302) * X ^ 5 +
    (17822290888370542) * X ^ 6 +
    (-60757622243990768) * X ^ 7 +
    (-15092317899760440692) * X ^ 8
  )

def recurrence1Remainder26Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-122739733042983787952) +
    (3980510503323414556252) * X ^ 1 +
    (80975272851461060031324) * X ^ 2 +
    (-339731311869300366432704) * X ^ 3 +
    (-14893034520022581397395970) * X ^ 4 +
    (-61507058526884679075023217) * X ^ 5 +
    (1557412099701861736209197599) * X ^ 6 +
    (11931824111968927302483079140) * X ^ 7 +
    (-74615194376512967677074331502) * X ^ 8
  )

def recurrence1Remainder26Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-1147978231603713844269051911554) +
    (1703605390132880923263815628087) * X ^ 1 +
    (65342815875548638995525416873715) * X ^ 2 +
    (46764779696712004097218540893258) * X ^ 3 +
    (-2756851892830333293894575180613507) * X ^ 4 +
    (-4973479925282740496115957637429406) * X ^ 5 +
    (90957482947576568207820968873219052) * X ^ 6 +
    (210316203154359032521086649236863646) * X ^ 7 +
    (-2519572862830697884162971473184893653) * X ^ 8
  )

def recurrence1Remainder26Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-5716537617376765869030209898778114261) +
    (60367025213541084292114337935339630656) * X ^ 1 +
    (106109478758528122081569249927892450975) * X ^ 2 +
    (-1258161069668623656362952421948325399372) * X ^ 3 +
    (-1140152263465682044046210616394825658004) * X ^ 4 +
    (22303221764783494685504179773267006285479) * X ^ 5 +
    (-3068732178837805852846609862113546712980) * X ^ 6 +
    (-321295042349681723632820191220560028096900) * X ^ 7 +
    (424684769546239265370557834075128561258657) * X ^ 8
  )

def recurrence1Remainder26Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (3467010735621713056201496621093019705005373) +
    (-9820907169482207987595217407352126266374824) * X ^ 1 +
    (-22643107225379856272866206550665913259766049) * X ^ 2 +
    (134638847786245837888592364557673177253229780) * X ^ 3 +
    (-14699805210117737208311297643153352365036420) * X ^ 4 +
    (-1140838767007516959294651878397634074067432175) * X ^ 5 +
    (2198291250583775650210278270666734838628936545) * X ^ 6 +
    (4377108880256740642198220811140850983490192676) * X ^ 7 +
    (-23751755542444203265532361883311010910235695327) * X ^ 8
  )

def recurrence1Remainder26Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (19324817302042652217758620587384065055762449306) +
    (101615939163603552285300697518056435893445132998) * X ^ 1 +
    (-317667961885729755212373371552547149669387921084) * X ^ 2 +
    (159166271221174898678323869034613115263357675153) * X ^ 3 +
    (1131726611565921421877434735816529017800358660734) * X ^ 4 +
    (-3121040979427526931885619959908673567118952942816) * X ^ 5 +
    (2410820301271893278955207186857464670676422527112) * X ^ 6 +
    (5652777509329527173079846530507218923725434481468) * X ^ 7 +
    (-19732291277255062629310930650026635106843797097302) * X ^ 8
  )

def recurrence1Remainder26Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (26291104706672415387657384787000492935607658169965) +
    (-6727489552838408179719537274002341989653780935383) * X ^ 1 +
    (-41253678474640061179888179619384622750096492600682) * X ^ 2 +
    (89385293720112488291822566607840486914388527327607) * X ^ 3 +
    (-95585932980783456538720432113582851069188735402901) * X ^ 4 +
    (43474965187021755618392755436146346521712452303683) * X ^ 5 +
    (36264262946462470264963478808724054066882211552046) * X ^ 6 +
    (-90077395241547150221305671591175204232776602561308) * X ^ 7 +
    (88311380474228653853967785701384992363103654210137) * X ^ 8
  )

def recurrence1Remainder26Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (-46171373163504543158557914214045685537226653625329) +
    (1760996210278097879640123794600894772440302289074) * X ^ 1 +
    (19420671632102037980135832791336634529791939084307) * X ^ 2 +
    (-17939533405231251363616472490566952428926934345738) * X ^ 3 +
    (8088426106972228431048023598589508535972069747653) * X ^ 4 +
    (-932324612480629040663752920016275618786874393818) * X ^ 5 +
    (-1259284677279418318144667404132063930058303046310) * X ^ 6 +
    (907052891357068529730115275023977792560595353116) * X ^ 7 +
    (-259796156938576126935931880575940133496455929373) * X ^ 8
  )

def recurrence1Remainder26Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (-5743205394693217441326578355115890903196243276) +
    (31287071019551607357660603537375697104621823622) * X ^ 1 +
    (-9904927975710995422196730406795647174801069171) * X ^ 2 +
    (407325991422521290337696636708310350463817027) * X ^ 3 +
    (520301936077397947184043319587679666723442887) * X ^ 4 +
    (-116621656765750600540617213369055032965477929) * X ^ 5 +
    (-4657048383506180696440995131466651437813763) * X ^ 6 +
    (4212045223053116439059613323987782256717639) * X ^ 7 +
    (-130364068837196412915331835983767607389036) * X ^ 8
  )

def recurrence1Remainder26Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    (-79855619076933278288806586082688280262928) +
    (806770333612448780191069553229078389783) * X ^ 1 +
    (931515776698594048009905810307361214858) * X ^ 2 +
    (68165293576858192487165357082552974621) * X ^ 3 +
    (2171214875594016473752712052888364881) * X ^ 4 +
    (34944721186945926298271664519464594) * X ^ 5 +
    (286363027698652162782785744858111) * X ^ 6 +
    (1089413395938381807202776494154) * X ^ 7 +
    (1107378815922411149079177229) * X ^ 8
  )

def recurrence1Remainder26Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    (-3292471087723803892438322) +
    (-7229173878372384068265) * X ^ 1 +
    (-3092981143429333279) * X ^ 2 +
    (-199417564971929) * X ^ 3 +
    (-629591425) * X ^ 4 +
    (-1) * X ^ 5
  )

def recurrence1Remainder26 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder26Block0 +
  recurrence1Remainder26Block1 +
  recurrence1Remainder26Block2 +
  recurrence1Remainder26Block3 +
  recurrence1Remainder26Block4 +
  recurrence1Remainder26Block5 +
  recurrence1Remainder26Block6 +
  recurrence1Remainder26Block7 +
  recurrence1Remainder26Block8 +
  recurrence1Remainder26Block9 +
  recurrence1Remainder26Block10

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder3Data. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 1 certificate: Remainder3Data

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1Remainder30Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-8) * X ^ 2 +
    (179024) * X ^ 3 +
    (30754666) * X ^ 4 +
    (477021417487) * X ^ 5 +
    (-232679923019180) * X ^ 6 +
    (101440949732911807) * X ^ 7 +
    (-24730814056414366604) * X ^ 8
  )

def recurrence1Remainder30Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (4024008953500262585477) +
    (-453727011615361254128640) * X ^ 1 +
    (35773836854796317297182412) * X ^ 2 +
    (-2034870664052154352728358965) * X ^ 3 +
    (83905281819788621191507714267) * X ^ 4 +
    (-2629889589502770617695121931036) * X ^ 5 +
    (68870813236477147681526337937965) * X ^ 6 +
    (-1742335801519438920177093336423298) * X ^ 7 +
    (38064345949383782936507754711195193) * X ^ 8
  )

def recurrence1Remainder30Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-179204151669257402026118359209574838) +
    (-36973979374681706412342359208334347420) * X ^ 1 +
    (2137363388566628284743357197726381838956) * X ^ 2 +
    (-71911779643193959004534831480162841168816) * X ^ 3 +
    (1762597275403315276703628289405966746342987) * X ^ 4 +
    (-34138692680849682446976950412851940339449937) * X ^ 5 +
    (552467363692672535803570517425603952564410700) * X ^ 6 +
    (-7939075987439788713884785869012474294399561470) * X ^ 7 +
    (109349853254286577338279748981779958688710271384) * X ^ 8
  )

def recurrence1Remainder30Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-1545880979781235721694231385301134279432156136508) +
    (22676504550839967189427936447813371811662024521348) * X ^ 1 +
    (-328974304001526798795544959789385551647442053342118) * X ^ 2 +
    (4465286366450333486645924557987928865749063110891113) * X ^ 3 +
    (-54858799736235509791029301212568734913907021329458784) * X ^ 4 +
    (602145153406959310447880262540369323094402427015474536) * X ^ 5 +
    (-5892564198806635769120058488175133730683428849273203299) * X ^ 6 +
    (51545635611367479734117846407920081397724562865823431419) * X ^ 7 +
    (-404733608756654388005937985259073789253768588125584448198) * X ^ 8
  )

def recurrence1Remainder30Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (2864527516590043161232655711795302583444761115820971275073) +
    (-18338507132563601942380943235856576917881771753697255182725) * X ^ 1 +
    (106463557541167214228442303735616701032671133924883061691086) * X ^ 2 +
    (-561314278962909219698295422547172122011777036251181215870161) * X ^ 3 +
    (2688714399335101325596980661656839893849979702706195758065970) * X ^ 4 +
    (-11689549642467735400408356871109602940443575954274571913303935) * X ^ 5 +
    (45985306071259975175409394912470024994236286701497963142226289) * X ^ 6 +
    (-162524193462981449826461384091871109782767383312237911541949276) * X ^ 7 +
    (508227155293203124988320624447267957476766364183277258945266574) * X ^ 8
  )

def recurrence1Remainder30Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-1359566889412032846429096507235445040180812639893288373562239901) +
    (2851082208712297703151714776027122850324020555819312143829871493) * X ^ 1 +
    (-3190153207632062724964284287111805372054977741114378625081653140) * X ^ 2 +
    (-8222234960983443522939973587058089086984514578165173608118869832) * X ^ 3 +
    (71950429460641988698423177959227678104989764102893748462736114766) * X ^ 4 +
    (-318655852741105373388953630861154707199405529356719958730512207827) * X ^ 5 +
    (1138173346144201769318489239229936809648313545540220639990693475460) * X ^ 6 +
    (-3582063774549879460130271415765521782441072173836308200276279318640) * X ^ 7 +
    (9726947810203285340886442629401443956236951259119670967933377171956) * X ^ 8
  )

def recurrence1Remainder30Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-20245176225376080422475912791710571138087986505378621699306103086440) +
    (22607993508856402456617761214149894753738162723981498978965300550861) * X ^ 1 +
    (13846440143222403243857340271597973942352036638054698356320170152420) * X ^ 2 +
    (28554743406922175307074588179655867012406316324581886630530548415658) * X ^ 3 +
    (-1182651282063552015081910611553092382095478983530767711217513298572824) * X ^ 4 +
    (6187143208974982925970866126985089225146046238944149450001511003299263) * X ^ 5 +
    (-12085970620285470392865219150601545691257864750607172538217681000660039) * X ^ 6 +
    (-31901383709098183409915792383015946630065796182777010317406901156610827) * X ^ 7 +
    (309561833262843952809262611815720791267176350825051048545067831418476941) * X ^ 8
  )

def recurrence1Remainder30Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (-987677926928852386393594783917498824380279216660370137348055931732846692) +
    (588024880259329850641699607917506419856806472613989222099654546179168908) * X ^ 1 +
    (9264145145529487333065545272393485536463105174908381470661656996415373733) * X ^ 2 +
    (-48854848455228927648187599058205666114899346301381293944978894488897400107) * X ^ 3 +
    (118363483970638617886026488422400632582889101072970288920770240460647017406) * X ^ 4 +
    (-13370921428541403960987264206305331329502666685355146998744423451261826349) * X ^ 5 +
    (-1160896702235321806926155180301241708749461687596901244528567903768516672786) * X ^ 6 +
    (5416819534297521735342029738650870668182171078734748142411195867178458126851) * X ^ 7 +
    (-13598457153377359221241680560545494370786197657396585222808925930939766106640) * X ^ 8
  )

def recurrence1Remainder30Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (12293821311286611871202468054543104929690652817501167700804438443144352646901) +
    (63890905636886912336226670298245357517314331241637596228909850780665834212548) * X ^ 1 +
    -((3 * 10 ^ 77 +
      96042262259627221364964157794682836090253498123192830176801346768031823893364)) * X ^ 2 +
    ((12 * 10 ^ 77 +
      88439266026287706649311815457268670346299060155594090441456218050598517348007)) * X ^ 3 +
    -((27 * 10 ^ 77 +
      84533571779230066412021845150390271391126105507858835292019039476615358329608)) * X ^ 4 +
    ((30 * 10 ^ 77 +
      21022699295861798022802581679693657514244784648543256589748207996165763242506)) * X ^ 5 +
    ((63 * 10 ^ 77 +
      72655543282697507054098880371590413640098565564533962612427941948736179061248)) * X ^ 6 +
    -((503 * 10 ^ 77 +
      15538790393813884086211108635282259215299900350178106990631385272414836887462)) * X ^ 7 +
    ((1881 * 10 ^ 77 +
      81234974120523759381199418842667518119761069584320583760568653061355197891663)) * X ^ 8
  )

def recurrence1Remainder30Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((5398 * 10 ^ 77 +
      44544806811164544346815931077803689983026155988049170761101468716449152852654)) +
    ((13149 * 10 ^ 77 +
      63381584975580411685665925306576885383876271381976106390185088995350036226044)) * X ^ 1 +
    -((28329 * 10 ^ 77 +
      61319623624223922612719819140228645599802013120937393586924233622809071147118)) * X ^ 2 +
    ((55143 * 10 ^ 77 +
      25698833414817309441740525901669871318255178687825615833589108515931765379326)) * X ^ 3 +
    -((98233 * 10 ^ 77 +
      71650002842268045067928307601056453411895545475235805828187397690464187019978)) * X ^ 4 +
    ((161539 * 10 ^ 77 +
      08515362124440216079338858528841092923698896994648198128599585321933507688391)) * X ^ 5 +
    -((246729 * 10 ^ 77 +
      82597717824925062618263418929687987715868218696519945238350744394649053882099)) * X ^ 6 +
    ((351665 * 10 ^ 77 +
      53675122033587120505110880403502016910954759245948424965759432154930537538922)) * X ^ 7 +
    -((469498 * 10 ^ 77 +
      07668912672815048823497379023329058984347663344774370127978105716918838826127)) * X ^ 8
  )

def recurrence1Remainder30Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((588987 * 10 ^ 77 +
      51679251732090932462756142994987227470378401137868957962566949052247962058830)) +
    -((696236 * 10 ^ 77 +
      39576848753243718206642823848292474709570948204395678589619280115382516285324)) * X ^ 1 +
    ((777500 * 10 ^ 77 +
      66469441271781763613081059113780969293778483475067120470317565586744881191969)) * X ^ 2 +
    -((822251 * 10 ^ 77 +
      74244113453057363360237729600562523297152011695800243201475928438641391323414)) * X ^ 3 +
    ((825497 * 10 ^ 77 +
      77433585876047809859239589397583704250627237971723867666555166478842713669344)) * X ^ 4 +
    -((788629 * 10 ^ 77 +
      09008319389329793144120444348503412512015638338885692480594619933748151825207)) * X ^ 5 +
    ((718616 * 10 ^ 77 +
      17587416195823642756731283672918981396625831551497803412791111407407499243582)) * X ^ 6 +
    -((625982 * 10 ^ 77 +
      68203509287325825363707077757076047763491948404540761367423412158541667877138)) * X ^ 7 +
    ((522328 * 10 ^ 77 +
      32620198375180849827500216389394710718433113262620150797868060086010432185611)) * X ^ 8
  )

def recurrence1Remainder30Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((418167 * 10 ^ 77 +
      57204284487997184491297910580978624859397280650449284020085939805016537121909)) +
    ((321556 * 10 ^ 77 +
      92185016652634743605926884083993085912259417191408995184205690703384129195208)) * X ^ 1 +
    -((237602 * 10 ^ 77 +
      44479350439984669377098056042127913340264298475916025841369295483046621340362)) * X ^ 2 +
    ((168653 * 10 ^ 77 +
      76520372639563131287106271952671683664243208591892802651358470329547719388728)) * X ^ 3 +
    -((114881 * 10 ^ 77 +
      61090538496635571322553799349159890504376240458533771882012393258257312819157)) * X ^ 4 +
    ((74973 * 10 ^ 77 +
      16056040079523803003289733801098294690379738804613869586231936849966490454629)) * X ^ 5 +
    -((46779 * 10 ^ 77 +
      36942185549123077764746854956975534097579090798864594354813203874342078531782)) * X ^ 6 +
    ((27839 * 10 ^ 77 +
      62289896585025574778165916113156451102909859251474770631920500927437296205371)) * X ^ 7 +
    -((15763 * 10 ^ 77 +
      09148367956723587824565004165031538085554706244798510673407453791285161808265)) * X ^ 8
  )

def recurrence1Remainder30Block12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((8470 * 10 ^ 77 +
      10856743521030817930811536018712083082159780463815449718891062788700093784844)) +
    -((4308 * 10 ^ 77 +
      53622814861337576523389200278686498248800050127435208616555976542856075108934)) * X ^ 1 +
    ((2069 * 10 ^ 77 +
      78154465339680743551319089030616022609445083443493320200485441591694469275402)) * X ^ 2 +
    -((936 * 10 ^ 77 +
      85375517402831066700830220230779874814266368052112627961790098551186292677762)) * X ^ 3 +
    ((398 * 10 ^ 77 +
      65728402929959663196554827000207119551579165819291385530935944272871231301355)) * X ^ 4 +
    -((159 * 10 ^ 77 +
      13028146501764937509219606675639165927048343089575355276839535699262296719279)) * X ^ 5 +
    ((59 * 10 ^ 77 +
      45353547948251466012727094255100250555954330598620983016004020153505202647983)) * X ^ 6 +
    -((20 * 10 ^ 77 +
      74477692605407839113645381870498466686183308682133541356084259978633855899602)) * X ^ 7 +
    ((6 * 10 ^ 77 +
      74461990907623585363458366112947308473564960929398356230375635079126179452507)) * X ^ 8
  )

def recurrence1Remainder30Block13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    -((2 * 10 ^ 77 +
      03847734819215826421435314192094498992896357031348647856186438074115378109371)) +
    (57135769510060078692401921468047597800136099127910548317546758145869716383679) * X ^ 1 +
    (-14815042078440609075985919940138919909089519674066290142820247383085196128127) * X ^ 2 +
    (3545222914893712326206528796479084098997714334778175052955882894646241038904) * X ^ 3 +
    (-781180638840573974600871508196653912903116876024338642130622120750037433134) * X ^ 4 +
    (158198288556425185236400140464479511140692366474006193806836523494698068047) * X ^ 5 +
    (-29406486499099729956300950206526716081741152804858236072771958329847869630) * X ^ 6 +
    (5015743261313349696684144127279389992962815447726472509388863282654896318) * X ^ 7 +
    (-785670058579752082037762826501661006933927038226813934010398924281667696) * X ^ 8
  )

def recurrence1Remainder30Block14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    (113218082722740306109096795283920026113796946052082605525289866910205118) +
    (-15030194968541871038434252452760894584665599963720825971855744422440578) * X ^ 1 +
    (1834827527184728066937284515735569308140319670438270299778071166717767) * X ^ 2 +
    (-204025618344663817048914574886865361097987480803804696192799852734959) * X ^ 3 +
    (20198801752175316049811777180007732333864490316687238813135479047170) * X ^ 4 +
    (-1702446196019049729108408376329147576875929173287432278190303921572) * X ^ 5 +
    (111276423164953787066102218819162935182149174135000407027111793574) * X ^ 6 +
    (-4139802210795116435144972353740749138052802559496185808778173681) * X ^ 7 +
    (-151124331760411728556559511211740112853960585305662203599722374) * X ^ 8
  )

def recurrence1Remainder30Block15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    (41243569877879273185902978459566132734664168360527059732092987) +
    (-3862183401125520033506848253432213202056041276232465423771467) * X ^ 1 +
    (229990070726724836385075136060987756387867673675465768566161) * X ^ 2 +
    (-9290697854385371177486367979965834868714849010537332656527) * X ^ 3 +
    (248727234973674867513257277298321151413727299366901080327) * X ^ 4 +
    (-4078153179376266612559525887827345638572102738839086124) * X ^ 5 +
    (33809467951087185928507141418130229292018171920903153) * X ^ 6 +
    (-37817579212424531880147848185303768933624033934741) * X ^ 7 +
    (-1246244779211640409521911260108607639113011879035) * X ^ 8
  )

def recurrence1Remainder30Block16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    (5925938749583198575776933513034738181026733413) +
    (2887992996509810155902212709188379207670954) * X ^ 1 +
    (-63885184880089663970531341606708629746598) * X ^ 2 +
    (131521815278795812666703554559090676741) * X ^ 3 +
    (-99880414820312230247369694394082213) * X ^ 4 +
    (27137546393774277028731104945873) * X ^ 5 +
    (-2142134801952946451436700965) * X ^ 6 +
    (34993556805095373359551) * X ^ 7 +
    (-67212899013694767) * X ^ 8
  )

def recurrence1Remainder30Block17 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 153 * (
    (3578955260) +
    (-1) * X ^ 1
  )

def recurrence1Remainder30 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder30Block0 +
  recurrence1Remainder30Block1 +
  recurrence1Remainder30Block2 +
  recurrence1Remainder30Block3 +
  recurrence1Remainder30Block4 +
  recurrence1Remainder30Block5 +
  recurrence1Remainder30Block6 +
  recurrence1Remainder30Block7 +
  recurrence1Remainder30Block8 +
  recurrence1Remainder30Block9 +
  recurrence1Remainder30Block10 +
  recurrence1Remainder30Block11 +
  recurrence1Remainder30Block12 +
  recurrence1Remainder30Block13 +
  recurrence1Remainder30Block14 +
  recurrence1Remainder30Block15 +
  recurrence1Remainder30Block16 +
  recurrence1Remainder30Block17

def recurrence1Remainder31Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (790) * X ^ 2 +
    (13593174) * X ^ 3 +
    (-3143765912) * X ^ 4 +
    (22224431529139) * X ^ 5 +
    (-9581546513540763) * X ^ 6 +
    (3625768004123046781) * X ^ 7 +
    (-736427900725824578076) * X ^ 8
  )

def recurrence1Remainder31Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (103602730525610362262883) +
    (-9720000525951758301319245) * X ^ 1 +
    (641384061688276159506992347) * X ^ 2 +
    (-29807610346047288542981828167) * X ^ 3 +
    (1011993514928827874626255085507) * X ^ 4 +
    (-27588785382850700761419492527289) * X ^ 5 +
    (778856192928799753253598015152603) * X ^ 6 +
    (-26284968749545126326416226531774290) * X ^ 7 +
    (838677187750941599932471485344008670) * X ^ 8
  )

def recurrence1Remainder31Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-19840159097813206912112856692962029068) +
    (283995824988650272088359232893564919176) * X ^ 1 +
    (-200658286951553508779688024152928626651) * X ^ 2 +
    (-120919132753601655772668751345790687120650) * X ^ 3 +
    (4455966837412600171978384930666283132335687) * X ^ 4 +
    (-120077005830542256214571792357570834586972659) * X ^ 5 +
    (2902315697149986652200100169000154423713480755) * X ^ 6 +
    (-64526473845662151335844662172009059089429794440) * X ^ 7 +
    (1290617704867752262141072773114910620724348839175) * X ^ 8
  )

def recurrence1Remainder31Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-22794729084532014995478647727817834396948459520021) +
    (353315556448081185199307400698484199360270721194167) * X ^ 1 +
    (-4812880786691912788110047237084103655447978586593530) * X ^ 2 +
    (57878291146815460358092129376595562590210734151862692) * X ^ 3 +
    (-617737352359349426905107435023724165392922381504137923) * X ^ 4 +
    (5882473491592880845864414439966373119811884720514047408) * X ^ 5 +
    (-50225332563756226781419166424600265060827872658557808475) * X ^ 6 +
    (386197339368419763052534094787306808064088847892188612625) * X ^ 7 +
    (-2684385573847498095843446412228192123945573443457869640978) * X ^ 8
  )

def recurrence1Remainder31Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (16915745887002034351475883518944567198214998221214373419499) +
    (-96824403862890422932058276712182234587757995442593103229009) * X ^ 1 +
    (503844983252797470837528502548084963562855064376136786810227) * X ^ 2 +
    (-2382798511493624516680177675176011018883559732018875565761936) * X ^ 3 +
    (10223013125965829245523948751685394125642246592829054736465168) * X ^ 4 +
    (-39627501507429808811790196833806911471089677385973947886850912) * X ^ 5 +
    (137616328417704194525298358145366065885753892096244508687775525) * X ^ 6 +
    (-420617832937282719549932530428156073690217654863162183515867533) * X ^ 7 +
    (1086688077016891640040404719916952250758001709002929849819100269) * X ^ 8
  )

def recurrence1Remainder31Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-2117045900378094450302394180197976052020697874866389261529290053) +
    (1573873370402300220999391826761829897204425586926558504077729681) * X ^ 1 +
    (10644311786833732656582735778162373125475408995102187543542544923) * X ^ 2 +
    (-71136715030969184183854200060725777190148445001450823149086923021) * X ^ 3 +
    (292069722490930185310853946295842046672642764572343504310414030087) * X ^ 4 +
    (-993393455921345980841725671678556174931105337591928892889947841542) * X ^ 5 +
    (3023085324759856524499293283672137920340087897186076737631493632750) * X ^ 6 +
    (-8104447679923438559902964456472011977417072409659123493088766295176) * X ^ 7 +
    (17068731288293475113119521168870069874789814003682746242005916945360) * X ^ 8
  )

def recurrence1Remainder31Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-19928043604410636555449239072426940875229149351481373517789242548598) +
    (-13406571249791003147339517709710462822381192608530851772516857429164) * X ^ 1 +
    (16337173046674659333592019656472193136943084993896137745116502038120) * X ^ 2 +
    (788244571679145887294001151407222542857474774728122808576916171988427) * X ^ 3 +
    (-4720544453607848933345905252674414508285957488103489946389986149675376) * X ^ 4 +
    (10541615416793286959116889447018063695759759247843859465082481202079933) * X ^ 5 +
    (19057956045469880482016929997469405733565450970846524356670318413745663) * X ^ 6 +
    (-229234680572595593158202990957944906398901149263780505360321775093890590) * X ^ 7 +
    (780833008966444051047835542198098936282536197180909773443671782123198606) * X ^ 8
  )

def recurrence1Remainder31Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (-634880177846232697069663772185982670415648143436134681720696102204307272) +
    (-6527460295408561257167332988789855457353847879369243876202961901336308128) * X ^ 1 +
    (36603393159720128532642111962270836208076149013765143528862926056211777128) * X ^ 2 +
    (-92029916592950937771569915357495182546134341107195158563384457280187594141) * X ^ 3 +
    (23916344032483543070847613672697816675629296352215354705655717478907851007) * X ^ 4 +
    (834397404747305773033159661648892678823750538762615391283413824994843324864) * X ^ 5 +
    (-3996303655923177312452137471167100825147480661468764582415270062702396828521) * X ^ 6 +
    (10144526130743151480975052942590838687807536124908615956530007344433566950721) * X ^ 7 +
    (-9510009682626456726579735199708352255118508295802156374570801873286903511519) * X ^ 8
  )

def recurrence1Remainder31Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (-45620263581110809638804385783434895481376722178741641478022374645621764749733) +
    ((2 * 10 ^ 77 +
      86452492630542240220701359832941097694136397329407855152621898353506403112908)) * X ^ 1 +
    -((9 * 10 ^ 77 +
      30114323269042709597186787827597165949689489156861307830371574582153217620640)) * X ^ 2 +
    ((19 * 10 ^ 77 +
      96864106811636042452265558222841452121479111209476815590003680762080409656459)) * X ^ 3 +
    -((21 * 10 ^ 77 +
      28263304031884661937019467836098476351233112952289169889106497748167260011030)) * X ^ 4 +
    -((46 * 10 ^ 77 +
      55495353986032186065426927710087414336309004684723029863946850736938569625470)) * X ^ 5 +
    ((358 * 10 ^ 77 +
      98411322509749145087380687419441693370113656410088735179449966192125074667166)) * X ^ 6 +
    -((1328 * 10 ^ 77 +
      07489205616938214087373211656968748336618338539107970071507094374846674034578)) * X ^ 7 +
    ((3772 * 10 ^ 77 +
      97782007846935177266198251874381768322066955561437899269398642594015570946741)) * X ^ 8
  )

def recurrence1Remainder31Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((9100 * 10 ^ 77 +
      89787535213108242479439382101488926979837879483752938352754073706839987198819)) +
    ((19408 * 10 ^ 77 +
      60747609479118472499378373889364781727332852944916344459635046703292995638723)) * X ^ 1 +
    -((37373 * 10 ^ 77 +
      27068167475407120959320383631772753032800758325034742116172764465373878107207)) * X ^ 2 +
    ((65808 * 10 ^ 77 +
      37370078895186182865630996867775025095116301893879243303286625890166627309004)) * X ^ 3 +
    -((106849 * 10 ^ 77 +
      32001253622988142023115532959049080061802093752970417816761078591499250807254)) * X ^ 4 +
    ((160902 * 10 ^ 77 +
      27148332951542696197760384989426594002642638355335420759508825440104240254130)) * X ^ 5 +
    -((225681 * 10 ^ 77 +
      25567726506501385985517247895190314001236330498499045126621688603772909592417)) * X ^ 6 +
    ((295768 * 10 ^ 77 +
      66189948908515337294370596665858607544127164362644311738506511390616605453969)) * X ^ 7 +
    -((363063 * 10 ^ 77 +
      89646783321494750452325924261132158383094534561620618735540843181656110877606)) * X ^ 8
  )

def recurrence1Remainder31Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((418208 * 10 ^ 77 +
      50368466332543540512067269925867952266014135021476035233000503827107453223316)) +
    -((452682 * 10 ^ 77 +
      77477975586076434411748099016157251310647240396603582270928289374218893435263)) * X ^ 1 +
    ((460937 * 10 ^ 77 +
      76698752015643986033340566562149185287772005783886578615378058437004567684813)) * X ^ 2 +
    -((441835 * 10 ^ 77 +
      61077188996806071573938147676850018484377312384702936056805188796924819861325)) * X ^ 3 +
    ((398890 * 10 ^ 77 +
      75855121581495438948013265896228240917966746911158209976841867902727122876887)) * X ^ 4 +
    -((339247 * 10 ^ 77 +
      68588463739760834086536421430287865013236677602261259861102372066072850462997)) * X ^ 5 +
    ((271792 * 10 ^ 77 +
      19890885557877643306455097673083855955951862969115128872200019545705566982315)) * X ^ 6 +
    -((205065 * 10 ^ 77 +
      07857908575837110185319625117014694537599200934317278556929481254127853562549)) * X ^ 7 +
    ((145626 * 10 ^ 77 +
      34006383149416760999611782399304971132695187026094186416292925865657152703900)) * X ^ 8
  )

def recurrence1Remainder31Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((97253 * 10 ^ 77 +
      77515958751876262428885713982485030724452249106034199225362682938159166413016)) +
    ((61003 * 10 ^ 77 +
      84619588948366820489879908557739215404298729479391143929861637866729604457533)) * X ^ 1 +
    -((35880 * 10 ^ 77 +
      69453348029601709809758965314778462661253735268111856665578436012941567200002)) * X ^ 2 +
    ((19743 * 10 ^ 77 +
      73716123957634869376279894372047384264888664388286890466656349383544115360163)) * X ^ 3 +
    -((10132 * 10 ^ 77 +
      66923846325179505239585369117993025728288204184537341584019354554314103917757)) * X ^ 4 +
    ((4829 * 10 ^ 77 +
      45720293470433309490047398087627204637894595049763822438025225764127409906729)) * X ^ 5 +
    -((2124 * 10 ^ 77 +
      83420295296488441844831984739845110213850679632154677322289552445387763338952)) * X ^ 6 +
    ((855 * 10 ^ 77 +
      20930800323862608921055837306391440638217718883126650661010452375201449136544)) * X ^ 7 +
    -((310 * 10 ^ 77 +
      31219367880682793436916875037180352977051960182882782303518476488465295634159)) * X ^ 8
  )

def recurrence1Remainder31Block12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((98 * 10 ^ 77 +
      86169286178010552278236759819134929554734549649775519754451399698435242206457)) +
    -((26 * 10 ^ 77 +
      10151192256878161377874578099475093860301470309729828314733853290122116329096)) * X ^ 1 +
    ((4 * 10 ^ 77 +
      75416169395747393993690774587995672010918662672232166626647879630890554139506)) * X ^ 2 +
    (6807258215601181270825551708928620507941647742229886613921890657166990056625) * X ^ 3 +
    (-56773492575788127203591776336052068471315035546375162400502978977957918879915) * X ^ 4 +
    (32641422498515100281541262273026639951336885094860458705571347218406782191670) * X ^ 5 +
    (-12961974768585141306529739412325910605254911809266707173444777754199197117405) * X ^ 6 +
    (4112100615905650925761907793181318489600313256560203059785385739302444440528) * X ^ 7 +
    (-1069438292863121591341343098989279807575505500494470269216423749908517787097) * X ^ 8
  )

def recurrence1Remainder31Block13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (221316659772670166692895082049494369426799689678856502350466588757680944315) +
    (-31612871547811751919971175442334048754532200354187620055162056546536666592) * X ^ 1 +
    (611752879729334922764789269955569477349949902997553095919933524614039751) * X ^ 2 +
    (1454576979830563366719294775279603741617520000804671943305892791271946524) * X ^ 3 +
    (-601983510415873099185742587321856897532228258987522196529103207795599249) * X ^ 4 +
    (160673108225330972831596641133967268423928982157302465845839001602843914) * X ^ 5 +
    (-33159189961298257144236198994417581469091854311710197435272783921001811) * X ^ 6 +
    (5500690565123684648068027453042753689649826253269721262388770496426180) * X ^ 7 +
    (-727320140970134352554732927035915214612111696900761659515242968612036) * X ^ 8
  )

def recurrence1Remainder31Block14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    (72187319352308426801146532368161192757279536276969014179403904369732) +
    (-4218244686005705265308018284230687237289489357001229744584333300507) * X ^ 1 +
    (-139307632926777985198982076496959313080569609220227305142667906283) * X ^ 2 +
    (74195559968049977844094353834252111881072072129491686892782427928) * X ^ 3 +
    (-11000878240301108446232847583891856362587171660360346433747772014) * X ^ 4 +
    (1071177102373187841768649437842988267533738719301055727435847552) * X ^ 5 +
    (-75779327597226316549893017568008428679137405770638801204431961) * X ^ 6 +
    (3941362457426846987591807964942227553872051291430027126569177) * X ^ 7 +
    (-147335209057738889554839018861819964914468200136625830998411) * X ^ 8
  )

def recurrence1Remainder31Block15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    (3765636401631912124103489222329610653087092710226271636432) +
    (-60176317700103030329492405261393362787408546349180388892) * X ^ 1 +
    (494637248126954007030269825502921126464763316763120633) * X ^ 2 +
    (-585404634050633860856164267033391374720611073085002) * X ^ 3 +
    (-18075531155479761994337968259563696552934565603073) * X ^ 4 +
    (88688412798114701400044474593236585742109067413) * X ^ 5 +
    (33286756372807294838081351857126589748431361) * X ^ 6 +
    (-947983312731369225699789814629797199677964) * X ^ 7 +
    (2020920246644392060969107822451951528536) * X ^ 8
  )

def recurrence1Remainder31Block16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    (-1592238664499157879719509935713969035) +
    (454584863828938384243537124772738) * X ^ 1 +
    (-38542448209451443600274287315) * X ^ 2 +
    (702479133103523993168864) * X ^ 3 +
    (-1620196522930594940) * X ^ 4 +
    (140328271398) * X ^ 5 +
    (-71) * X ^ 6
  )

def recurrence1Remainder31 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder31Block0 +
  recurrence1Remainder31Block1 +
  recurrence1Remainder31Block2 +
  recurrence1Remainder31Block3 +
  recurrence1Remainder31Block4 +
  recurrence1Remainder31Block5 +
  recurrence1Remainder31Block6 +
  recurrence1Remainder31Block7 +
  recurrence1Remainder31Block8 +
  recurrence1Remainder31Block9 +
  recurrence1Remainder31Block10 +
  recurrence1Remainder31Block11 +
  recurrence1Remainder31Block12 +
  recurrence1Remainder31Block13 +
  recurrence1Remainder31Block14 +
  recurrence1Remainder31Block15 +
  recurrence1Remainder31Block16

def recurrence1Remainder32Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (20566) * X ^ 2 +
    (467452502) * X ^ 3 +
    (-248803518198) * X ^ 4 +
    (383227126470131) * X ^ 5 +
    (-152822662923162884) * X ^ 6 +
    (42180852282813951032) * X ^ 7 +
    (-7051644585908704055280) * X ^ 8
  )

def recurrence1Remainder32Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (789505055030491628391075) +
    (-59986525779113592452228114) * X ^ 1 +
    (3140523831275756399695569367) * X ^ 2 +
    (-114649868328970443430888145935) * X ^ 3 +
    (3145208853554043704377412826823) * X ^ 4 +
    (-95254075572483322850249961335294) * X ^ 5 +
    (4707286715224831131980976760272090) * X ^ 6 +
    (-252119760709282965148060859490098674) * X ^ 7 +
    (10920773607153928613786783012238872921) * X ^ 8
  )

def recurrence1Remainder32Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-374755433938771058464397696038142186056) +
    (10423139299556869835388904607584062679111) * X ^ 1 +
    (-236508744925100315692077438653052297791806) * X ^ 2 +
    (4264782476520433050173386942964682535047038) * X ^ 3 +
    (-55256619995110073203406178869402808396548740) * X ^ 4 +
    (285706806254928866062310198554674176338128828) * X ^ 5 +
    (9151218683896100753611859546553688315536346346) * X ^ 6 +
    (-360723793542344848926346348860010605221468898151) * X ^ 7 +
    (7988566775046323816950452536667043821428643273571) * X ^ 8
  )

def recurrence1Remainder32Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-135610457529676213927524080412967938276908000989499) +
    (1912098641510585058099084468722416136697822198628623) * X ^ 1 +
    (-23183387137118427190312349102213378182877449677860270) * X ^ 2 +
    (246329617178149273935393622793688400091367824947689466) * X ^ 3 +
    (-2321078854207125281928321165528633903884832772129450505) * X ^ 4 +
    (19554454400437866274729702375867507229487690725880338625) * X ^ 5 +
    (-148173271675304899089185520264698955187655856836240781529) * X ^ 6 +
    (1014337899014932756179294601359552920296855999551578100641) * X ^ 7 +
    (-6293016267641226930816983777632313952601640526445380151277) * X ^ 8
  )

def recurrence1Remainder32Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (35453047198090537082304117523098262290953781713141305831790) +
    (-181499756823876778304060593417382305756426614026496891389935) * X ^ 1 +
    (843755290301089933115552025148303090521645311900760275574478) * X ^ 2 +
    (-3552824034029471684453840394271692866755848034950107359651480) * X ^ 3 +
    (13478123055651230228272777873715663363791103402982773920944516) * X ^ 4 +
    (-45582171189210250545017707180304950371503361684194561569665487) * X ^ 5 +
    (134429195558020180454399136591174639861549207080127987930005697) * X ^ 6 +
    (-328003938045700375173751495721136104332755576834768852631221653) * X ^ 7 +
    (557924028055441474238630776968822342538856427701636338978197629) * X ^ 8
  )

def recurrence1Remainder32Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (4443215559487839326439914202816308765887547512828767566577894) +
    (-5190470250224262508551271917117761513256090003934359515937713572) * X ^ 1 +
    (28122045346581622831222804024479730765729259546789372377157070970) * X ^ 2 +
    (-106788653096648679148087335350647801913263895572835705266931236346) * X ^ 3 +
    (342145434390218184106531767714388496739031953827924299460661589676) * X ^ 4 +
    (-987235433873104535656362726172641254794587115864251552945804076105) * X ^ 5 +
    (2561901456258136949894791767672983359060878522867259312939165863923) * X ^ 6 +
    (-5457811960018399890535577784772290315877026020624914203761494109784) * X ^ 7 +
    (7209866222568054868512328548494855815959045172876543998169252113244) * X ^ 8
  )

def recurrence1Remainder32Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (1724737831226548170000465792846091900982352387032329614998427719216) +
    (-13372367869848666839347703572120985123394727185653966147681404955432) * X ^ 1 +
    (-157339896768072354933942554862976313707979773239351019084456150604421) * X ^ 2 +
    (1159564890418055661323514297762148901433296114321838721244994297797577) * X ^ 3 +
    (-3054243963534027327407222692196537649633065226852682894389216541526680) * X ^ 4 +
    (-2858937352163103397112804505247217042729858885502902041365725400988923) * X ^ 5 +
    (54534678257021364220065665885601967779032608595213555231118776038064568) * X ^ 6 +
    (-205316457637001890020694013735680233966638042633322734632182196570211985) * X ^ 7 +
    (230619480194053390530218647033603763596156082753043918233161797927318675) * X ^ 8
  )

def recurrence1Remainder32Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (1433322050784409541498630282889013093835565987124507123047930319437077533) +
    (-9005447893521413281801840670945787098264834803571205293176637274299607663) * X ^ 1 +
    (24187446152476167709049666999809968464537768999676262503271693769681195773) * X ^ 2 +
    (-12191726704762365575889116972647849103155504577598226140509866060555820458) * X ^ 3 +
    (-191782875446448841531236806362122177755799580882564598469929967208992738766) * X ^ 4 +
    (974827413972977330840741571666419461094606328959665463097412149691014151041) * X ^ 5 +
    (-2555352528096015106219807884752781334469308302588552952229209584596469340131) * X ^ 6 +
    (2642679044419317102424322353002264157586752254742401646693919167246904528533) * X ^ 7 +
    (10299600007772281310642717885390182951937129250880590873228342112801682245293) * X ^ 8
  )

def recurrence1Remainder32Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (-68214330578893228553685928493216088652583932457539998082710688173398952810092) +
    ((2 * 10 ^ 77 +
      24093069522919787142159639007142043033037572457611885946470063852114368708480)) * X ^ 1 +
    -((4 * 10 ^ 77 +
      83806125807736123651960748029311842457560255736945738204410330523200568952260)) * X ^ 2 +
    ((5 * 10 ^ 77 +
      23991167770562787171192347484713869695582412439151555427480508975751709820955)) * X ^ 3 +
    ((10 * 10 ^ 77 +
      71666725440105407199975529011841541270732034051950886271738620517456422152047)) * X ^ 4 +
    -((84 * 10 ^ 77 +
      19336145195486471546444844639582432741639081154222478481994343614119951929873)) * X ^ 5 +
    ((310 * 10 ^ 77 +
      70586028575533537966814752107681158725330531559295349324840267049168204212129)) * X ^ 6 +
    -((877 * 10 ^ 77 +
      35276521230941836863563003666073305004776276234976737873801757428613106117883)) * X ^ 7 +
    ((2099 * 10 ^ 77 +
      84150859919551749454457773268112361470632809987902168684317820942572855625756)) * X ^ 8
  )

def recurrence1Remainder32Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((4438 * 10 ^ 77 +
      13185349991263522080593701675830045279755086470509237212549004952614599067836)) +
    ((8461 * 10 ^ 77 +
      97087825182960830123775269160213699923146932640641182513694132981459534339840)) * X ^ 1 +
    -((14742 * 10 ^ 77 +
      19308947706039837280037719223729477628176833507078285282096993655663177966866)) * X ^ 2 +
    ((23666 * 10 ^ 77 +
      61704576729176633787840805536982086739222216021383988402340329014646659614868)) * X ^ 3 +
    -((35217 * 10 ^ 77 +
      90491252965591377213287177576881910496550810869277228925378637784289444061185)) * X ^ 4 +
    ((48789 * 10 ^ 77 +
      58677748172552623183993860838773198665262867925026377947262128756387467729355)) * X ^ 5 +
    -((63132 * 10 ^ 77 +
      23188627745520386782674434168398018887582965950172115711016381395623210886699)) * X ^ 6 +
    ((76495 * 10 ^ 77 +
      76334355262921675886643795518394449271592980846168144490216083156286725179810)) * X ^ 7 +
    -((86966 * 10 ^ 77 +
      60169749247515814676320711805214435858709310274527504992268040365030782945048)) * X ^ 8
  )

def recurrence1Remainder32Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((92915 * 10 ^ 77 +
      04956220607486260275725415665031661219655566975464158435763998554034408554480)) +
    -((93409 * 10 ^ 77 +
      50956749192471828259133872859662088215163160511923113444117696730716028180224)) * X ^ 1 +
    ((88453 * 10 ^ 77 +
      16784338692901094669615449669766070519250450292523084406166617076303714279159)) * X ^ 2 +
    -((78961 * 10 ^ 77 +
      16109931799268872997803709586067011435150914429479252792584491414568389724059)) * X ^ 3 +
    ((66494 * 10 ^ 77 +
      20612699135338432189625888500495771915866405248649841807175754422661512499891)) * X ^ 4 +
    -((52852 * 10 ^ 77 +
      03929474997527372842096920042464534806899023615255895802918082215516192145774)) * X ^ 5 +
    ((39668 * 10 ^ 77 +
      05692998762561882331514688247223528604670263469644760728124408662115906623395)) * X ^ 6 +
    -((28124 * 10 ^ 77 +
      16657068056806788737292238830452277858362790864191804878612755888438156771610)) * X ^ 7 +
    ((18841 * 10 ^ 77 +
      16403729949346202045504220818498858162623313256366101561117504765028790497700)) * X ^ 8
  )

def recurrence1Remainder32Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((11929 * 10 ^ 77 +
      73960328987229107472584980350730821716258482294929301075098159562646123036503)) +
    ((7140 * 10 ^ 77 +
      57692066029865589604113091419977440487922673444086032763502423849396950279416)) * X ^ 1 +
    -((4040 * 10 ^ 77 +
      87757654661435721225872224038364036391109826680982581666362786191551875430469)) * X ^ 2 +
    ((2162 * 10 ^ 77 +
      17583139531823907399361439529348444260659020277621502005525504665463291009353)) * X ^ 3 +
    -((1093 * 10 ^ 77 +
      89106450154930183536201085638951475155070008832443978726648528516074363443685)) * X ^ 4 +
    ((523 * 10 ^ 77 +
      19797990311232815505304664380859811791115565533207489647734100299043137156138)) * X ^ 5 +
    -((236 * 10 ^ 77 +
      50089181178437391060507335313003191109706233441566022648438160414367711400991)) * X ^ 6 +
    ((100 * 10 ^ 77 +
      98042103165083692827076657670753797373804887895297423411954063969389581151368)) * X ^ 7 +
    -((40 * 10 ^ 77 +
      69179436436706490024028444350089890583884145684810998237906683449509258064080)) * X ^ 8
  )

def recurrence1Remainder32Block12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((15 * 10 ^ 77 +
      45604664960767846161518367809748171508613227035233358423742338650833991643039)) +
    -((5 * 10 ^ 77 +
      52409062841964684254711041690876799138153832260128413836379376381369612946193)) * X ^ 1 +
    ((1 * 10 ^ 77 +
      85352560904930368592815932380381576355851551316029050931749931300118178605900)) * X ^ 2 +
    (-58215128906236695980483756084115106517291392548948680941089857212726578660303) * X ^ 3 +
    (17052061253393681835039412989419604298863122129266837879542283424132438243727) * X ^ 4 +
    (-4637206126802533542607293997760943851314674432049460003414568296716125593865) * X ^ 5 +
    (1164299929306790927109332300531702373845252155692296120035775140746680497093) * X ^ 6 +
    (-268053974593728480433715158939486055239104791127235534198899486263968825702) * X ^ 7 +
    (56098287185765485529213994082243262581584135657387543776870949233940638251) * X ^ 8
  )

def recurrence1Remainder32Block13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (-10549445995579726899352496198976701305591064216596749616103919801888854209) +
    (1753428219162708042442929021584283905383289737567132038310659234492806248) * X ^ 1 +
    (-250847183531193488012110421608822055089562893084198397695106008999443863) * X ^ 2 +
    (29347117917665943159179787044301639136720281522779247972409835369510261) * X ^ 3 +
    (-2446500681235254820503020803171739951147113076143029101929298950265299) * X ^ 4 +
    (53313951655807229356091123970641619108721066463092394318897182995114) * X ^ 5 +
    (27739334662807329564267888375865993661995166764506857963097879248305) * X ^ 6 +
    (-6572864111312376157183801082731963573243496346867076686409667113807) * X ^ 7 +
    (934681107860434837000953261878398686818274156008261289171673950871) * X ^ 8
  )

def recurrence1Remainder32Block14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    (-98631113392338475087316148944972009748966393538867971507679983646) +
    (8070972681488537876096594324281849283907104357091359639643098128) * X ^ 1 +
    (-513168991194838191484932827443203554829686858690826486174294323) * X ^ 2 +
    (24887956221358816884567392188078705225648221779419059150477356) * X ^ 3 +
    (-888796707805812581979468384138402810818976447442320188418243) * X ^ 4 +
    (22102615787889023365940715477631828559349160837530666583016) * X ^ 5 +
    (-349215718451208953719573869056996934238274938879200054710) * X ^ 6 +
    (2892042315176818529738807354915088841226469430894035494) * X ^ 7 +
    (-3984496954486262589407169793306672512000502855155540) * X ^ 8
  )

def recurrence1Remainder32Block15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    (-103101870016126360746150005911720546492853629670543) +
    (536387544838059037062928334334550440874733909731) * X ^ 1 +
    (100574681677421432279576674671370954256997612) * X ^ 2 +
    (-5622196839184792936462092408424956837028696) * X ^ 3 +
    (12655902568973616262798152588184214229432) * X ^ 4 +
    (-10521605408537418559835170422339834894) * X ^ 5 +
    (3222330311416572061294843994497685) * X ^ 6 +
    (-301677638040674755667972554263) * X ^ 7 +
    (6373118709373069341699962) * X ^ 8
  )

def recurrence1Remainder32Block16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    (-18614232357864327257) +
    (2740936995785) * X ^ 1 +
    (-2406) * X ^ 2
  )

def recurrence1Remainder32 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder32Block0 +
  recurrence1Remainder32Block1 +
  recurrence1Remainder32Block2 +
  recurrence1Remainder32Block3 +
  recurrence1Remainder32Block4 +
  recurrence1Remainder32Block5 +
  recurrence1Remainder32Block6 +
  recurrence1Remainder32Block7 +
  recurrence1Remainder32Block8 +
  recurrence1Remainder32Block9 +
  recurrence1Remainder32Block10 +
  recurrence1Remainder32Block11 +
  recurrence1Remainder32Block12 +
  recurrence1Remainder32Block13 +
  recurrence1Remainder32Block14 +
  recurrence1Remainder32Block15 +
  recurrence1Remainder32Block16

def recurrence1Remainder33Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (480) * X ^ 1 +
    (2101370) * X ^ 2 +
    (6741833232) * X ^ 3 +
    (1007725038232) * X ^ 4 +
    (1514210590514436) * X ^ 5 +
    (-252661954362651579) * X ^ 6 +
    (70580976386535404667) * X ^ 7 +
    (-7770078999813774941161) * X ^ 8
  )

def recurrence1Remainder33Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (665619660847415358333691) +
    (-29151787061008139356079371) * X ^ 1 +
    (431573081168452503245082016) * X ^ 2 +
    (30765060231123124340888747962) * X ^ 3 +
    (-420465597786790140177689853690) * X ^ 4 +
    (-231635597859453393669645890767315) * X ^ 5 +
    (25672040339073566305162429711917504) * X ^ 6 +
    (-1592649904244241948776821944667945208) * X ^ 7 +
    (70157524981800905948027975244144740677) * X ^ 8
  )

def recurrence1Remainder33Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-2364120591100822355029001163835195851320) +
    (62761081465454613200917170451308753755965) * X ^ 1 +
    (-1318506620132714491021676215087936613503383) * X ^ 2 +
    (21363805450566397992596429376467518622113721) * X ^ 3 +
    (-239591519486512844355524506906757411025312820) * X ^ 4 +
    (838631976014592192045689475297883405338670433) * X ^ 5 +
    (39323680664207917462371268634588994878314588210) * X ^ 6 +
    (-1255110642812999386812854618143537947008519295245) * X ^ 7 +
    (24053754625448439086729037783714806004867064042388) * X ^ 8
  )

def recurrence1Remainder33Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-358260090509608225437473550360386781388050237382264) +
    (4458993574907075907833466976323982545417966441849142) * X ^ 1 +
    (-47902052794745215049494643059608532424443234199200138) * X ^ 2 +
    (452230724637998595531068226168393585178727164709934656) * X ^ 3 +
    (-3794690300542582961642781778549697535408669518720738785) * X ^ 4 +
    (28519195587756404058556484972768149611446839249356728281) * X ^ 5 +
    (-193006169853746414143059339818637808762978975764455612203) * X ^ 6 +
    (1180512781369252764224539615477987005850127381835100835434) * X ^ 7 +
    (-6540297908704906261785640102274014945053908943605902258910) * X ^ 8
  )

def recurrence1Remainder33Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (32845376198865990567951542846521074366912829360068369899529) +
    (-149370660360551090862289677618089905267374498746780124414367) * X ^ 1 +
    (613047825618599045320058133249562112630192030938648579518817) * X ^ 2 +
    (-2254365055564034132731832311863235427197643124596087865032902) * X ^ 3 +
    (7321318705668383896097494672479343144359967198655430342717486) * X ^ 4 +
    (-20359196587192512199618778289586529741252603082861773640976589) * X ^ 5 +
    (44716004517758441781127530550017635633020047704487393900203363) * X ^ 6 +
    (-54547649269116285811940460593138403304655554475696782746415836) * X ^ 7 +
    (-125509718208091748382174758817225511947054422065220370360597262) * X ^ 8
  )

def recurrence1Remainder33Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (1215361719188425093232555521244922693523846897761855976385158596) +
    (-5541279931949491542041626920062413590725488757902183037311898975) * X ^ 1 +
    (19436837625481187499608194721315137768824828232880362815327875540) * X ^ 2 +
    (-58004990475890653255376363542401572493144229521007025661597927553) * X ^ 3 +
    (153900138161638371624835943034609193562584588628438062946369208590) * X ^ 4 +
    (-369949353922945682441428217191353664500854628602529259821808490438) * X ^ 5 +
    (786531198946204696287853158862770410673610041919757365882480319893) * X ^ 6 +
    (-1315148907904428959344457482256885861297507477213747480995800745496) * X ^ 7 +
    (1119265223719573832872973365455181888551819724380791786529972617873) * X ^ 8
  )

def recurrence1Remainder33Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (1103333684396259870377688427485826900794632598081214990524829572842) +
    (1879283894331569741651940079644695979141359000303877435700869098121) * X ^ 1 +
    (-55916938128361122720655140509859282882931568761100019509452561234930) * X ^ 2 +
    (237409309822331554824686877050604264611793171567334358766319913269188) * X ^ 3 +
    (-213809508961350916516566904523070525246423816908895380968995947186338) * X ^ 4 +
    (-2435613045093290359826760836596567532184760578143784772131849034201698) * X ^ 5 +
    (13669025606547521390174941188337277461436254658068376501898396076304454) * X ^ 6 +
    (-29337314899757779683220696984335609046041918345516209208311730243348620) * X ^ 7 +
    (-36308947584604616756602443827076121828667671223942697206251844585543158) * X ^ 8
  )

def recurrence1Remainder33Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (497066274580660981369955743351611388439772409469801925676732534327609626) +
    (-1770530895444771418085531175747306495574764841097798966157168987918658459) * X ^ 1 +
    (2467981732566273496085035602001082015752261480043597428754637415453115977) * X ^ 2 +
    (7241357216704572356197710263676729547799881075345243555549121601273000653) * X ^ 3 +
    (-56013296515130011635859672204617785145896963808738077525612998095820173738) * X ^ 4 +
    (178657839627351753032682798882747466385046668110767113526829669925648872946) * X ^ 5 +
    (-282998781924408871682093359956131542837394822113871837939698690563478178401) * X ^ 6 +
    (-296167432209641770047161144972637366501188852007704895018441642063244091365) * X ^ 7 +
    (3663548145118652539719394997134023618733741136223405375632738092129050866093) * X ^ 8
  )

def recurrence1Remainder33Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (-13883285238043731030330790713940511319626048720629589588888271371062127741683) +
    (33601173022606147947843767961852344442669454883776315937090545525310171456890) * X ^ 1 +
    (-47370726090936146674134016235557954779411823888514787882540198733169481900505) * X ^ 2 +
    (-26247249349164207924627981058158461225611093231614953451919208579934556741577) * X ^ 3 +
    ((4 * 10 ^ 77 +
      38580916870627634708516910743861745028824489961175600550351050985118436273973)) * X ^ 4 +
    -((17 * 10 ^ 77 +
      90702669589498380276133033847446918678790611709121963201680665644583381614252)) * X ^ 5 +
    ((52 * 10 ^ 77 +
      79900888340514526258673613044406660446078556554308736616617662304479479782250)) * X ^ 6 +
    -((129 * 10 ^ 77 +
      43388582705179224593434311536208709660555789228417679677276709994176807432123)) * X ^ 7 +
    ((277 * 10 ^ 77 +
      53456106047690258437353814777402512605564537582046174681702184106457413755760)) * X ^ 8
  )

def recurrence1Remainder33Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((533 * 10 ^ 77 +
      68667115558757960545479947487715642796348842243313869284298765413118950184842)) +
    ((933 * 10 ^ 77 +
      83424914547747692476729917418390690293248150863797874617264376888690357768491)) * X ^ 1 +
    -((1500 * 10 ^ 77 +
      84260214766007516029025019068720450815586742536111508786637735926736770902335)) * X ^ 2 +
    ((2229 * 10 ^ 77 +
      89837446311333400278246490275490085439078114621156373188308191957210496629154)) * X ^ 3 +
    -((3077 * 10 ^ 77 +
      09085873962394517062641398577928956726232725723719748535595804909727287053652)) * X ^ 4 +
    ((3957 * 10 ^ 77 +
      33492136647448009893839264751098020944987601677521124506095793071558236422206)) * X ^ 5 +
    -((4755 * 10 ^ 77 +
      65040336437609330922112075418285296579677968383349922242309221418675982505726)) * X ^ 6 +
    ((5350 * 10 ^ 77 +
      94320963488480646638594542506252603333993793146798225841484164917439507800935)) * X ^ 7 +
    -((5645 * 10 ^ 77 +
      80847864190690510083077567293854758366535306520954639804725071428367092560777)) * X ^ 8
  )

def recurrence1Remainder33Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((5592 * 10 ^ 77 +
      34950371663278726519594183031856054849549265228373579997183202001302428425105)) +
    -((5204 * 10 ^ 77 +
      69192440245729891983109826167165713221345673216761280993553561034618732248381)) * X ^ 1 +
    ((4553 * 10 ^ 77 +
      77001687927812796731397167037375330900616752007443513407796330531380045117922)) * X ^ 2 +
    -((3746 * 10 ^ 77 +
      80365731299261936766892806590124135272301940041866259433318211287855773886541)) * X ^ 3 +
    ((2899 * 10 ^ 77 +
      39208861927255211693879492053562977904542102246011966678349916340599005430064)) * X ^ 4 +
    -((2109 * 10 ^ 77 +
      89084817149769175338205653853808985071008687124120075140711826138067180319495)) * X ^ 5 +
    ((1443 * 10 ^ 77 +
      37947275297024171563371299886010988785669209358853038954413551689331821253507)) * X ^ 6 +
    -((927 * 10 ^ 77 +
      76204514688901997793636199505446776353229134476728368971836344352104289483319)) * X ^ 7 +
    ((559 * 10 ^ 77 +
      88438400487964921127558627460459444195679199005768810394975681682793531194724)) * X ^ 8
  )

def recurrence1Remainder33Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((316 * 10 ^ 77 +
      90456381798051743178479959276351563307044660311974116271001215314755904898043)) +
    ((168 * 10 ^ 77 +
      02255930595853467055537199043237604617995086573765094092148094341971452703797)) * X ^ 1 +
    -((83 * 10 ^ 77 +
      31289630849637918252301393369488890104479012971264621242663842813454319699453)) * X ^ 2 +
    ((38 * 10 ^ 77 +
      55516665802135723426507085892522511470511019193367561640069117603190196179010)) * X ^ 3 +
    -((16 * 10 ^ 77 +
      61015699297761118541732804207642645869441274853708845063294583493587360428220)) * X ^ 4 +
    ((6 * 10 ^ 77 +
      64018609132041892649150005780483092285101251834636417139194287863524890218134)) * X ^ 5 +
    -((2 * 10 ^ 77 +
      45286872579494794711164493822023948181353957641425698090298702202763332428513)) * X ^ 6 +
    (83252567572990935712375096305050418191634016510237177049359517726662164307610) * X ^ 7 +
    (-25756084359140767751522153471209456351734930541495077954072566961230423326291) * X ^ 8
  )

def recurrence1Remainder33Block12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    (7175779352112322493007564405383946748036764751487537894299807560164342323475) +
    (-1764284169942141516794254625106998496771725351030659813117162976573989894870) * X ^ 1 +
    (367918324021014412159551117731191087868242145449506185478836464720893206693) * X ^ 2 +
    (-58770610913316811161165320622211908368657604232622606418763067929277288747) * X ^ 3 +
    (4302808007910672461271958621805881394611136629638456596163558895095506436) * X ^ 4 +
    (1433357835678070583064988300991178019401959915876652541887820763526814519) * X ^ 5 +
    (-817802592660912823625378828639395904673124044039367492061682729383192345) * X ^ 6 +
    (256830603734648461069625921244941520037381800577978632773618583405051344) * X ^ 7 +
    (-62146558126475951742091459752987887047106399082475107324835575852357657) * X ^ 8
  )

def recurrence1Remainder33Block13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (12478290413189209613386529064564346453881849061384461516582119428712943) +
    (-2130607953765346486575979173587208401909940944070864743814160704988401) * X ^ 1 +
    (311562609388111263872074625058641185381641076702746853194821516905497) * X ^ 2 +
    (-38960786157044998051481637794162861979218679962776265995678533141867) * X ^ 3 +
    (4136596077373626026460261570569508027070071107107547736180324465103) * X ^ 4 +
    (-368471479737378690063548259471548224159713335063659997557754145579) * X ^ 5 +
    (27074914537599357484718731902120870451633524112286446682375692616) * X ^ 6 +
    (-1604070201724773159251597259559365940215432279655332514103025681) * X ^ 7 +
    (74319461457584823064126825817146334370811950632684689276279227) * X ^ 8
  )

def recurrence1Remainder33Block14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    (-2583260145960009593741024175832818295951192540568447153431089) +
    (63517628334480963461838776082852917472358213369521692408986) * X ^ 1 +
    (-1008134748447768781584022993480510525609644882614813968103) * X ^ 2 +
    (8589632255858115315314958759907205405785857325245156640) * X ^ 3 +
    (-15073910588387535089979214015962316457358706139149486) * X ^ 4 +
    (-291052500416767275599138103498844807961572638140070) * X ^ 5 +
    (1674129651746526608831712981374666865668376926300) * X ^ 6 +
    (-184976099149246181142891522461286707584146859) * X ^ 7 +
    (-16928129819723046431748708882310310971802853) * X ^ 8
  )

def recurrence1Remainder33Block15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    (41524351678912399764784036074579321890738) +
    (-37355076014988173036934365236226010977) * X ^ 1 +
    (12630803349999293373479468844937253) * X ^ 2 +
    (-1353108127151867760064049878816) * X ^ 3 +
    (34612852489926112713304677) * X ^ 4 +
    (-134652616023164963796) * X ^ 5 +
    (34032965680161) * X ^ 6 +
    (-51783) * X ^ 7
  )

def recurrence1Remainder33 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder33Block0 +
  recurrence1Remainder33Block1 +
  recurrence1Remainder33Block2 +
  recurrence1Remainder33Block3 +
  recurrence1Remainder33Block4 +
  recurrence1Remainder33Block5 +
  recurrence1Remainder33Block6 +
  recurrence1Remainder33Block7 +
  recurrence1Remainder33Block8 +
  recurrence1Remainder33Block9 +
  recurrence1Remainder33Block10 +
  recurrence1Remainder33Block11 +
  recurrence1Remainder33Block12 +
  recurrence1Remainder33Block13 +
  recurrence1Remainder33Block14 +
  recurrence1Remainder33Block15

def recurrence1Remainder34Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (-488) * X ^ 1 +
    (79908936) * X ^ 2 +
    (-54171772584) * X ^ 3 +
    (74645004683336) * X ^ 4 +
    (-29051618894656499) * X ^ 5 +
    (7886790788452359315) * X ^ 6 +
    (-1278370368188845513764) * X ^ 7 +
    (140987840827161338457851) * X ^ 8
  )

def recurrence1Remainder34Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-10701779933849849433844089) +
    (588152189587661323715172081) * X ^ 1 +
    (-24167814127891687580020207335) * X ^ 2 +
    (729195980181088218206280942700) * X ^ 3 +
    (-8895471790438980058846996164913) * X ^ 4 +
    (-882612127378855411361653196714648) * X ^ 5 +
    (89365878071942030982913958852886304) * X ^ 6 +
    (-4923582587274649083139695798829936769) * X ^ 7 +
    (193360427385813188975621594468990858686) * X ^ 8
  )

def recurrence1Remainder34Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-5788532679887554975261205198967747686851) +
    (135288248224309717839398853453681221533696) * X ^ 1 +
    (-2462609013470166402268531714867748618199639) * X ^ 2 +
    (33339758442488426345554443264033565017930115) * X ^ 3 +
    (-270679302557652162589462507020207511690718005) * X ^ 4 +
    (-1008818495035685879478047562937998290862155503) * X ^ 5 +
    (87859518738094204518914861028615064599069473206) * X ^ 6 +
    (-1996446506939477995085583788522015464054736054877) * X ^ 7 +
    (32007005156281181505856727509883767105293103004514) * X ^ 8
  )

def recurrence1Remainder34Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-414475844456614144844151244654497319796243288778674) +
    (4553400933006248078802631154823702817095792105900271) * X ^ 1 +
    (-43490965361797663125814311585276534845596882357840770) * X ^ 2 +
    (366411820327147359441537506283766953887904168172066702) * X ^ 3 +
    (-2748502211711448991639651408908403456731970402167966495) * X ^ 4 +
    (18470328906533137619902866800115673246183364037582400911) * X ^ 5 +
    (-111648682526514395867932171694428172751902103118003413560) * X ^ 6 +
    (608432329238316096883754444681345561559019896743515021197) * X ^ 7 +
    (-2990695177461363061406833255061234766763411781951336165514) * X ^ 8
  )

def recurrence1Remainder34Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (13237718815493998019899288784617610290798803012441576727343) +
    (-52502605798787872119996775014233460522634368465938442985043) * X ^ 1 +
    (184579337456064638954568715230795236941493505519635632580955) * X ^ 2 +
    (-562236680128760107962573419031430712207619710315337358381305) * X ^ 3 +
    (1406307149455739623594356861532069650456895070659381148711193) * X ^ 4 +
    (-2423850189762669748208799419426172192321523993140498066104006) * X ^ 5 +
    (-197336827839669322632473451657661860781238967613539597953615) * X ^ 6 +
    (24854031952164914996894325056269314301931991893396923723541266) * X ^ 7 +
    (-138215545453863210538475321355045517286365246515311416313462181) * X ^ 8
  )

def recurrence1Remainder34Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (542576334946524184941790668853533285102927230254261096629654661) +
    (-1755657688136356897476181133016516604599131969331912417823621915) * X ^ 1 +
    (4824953892101361868840861253802219905285789358070456586664162781) * X ^ 2 +
    (-11188907154916730751431668524239029812334343868615229025696267272) * X ^ 3 +
    (22159876195200541825288614976241194304914096854983463400518814819) * X ^ 4 +
    (-43878357774793283803705695084308372379342153863154742382676829337) * X ^ 5 +
    (116168706880217995187833923198595633714237637222029887934310148860) * X ^ 6 +
    (-331531685124414616494006930352859635083193832697486716593344284348) * X ^ 7 +
    (416781706939311167391295573343303108140942582076923175022422653348) * X ^ 8
  )

def recurrence1Remainder34Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (2288057942395516301874537037127348688860236592066239956523068698194) +
    (-15027005393041491111291775726982408973660731111581889612795188198276) * X ^ 1 +
    (31205787281616005358739491370661912562932163198191396863724752762504) * X ^ 2 +
    (70824160951855985857684626573077506889865415795629591025559933421298) * X ^ 3 +
    (-704329761420437485860504450663813125601364110836143296241149336499616) * X ^ 4 +
    (2096673518452005734254197699408252886561028548057257693744437477509923) * X ^ 5 +
    (-429095125300578788538477178154569570773685060326131013651589371659683) * X ^ 6 +
    (-22492281016135882505333965254250250313578373468918714135682932527214861) * X ^ 7 +
    (101558558039385865222836294369420977249002541350024726686687301932041169) * X ^ 8
  )

def recurrence1Remainder34Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (-198652577094721135931073178264219316140899172164130278500653729568501592) +
    (-176565239946859853473116379656727546168794978080509620418351549224155658) * X ^ 1 +
    (2702953007588566631629174960270157122332606142430035329079709240392592458) * X ^ 2 +
    (-10063842118408960246637724608263283382533914182735720419176302758058387438) * X ^ 3 +
    (19456360616319541174764935443622590468639352927797789194888322544251300231) * X ^ 4 +
    (1922214155732299846269579554624683053779207647506245495350597584069315180) * X ^ 5 +
    (-168939163095657195668981069001406276089211626802206649683371629930986218430) * X ^ 6 +
    (722936546298955043341803801756707295402481722750762138409272635463114366872) * X ^ 7 +
    (-1882498264228494952716897055549192866735040549568852464851571751607254133648) * X ^ 8
  )

def recurrence1Remainder34Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (2993533819118038278918281363506249228537160055307838046960865932584877026862) +
    (-8232324130292502960379709079989235617404803803740994462067480843269586572) * X ^ 1 +
    (-20022265532399621233984515829052094075829741564337127897599399293694349930041) * X ^ 2 +
    (88413396433040341167382275939927070307274891756469640623047195629519480931904) * X ^ 3 +
    -((2 * 10 ^ 77 +
      67523213229486000588140745357639417363400005006489730779474069838766336181069)) * X ^ 4 +
    ((6 * 10 ^ 77 +
      62566220540898441314124627966305086727507212463405811337169716214565403849511)) * X ^ 5 +
    -((14 * 10 ^ 77 +
      24558960722572213083076822628651932983979906175362937045217674479908435327793)) * X ^ 6 +
    ((27 * 10 ^ 77 +
      34385496769727566161581142791822932842932319131230956667858814263202751532890)) * X ^ 7 +
    -((47 * 10 ^ 77 +
      61067689242154024196020089052684996121630353982565142785233562563126702221069)) * X ^ 8
  )

def recurrence1Remainder34Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    ((75 * 10 ^ 77 +
      97113212604784453966461208054289680894457147649477622894193858695088995530860)) +
    -((111 * 10 ^ 77 +
      87903027318136317892063105151494098427299971270368139630649483172552208778120)) * X ^ 1 +
    ((152 * 10 ^ 77 +
      83629782885341592599066200522128164017201648705113795779833317934912873796661)) * X ^ 2 +
    -((194 * 10 ^ 77 +
      42946024757985943605790594512323681137252438779763104278384719484780488590953)) * X ^ 3 +
    ((231 * 10 ^ 77 +
      02762536526530175042687455315692981900230669699816352895023190744212553846896)) * X ^ 4 +
    -((257 * 10 ^ 77 +
      02444383954427859365006550288294893519496392718208009886080739156081891640020)) * X ^ 5 +
    ((268 * 10 ^ 77 +
      24888610366718263831293466549513020610567578482050277295338704570109519554635)) * X ^ 6 +
    -((263 * 10 ^ 77 +
      05462293125612643666967621719007779474712200568671476586209363934903873224876)) * X ^ 7 +
    ((242 * 10 ^ 77 +
      69882080023183135037612333027384563202292542989885251222176691684716872086862)) * X ^ 8
  )

def recurrence1Remainder34Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((210 * 10 ^ 77 +
      89691496150868430004524959658346988303085720770418499213225587943674114347325)) +
    ((172 * 10 ^ 77 +
      75530640114236332374562784641045449023565067420300617594329962760964940673928)) * X ^ 1 +
    -((133 * 10 ^ 77 +
      48934219073107537917657924673541044166478524743153344467397622935895465968103)) * X ^ 2 +
    ((97 * 10 ^ 77 +
      34895008149408062168356571431319160608670726118985984697123650828547752018559)) * X ^ 3 +
    -((67 * 10 ^ 77 +
      02234754006282755541930446584470691098991528066949365306902317341463337966194)) * X ^ 4 +
    ((43 * 10 ^ 77 +
      56728360579080087452820107525544644139704221831271942433855889810419879884016)) * X ^ 5 +
    -((26 * 10 ^ 77 +
      73689830972626075423450472368080268086739992817154259640557109519060905273751)) * X ^ 6 +
    ((15 * 10 ^ 77 +
      48565281952401353923621140015727192261910648679321021515264273411052448818224)) * X ^ 7 +
    -((8 * 10 ^ 77 +
      45994595728345182596141854462786209664878600017983372710734323642311215374515)) * X ^ 8
  )

def recurrence1Remainder34Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((4 * 10 ^ 77 +
      35575048336836472621610767820516862020740232837272957862852338290272287766724)) +
    -((2 * 10 ^ 77 +
      11121967249118397836152595743629594069474390351770707469294858648029819087685)) * X ^ 1 +
    (96199233965322760559251076344293145718571794832419172303977393639571369492580) * X ^ 2 +
    (-41137857746372218996284722706293423986162949322000514207473524877579591333294) * X ^ 3 +
    (16476925669392800475144901255982804517082150241506891099890558296924694399012) * X ^ 4 +
    (-6166990452048539346543409145632237018487591852511559680114191645744126560511) * X ^ 5 +
    (2151258734518826383342587870083294359383538963615383112838220694365279350594) * X ^ 6 +
    (-697347636728465043085077910103437617362691990986754589176341788777091409973) * X ^ 7 +
    (209364971475766633264194787104501300545407508134365709600123953770398958610) * X ^ 8
  )

def recurrence1Remainder34Block12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    (-58002749491038843155142605709413798589843284619608769324948135258266948481) +
    (14766768496062207618124554460556092810898302231359398966351689027232147725) * X ^ 1 +
    (-3438741078067813006999964111558802515650913563001272199381738696663260175) * X ^ 2 +
    (728651688557667569717560257497291319857445016512279007790599929826497054) * X ^ 3 +
    (-139659714224592769635984264760056782903951715702256776404717511245505575) * X ^ 4 +
    (24049548201996091490503564997300121330517421945187119738711493174145342) * X ^ 5 +
    (-3691694611221366274457078411542491964204073636130756575140474765809139) * X ^ 6 +
    (500562717063577489490331790070398938980262126112598798225496500501679) * X ^ 7 +
    (-59308767984437397009771699399855183112786431021313900982449145260424) * X ^ 8
  )

def recurrence1Remainder34Block13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (6061805810475100842236192944724333454945927691876451661768457509208) +
    (-526146696073771114129468010201317951983904526345399239456287295778) * X ^ 1 +
    (38040539816116776731133440544087903974097916940432998240197912828) * X ^ 2 +
    (-2236071424626926695964541350283361969758705262391755786029701063) * X ^ 3 +
    (103583270207729848252855016478559194645919148297368310956552733) * X ^ 4 +
    (-3628696384037984960252045373735553196736232430519501983629386) * X ^ 5 +
    (90789408065674999168409458609903686043489473381768803237326) * X ^ 6 +
    (-1486886117090757955611969937896437602163161758729217465430) * X ^ 7 +
    (13464155310162441795021689648575150520982710456067865301) * X ^ 8
  )

def recurrence1Remainder34Block14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    (-32477957755995909479046641812234839673995332546198744) +
    (-412510088768745846689445454736320617589341970511378) * X ^ 1 +
    (2816636253566328745715348205629681472013754323165) * X ^ 2 +
    (-1618028819840626949148439626073625377555435387) * X ^ 3 +
    (-26735832861833083505215688216277786586607238) * X ^ 4 +
    (75348378164637813971372304330837750740845) * X ^ 5 +
    (-76049583511674624112600037709819546500) * X ^ 6 +
    (29466558674585668368175858912839223) * X ^ 7 +
    (-3762970816376932961872264762260) * X ^ 8
  )

def recurrence1Remainder34Block15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    (121657735088933848098082139) +
    (-655632661571987784261) * X ^ 1 +
    (280915358490100) * X ^ 2 +
    (-794588) * X ^ 3
  )

def recurrence1Remainder34 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder34Block0 +
  recurrence1Remainder34Block1 +
  recurrence1Remainder34Block2 +
  recurrence1Remainder34Block3 +
  recurrence1Remainder34Block4 +
  recurrence1Remainder34Block5 +
  recurrence1Remainder34Block6 +
  recurrence1Remainder34Block7 +
  recurrence1Remainder34Block8 +
  recurrence1Remainder34Block9 +
  recurrence1Remainder34Block10 +
  recurrence1Remainder34Block11 +
  recurrence1Remainder34Block12 +
  recurrence1Remainder34Block13 +
  recurrence1Remainder34Block14 +
  recurrence1Remainder34Block15

def recurrence1Remainder35Block0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (64) +
    (-12156) * X ^ 1 +
    (1354562202) * X ^ 2 +
    (-518380813692) * X ^ 3 +
    (585555622533882) * X ^ 4 +
    (-157410261428692160) * X ^ 5 +
    (34556515582732965276) * X ^ 6 +
    (-4301410760970204622105) * X ^ 7 +
    (384185146583496783398731) * X ^ 8
  )

def recurrence1Remainder35Block1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-23102340457255115206225180) +
    (1023234497103504062614474552) * X ^ 1 +
    (-33268964950842174920443327383) * X ^ 2 +
    (758633249959525901109917614448) * X ^ 3 +
    (1507484628252244886952455312383) * X ^ 4 +
    (-1597478344599563677298840073878171) * X ^ 5 +
    (116373838883438904938614640656704955) * X ^ 6 +
    (-5366032119857615523081935066061634679) * X ^ 7 +
    (181168266321197660865678430073531837421) * X ^ 8
  )

def recurrence1Remainder35Block2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-4688268113965608702130455099134678375699) +
    (94242606004781941951845106722309539305573) * X ^ 1 +
    (-1443692377612875362915310937684463618654664) * X ^ 2 +
    (15220765080512840366464686731227324522190291) * X ^ 3 +
    (-51709534414231195056832264154795877180578015) * X ^ 4 +
    (-2088691358881307945602799163382309623604857558) * X ^ 5 +
    (62112663824049410516588572312860692397002375981) * X ^ 6 +
    (-1096152708335522347033464127465701902955878650206) * X ^ 7 +
    (14948017681121838016616867722378586391672891499004) * X ^ 8
  )

def recurrence1Remainder35Block3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-169500399305199683132202717770969364728771132566079) +
    (1651019051308693417631201608933808494457423689764077) * X ^ 1 +
    (-14063627383815414127233100855777399941339125040500099) * X ^ 2 +
    (105917189634355617289564490597701936033350055464950937) * X ^ 3 +
    (-710165696978516089964604718979335271731610544719841884) * X ^ 4 +
    (4256548100224837219944082284559531223048156335571915446) * X ^ 5 +
    (-22848238885305523165302020957055047654566058350901061154) * X ^ 6 +
    (109789128754097385507407932976912040088068164627896663603) * X ^ 7 +
    (-470661950176926338602388446111629162245194919375373530551) * X ^ 8
  )

def recurrence1Remainder35Block4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (1785017533754185844634067673117507157955536654718105276975) +
    (-5877578946285211009667169735200547441309488908296664940137) * X ^ 1 +
    (16073844166706592948672022590492243118351718016347366895539) * X ^ 2 +
    (-31972063857397936867818279330587369649806597070346540161288) * X ^ 3 +
    (16526830343414984442770481395649957371359772004219738968345) * X ^ 4 +
    (232874833269767410146557178501078408661719140279534891310910) * X ^ 5 +
    (-1483268019190884257892954689205167345399660826585251827140150) * X ^ 6 +
    (6153412297890782315442632121625329952107476035612251127804010) * X ^ 7 +
    (-21050635779083919515488972262208135117165390212869305927476258) * X ^ 8
  )

def recurrence1Remainder35Block5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (62627862336168020614276340147971039322194268518301393583264248) +
    (-156650913352348315895120015905858960763193998994036032611684592) * X ^ 1 +
    (288605086662484691375303631867463597517122484614948498510881529) * X ^ 2 +
    (-274939148849570046895308170617336734246000723960126787775642912) * X ^ 3 +
    (152350745627287390737076952925818039970546316231009997001622265) * X ^ 4 +
    (-3675919368687448028956551421543945784774951429554339175838887131) * X ^ 5 +
    (24718253578327531557654063039275426081028169217687267035479497655) * X ^ 6 +
    (-55400300387709814704672048624214403986754900782173671569889578366) * X ^ 7 +
    (-157374571515781813053417558657762161533945946317239716557761927688) * X ^ 8
  )

def recurrence1Remainder35Block6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (1534714190196044122729144518082790927485218819424997583811024485594) +
    (-4282329269304493210767701528326420236321334042909988444148947142377) * X ^ 1 +
    (-3041267233044429338394683166576711604150740321675024639781277390349) * X ^ 2 +
    (69524738659047282022855197487281119144351180244689394823464662944194) * X ^ 3 +
    (-255969526666785140037704816165129538592843787358204745662036357188846) * X ^ 4 +
    (241457309966006350374379727158419282784868344869176178406301862034607) * X ^ 5 +
    (1955858626746270931855404397872885430919663983795806797029695044989887) * X ^ 6 +
    (-11051349933467088165738058933963914517770030080980683601082305893458160) * X ^ 7 +
    (26400172437023117610899553651518033237685125014432822917090407935153063) * X ^ 8
  )

def recurrence1Remainder35Block7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (-91318310931367026818465719861175689272173472685573552275420049939245) +
    (-258532857061551560619365614597404627507404602945638687838891821075609611) * X ^ 1 +
    (1114163830836147869011439870007577002678406117261980631161822979234983019) * X ^ 2 +
    (-2479240447283096022041103532283391225269761211109368923961149915724191930) * X ^ 3 +
    (1102611223183233577487645478890032845953513110067800062998680582546465865) * X ^ 4 +
    (15733700482159318132242512486410154453982346751587044020014681765236104936) * X ^ 5 +
    (-77040918225517736074921729336195990513293135974166709962259944549347487984) * X ^ 6 +
    (215489784207940916533650299384876288246083729670829769966431539795282755301) * X ^ 7 +
    (-377781753888803961828638061639688835594512078997877013100237833213875331715) * X ^ 8
  )

def recurrence1Remainder35Block8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (144693952666072833585053620515821037495162493008316823504075366429204108104) +
    (1895508554447424250237432462766301765926181207829128055282173822134556985390) * X ^ 1 +
    (-9236535594132348555596946779758091358231885991776368090587872494569704894555) * X ^ 2 +
    (28913075527356861206989739822304185594896592679563225301983049716920497522603) * X ^ 3 +
    (-72827982308281931102051921601933607417406329156971195387916888822612581704519) * X ^ 4 +
    ((1 * 10 ^ 77 +
      57967909333484461609288275868338609808176164588548581655633392941335843756709)) * X ^ 5 +
    -((3 * 10 ^ 77 +
      04304431198938751297424810222037624245617522712593614063490138278830609064811)) * X ^ 6 +
    ((5 * 10 ^ 77 +
      29612123679280822372791683194641512267340837658158128418351041129922782048672)) * X ^ 7 +
    -((8 * 10 ^ 77 +
      41710417408893468985812214369360201503454660116734631626444100440639462004271)) * X ^ 8
  )

def recurrence1Remainder35Block9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    ((12 * 10 ^ 77 +
      30403699005659483630457618521670262184337185591494109073399139827395928714682)) +
    -((16 * 10 ^ 77 +
      62730882017418057918669283278748618087014388397199910139714258714508328729345)) * X ^ 1 +
    ((20 * 10 ^ 77 +
      84965618315258459843686050587028944636622744493983962353207759297044654731947)) * X ^ 2 +
    -((24 * 10 ^ 77 +
      32647326235158778861948905430387116985610128303329311138506996275486962607249)) * X ^ 3 +
    ((26 * 10 ^ 77 +
      46447166741888933563934245131887161077794221571807873883191441673518770514292)) * X ^ 4 +
    -((26 * 10 ^ 77 +
      88582878365336436617406242871454627367694745114585140934013065063317671139375)) * X ^ 5 +
    ((25 * 10 ^ 77 +
      53593557271417913201208446836563835930399275607651619991705100169760218752352)) * X ^ 6 +
    -((22 * 10 ^ 77 +
      69304458244851130786977824229705264836156732253056194702450059501876420201137)) * X ^ 7 +
    ((18 * 10 ^ 77 +
      87844297009957210035837767091600120116933918934224364197779982762460968274730)) * X ^ 8
  )

def recurrence1Remainder35Block10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((14 * 10 ^ 77 +
      70560749271792529933718642297334643268309425912084999014088297796059317143268)) +
    ((10 * 10 ^ 77 +
      72646015655485347770105478432796670080315351963895547759087326290334576030275)) * X ^ 1 +
    -((7 * 10 ^ 77 +
      32503228668572862156810803118007404263776587791988126342028672689814708556496)) * X ^ 2 +
    ((4 * 10 ^ 77 +
      68144300853714753179464768165001736359478988720474738074794201969067930200703)) * X ^ 3 +
    -((2 * 10 ^ 77 +
      79847361235686798847775630656184850506128403611491407807494217458046530359994)) * X ^ 4 +
    ((1 * 10 ^ 77 +
      56352704291582908774896798775330773343512151522814191987918443839200574530752)) * X ^ 5 +
    (-81567964059342537181242914268387620031594439668585633103548300433367776799500) * X ^ 6 +
    (39688450707802158972314189699432560347948576501612799974069615748044579376778) * X ^ 7 +
    (-17986532606676608036032930939094674071980371221241581198247246483649023772656) * X ^ 8
  )

def recurrence1Remainder35Block11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    (7580184208916519539297790360378321882817195130328393419482122791868070465564) +
    (-2965272352933744063046617640492315934479033772964798254129430881919971030965) * X ^ 1 +
    (1074454443066940163824257190740599399667653184295345415616823262510873205420) * X ^ 2 +
    (-359753689819533977161037169955334229921734293980497730097550408841912945356) * X ^ 3 +
    (111000304750588690367789764447195187821765514094402108803291725926867574462) * X ^ 4 +
    (-31461878559035609974432185665843772417900361319406666511490799428414130423) * X ^ 5 +
    (8162689132900902153483871891507015679161297263692329257292945453729701981) * X ^ 6 +
    (-1930596903859232854114376492422850788611645700447386490662054897860910174) * X ^ 7 +
    (414301773830745419847878688478118867785217992374857152748342667625328316) * X ^ 8
  )

def recurrence1Remainder35Block12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    (-80232712501281461530959948749617306803171906720627872012789886366106333) +
    (13933501439803518606305450146542102579122155314673201932427275093563651) * X ^ 1 +
    (-2154010580000914123888347706398050309774017660112198043582971557811006) * X ^ 2 +
    (293867853613697882417068445880469772403917429438929376490465112531229) * X ^ 3 +
    (-35018937038253135983096510644117003315940010844022081388059837272272) * X ^ 4 +
    (3600251316487800894275753333865655352187404784049787781823472171617) * X ^ 5 +
    (-314569908194423288328232713754290979147036329351124493885887477841) * X ^ 6 +
    (22930458519256445288231122943193823159909427427981409944781646074) * X ^ 7 +
    (-1362504344401340245160496691822587524683394673409576352415777549) * X ^ 8
  )

def recurrence1Remainder35Block13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (64061390604558097883906764110598623800098919211954763283360665) +
    (-2292100627717888929660294276473888128612784009271797951977446) * X ^ 1 +
    (59151732100970484544108579724157902403400413763886616722712) * X ^ 2 +
    (-1016073560684526630577199370871922826342038529185970779716) * X ^ 3 +
    (10012740810256628612796853277483596506283317629267265714) * X ^ 4 +
    (-33354150504035218502672229077114828172928999151260057) * X ^ 5 +
    (-255742389286012772217283101849178090848564383478337) * X ^ 6 +
    (2285350403425215580504322667170907334123440058042) * X ^ 7 +
    (-2818287159834181677550113595790244618964107953) * X ^ 8
  )

def recurrence1Remainder35Block14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    (-19577197265577220913540397294542570172671329) +
    (68539716393261301098654953524650645861846) * X ^ 1 +
    (-80955427547538972733980674317060011479) * X ^ 2 +
    (37352905326245285965819736386876315) * X ^ 3 +
    (-5905487124530116060313320642201) * X ^ 4 +
    (249741379239703289263231179) * X ^ 5 +
    (-1912620390008597624124) * X ^ 6 +
    (1363823716622532) * X ^ 7 +
    (-9250229) * X ^ 8
  )

def recurrence1Remainder35 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Remainder35Block0 +
  recurrence1Remainder35Block1 +
  recurrence1Remainder35Block2 +
  recurrence1Remainder35Block3 +
  recurrence1Remainder35Block4 +
  recurrence1Remainder35Block5 +
  recurrence1Remainder35Block6 +
  recurrence1Remainder35Block7 +
  recurrence1Remainder35Block8 +
  recurrence1Remainder35Block9 +
  recurrence1Remainder35Block10 +
  recurrence1Remainder35Block11 +
  recurrence1Remainder35Block12 +
  recurrence1Remainder35Block13 +
  recurrence1Remainder35Block14

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1CommonData. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 1 certificate: CommonData

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1ExceptionalBlock0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (1) +
    (105) * X ^ 1 +
    (5082) * X ^ 2 +
    (149471) * X ^ 3 +
    (2958165) * X ^ 4 +
    (41023815) * X ^ 5 +
    (398598550) * X ^ 6 +
    (2560910535) * X ^ 7 +
    (8355842040) * X ^ 8
  )

def recurrence1ExceptionalBlock1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-16800566650) +
    (-313741204392) * X ^ 1 +
    (-1123713212160) * X ^ 2 +
    (1935404759771) * X ^ 3 +
    (26857369767123) * X ^ 4 +
    (39383182950540) * X ^ 5 +
    (-316919515997021) * X ^ 6 +
    (-1061659373279715) * X ^ 7 +
    (2578994534584713) * X ^ 8
  )

def recurrence1ExceptionalBlock2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (14288494642556554) +
    (-18493130411723205) * X ^ 1 +
    (-140484426344859681) * X ^ 2 +
    (159204577283229345) * X ^ 3 +
    (1086889149935431038) * X ^ 4 +
    (-1661810655047332671) * X ^ 5 +
    (-6274898549720833620) * X ^ 6 +
    (15651246118414389714) * X ^ 7 +
    (20157232407293036160) * X ^ 8
  )

def recurrence1ExceptionalBlock3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-106563752804659089492) +
    (43269078160928959479) * X ^ 1 +
    (414450006896428258455) * X ^ 2 +
    (-842014404361630034052) * X ^ 3 +
    (-119281767268473347265) * X ^ 4 +
    (3152774106769334731866) * X ^ 5 +
    (-5778553202927925661122) * X ^ 6 +
    (2666889620045223941340) * X ^ 7 +
    (9726971503363441945758) * X ^ 8
  )

def recurrence1ExceptionalBlock4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-28470153805727028841180) +
    (45078133249256375903376) * X ^ 1 +
    (-51771791451879902984532) * X ^ 2 +
    (46891866427818126636880) * X ^ 3 +
    (-34788479689070218208160) * X ^ 4 +
    (21590389997488734533580) * X ^ 5 +
    (-11357584058478926731960) * X ^ 6 +
    (5109027286320056088360) * X ^ 7 +
    (-1977373217055772954110) * X ^ 8
  )

def recurrence1ExceptionalBlock5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (661352733864819490186) +
    (-191733778484121398280) * X ^ 1 +
    (48278655302365030242) * X ^ 2 +
    (-10569935234012246939) * X ^ 3 +
    (2012514988901852565) * X ^ 4 +
    (-333010096820134566) * X ^ 5 +
    (47809311906657875) * X ^ 6 +
    (-5939098805026107) * X ^ 7 +
    (635839875408759) * X ^ 8
  )

def recurrence1ExceptionalBlock6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-58343362733250) +
    (4554127848543) * X ^ 1 +
    (-299389331370) * X ^ 2 +
    (16353765596) * X ^ 3 +
    (-728622972) * X ^ 4 +
    (25793250) * X ^ 5 +
    (-697739) * X ^ 6 +
    (13545) * X ^ 7 +
    (-168) * X ^ 8
  )

def recurrence1ExceptionalBlock7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (1)
  )

def recurrence1Exceptional : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1ExceptionalBlock0 +
  recurrence1ExceptionalBlock1 +
  recurrence1ExceptionalBlock2 +
  recurrence1ExceptionalBlock3 +
  recurrence1ExceptionalBlock4 +
  recurrence1ExceptionalBlock5 +
  recurrence1ExceptionalBlock6 +
  recurrence1ExceptionalBlock7







































































def recurrence1QuotientConstantBlock0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (8) +
    (13068) * X ^ 1 +
    (-54531222) * X ^ 2 +
    (3964492007) * X ^ 3 +
    (1468898335559) * X ^ 4 +
    (-44267829789087) * X ^ 5 +
    (-5037803459095162) * X ^ 6 +
    (1756975379887449) * X ^ 7 +
    (5725959059842460975) * X ^ 8
  )

def recurrence1QuotientConstantBlock1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (66709556870025521384) +
    (-1727173631399448109220) * X ^ 1 +
    (-50096143088169277279987) * X ^ 2 +
    (103719145293873687264828) * X ^ 3 +
    (10101262277240043268897475) * X ^ 4 +
    (75586294710160684796655886) * X ^ 5 +
    (-1138297751134838417956777485) * X ^ 6 +
    (-13346802070242962554632733244) * X ^ 7 +
    (36812472913738999116461816400) * X ^ 8
  )

def recurrence1QuotientConstantBlock2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (1359204080346850077245218594401) +
    (1408446452386639366980312527133) * X ^ 1 +
    (-79675304708396847641876100278520) * X ^ 2 +
    (-281585134312670780266870409807353) * X ^ 3 +
    (3461437008908583684215212895803557) * X ^ 4 +
    (17711455618050299223434097193819390) * X ^ 5 +
    (-115123961109439391512315530138138345) * X ^ 6 +
    (-744319101238687667890230189277065046) * X ^ 7 +
    (3277004376832468693210224243246017004) * X ^ 8
  )

def recurrence1QuotientConstantBlock3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (23263300686750827374779947751436751583) +
    (-85073816220882513668820821363515293239) * X ^ 1 +
    (-570277889304718662943532752941650749403) * X ^ 2 +
    (2085118574671557703064007164604462836690) * X ^ 3 +
    (11008068052971140053223472035597237832545) * X ^ 4 +
    (-47021183638954154391074474255752720063181) * X ^ 5 +
    (-160487497298315360955589883806584167953724) * X ^ 6 +
    (923622626896679291304228351499166767318939) * X ^ 7 +
    (1497962234340740759850088495122640028641394) * X ^ 8
  )

def recurrence1QuotientConstantBlock4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-14895521089031656970429947591553678524220241) +
    (-769286746948012393611598535314417420012331) * X ^ 1 +
    (184404620375996429091851669451180692786277506) * X ^ 2 +
    (-264581921525230483554879529546866219468665333) * X ^ 3 +
    (-1550808193158726832329218797003174124792714819) * X ^ 4 +
    (5199229205722972626767915426236312807608201378) * X ^ 5 +
    (5328822940339236631135856714084306039407146449) * X ^ 6 +
    (-54436440877609241171452368920675087682861919521) * X ^ 7 +
    (59205036490303284132867680029696019131271984187) * X ^ 8
  )

def recurrence1QuotientConstantBlock5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (291857668182945056228561215724424817009626527870) +
    (-990906027365401096810236675541198787877668187331) * X ^ 1 +
    (138171513655877004966777324926748331854545257685) * X ^ 2 +
    (5630070846436232020572581775758902860767750031323) * X ^ 3 +
    (-12684645751571012076455960854545241964869516567247) * X ^ 4 +
    (-1463643624772066760684973941276729211762443073134) * X ^ 5 +
    (62728799542800638563363211003431644274384301953938) * X ^ 6 +
    (-131072583607072835728263512697229784212896294426622) * X ^ 7 +
    (41691160270804258456427038986191345551430903596812) * X ^ 8
  )

def recurrence1QuotientConstantBlock6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (375694634511453033876416487803714570720578878726089) +
    (-954177668767191751999690510859187076297336856813661) * X ^ 1 +
    (980633384652262269309874645087636224519699996259811) * X ^ 2 +
    (338001816188580578455754838468506757057000911688503) * X ^ 3 +
    (-2823353110120929167334506296861052013211116611316165) * X ^ 4 +
    (4806072689794312237154573787581369093075330834303165) * X ^ 5 +
    (-4206852302916754152554798096972599470625735871057026) * X ^ 6 +
    (593892212141387337580390730456370490493428997450542) * X ^ 7 +
    (3942970693656320137393223219356264803233475509991733) * X ^ 8
  )

def recurrence1QuotientConstantBlock7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    (-6371521745023138116146337227512796702426340140950702) +
    (5330635637967165587037081199401781452486658174923772) * X ^ 1 +
    (-2115838897491464072081691887441128623937394477431834) * X ^ 2 +
    (-799010552378753330945329174742041098112410026987414) * X ^ 3 +
    (1923152045288975253557332984652970630596483899872749) * X ^ 4 +
    (-1490691487724970075043541464854350471231808381906369) * X ^ 5 +
    (585328054954623948033156916504835347257237745014343) * X ^ 6 +
    (6130497650841878153979272238789337129405272464822) * X ^ 7 +
    (-160063738085674094737344280277292389071447824545004) * X ^ 8
  )

def recurrence1QuotientConstantBlock8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    (101224787381366944785344405074315862049420210363365) +
    (-27644416727770167491345377040328477701444423127460) * X ^ 1 +
    (-2093635626870780042310065729199384315571719319890) * X ^ 2 +
    (4648827411303692756923108192228494236810295243992) * X ^ 3 +
    (-1589899197412312971684799035465173549058908398095) * X ^ 4 +
    (104611307747661486195638957587564039215482384423) * X ^ 5 +
    (92841805224398120533018605959181863741516316121) * X ^ 6 +
    (-28946385105590749059539502223569160797430635729) * X ^ 7 +
    (792460299320736142190210139305691660223515235) * X ^ 8
  )

def recurrence1QuotientConstantBlock9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    (1104329512783323733296356067440873262162219052) +
    (-149019731736318300834795123448166808019918267) * X ^ 1 +
    (-19205556078506077946842853372705103491854443) * X ^ 2 +
    (3841436018733511159270798707167627771021357) * X ^ 3 +
    (316704144410745523809359377185953467631488) * X ^ 4 +
    (-37624960044027773311194428988433997029540) * X ^ 5 +
    (-5402048322363559308977914316373487756663) * X ^ 6 +
    (-257662010728145829596199563993205895378) * X ^ 7 +
    (-6018321376083418002634543618592030902) * X ^ 8
  )

def recurrence1QuotientConstantBlock10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    (-73475965227879638021877837971440944) +
    (-456894887003893580993831002844426) * X ^ 1 +
    (-1236820737019774382789254981274) * X ^ 2 +
    (-194940497915311833242101812) * X ^ 3 +
    (4787667832732992035933979) * X ^ 4 +
    (6108791738159711311517) * X ^ 5 +
    (1668438307345457066) * X ^ 6 +
    (62130712356237) * X ^ 7 +
    (84879619) * X ^ 8
  )

def recurrence1QuotientConstant : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1QuotientConstantBlock0 +
  recurrence1QuotientConstantBlock1 +
  recurrence1QuotientConstantBlock2 +
  recurrence1QuotientConstantBlock3 +
  recurrence1QuotientConstantBlock4 +
  recurrence1QuotientConstantBlock5 +
  recurrence1QuotientConstantBlock6 +
  recurrence1QuotientConstantBlock7 +
  recurrence1QuotientConstantBlock8 +
  recurrence1QuotientConstantBlock9 +
  recurrence1QuotientConstantBlock10

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end

#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block12
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block13
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block12
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block12
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder22Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block12
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block13
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block14
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block15
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block16
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block17
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder30Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block12
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block13
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block14
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block15
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block16
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block12
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block13
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block14
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block15
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block16
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block12
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block13
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block14
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block15
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder33Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block12
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block13
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block14
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block15
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block10
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block11
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block12
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block13
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block14
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block8
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block9
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source0Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source0Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source0Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source0Block3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source2Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source2Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source2Block2
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source3
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source3Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source3Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4Block1
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source6
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source6Block0
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source7
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source7Block0


