-- Prove2me | Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
-- name    : MazurTransfer_Order49ResultantRecurrenceData0
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T18:33:50.529244+00:00
-- url     : https://prove2.me/theorems/4e882245-cdf0-4245-ac72-db1619eda7b1
-- title:
--   Order-49 exact polynomial data: recurrence-data-0
-- statement:
--   This shard contains the original bivariate polynomial data for step $0$ of the order-seven primitive pseudo-remainder sequence over $\mathbb Q[D][X]$. It records the exact remainders, quotient and exceptional factors, and defines the corresponding equation as a proposition. Defining that proposition does not assert that the equation holds. Its proof is a separate checked certificate. Named downstream consumers: the exact recurrence certificate and the bounded-resultant nonvanishing theorem used to exclude order49.
-- source:
--   Exact pure-data declarations from user MazurTheorem WIP, commit54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Source commands selected by kernel dependencies and complete resolved Lean AST ranges; all declaration types, values, rational coefficients, source headers and Apache-2.0 attribution retained. No proof assertion is exported as data.

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Field.Rat
import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData0. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial data for the order-seven branch-zero resultant PRS

This file starts the exact primitive pseudo-remainder sequence over
`ℚ[D][X]` for the selection cofactor and the first degree-seven
division cofactor. Each generated remainder is grouped by its outer
`X` coefficient; the first quotient remains exact table data, while
the later linear quotients are forced by the leading two coefficients.
Lean recurrence certificates check the untrusted generating computation.
-/
section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ abbrev Coefficient := Polynomial ℚ
/-- Internal datum. -/ abbrev Bivariate := Polynomial Coefficient

/-- Internal datum. -/ def coefficientTerm
    (degree : ℕ) (coefficient : ℚ) : Coefficient :=
  monomial degree coefficient



/-- Internal datum. -/ def outerTerm
    (degree : ℕ) (coefficient : Coefficient) : Bivariate :=
  C coefficient * X ^ degree

/-- Internal datum. -/ def linearPseudoQuotient
    (dividend divisor : Bivariate)
    (dividendDegree divisorDegree : ℕ) : Bivariate :=
  outerTerm 1
      (divisor.coeff divisorDegree *
        dividend.coeff dividendDegree) +
    outerTerm 0
      (divisor.coeff divisorDegree *
          dividend.coeff (dividendDegree - 1) -
        divisor.coeff (divisorDegree - 1) *
          dividend.coeff dividendDegree)

/-- Internal datum. -/ def parameter : Coefficient := X

/-- Internal datum. -/ def discriminantFactor : Coefficient :=
  parameter ^ 3 - 8 * parameter ^ 2 + 5 * parameter + 1

/-- Internal datum. -/ def cmSix : Coefficient :=
  parameter ^ 6 + 229 * parameter ^ 5 + 270 * parameter ^ 4 -
    1695 * parameter ^ 3 + 1430 * parameter ^ 2 -
    235 * parameter + 1

/-- Internal datum. -/ def cmTwelve : Coefficient :=
  parameter ^ 12 - 522 * parameter ^ 11 -
    8955 * parameter ^ 10 + 37950 * parameter ^ 9 -
    70998 * parameter ^ 8 + 131562 * parameter ^ 7 -
    253239 * parameter ^ 6 + 316290 * parameter ^ 5 -
    218058 * parameter ^ 4 + 80090 * parameter ^ 3 -
    14631 * parameter ^ 2 + 510 * parameter + 1

/-- Internal datum. -/ def remainder0 : Bivariate := selectionCofactorData

/-- Internal datum. -/ def remainder1 : Bivariate := divisionCofactorData0

/-- Internal datum. -/ def remainder2Coefficient0Chunk0 : Coefficient :=
  coefficientTerm 118
    (-((57 : ℚ))) +
  coefficientTerm 117
    (-((3841078186 : ℚ))) +
  coefficientTerm 116
    (-((558110085407786 : ℚ))) +
  coefficientTerm 115
    (-((5072148110737246025 : ℚ))) +
  coefficientTerm 114
    (-((7487522096003555795152 : ℚ))) +
  coefficientTerm 113
    (-((1507245375088838010731695 : ℚ))) +
  coefficientTerm 112
    (1577196414728952886234267757 : ℚ) +
  coefficientTerm 111
    (843753345028747037362040919139 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient0Chunk1 : Coefficient :=
  coefficientTerm 110
    (165026199140154693898992949889670 : ℚ) +
  coefficientTerm 109
    (15560161622173073532254368820081712 : ℚ) +
  coefficientTerm 108
    (744894209253773091908300182564263888 : ℚ) +
  coefficientTerm 107
    ((17 : ℚ) * 10 ^ 36 +
      117395763730572988598898971842175952) +
  coefficientTerm 106
    ((121 : ℚ) * 10 ^ 36 +
      420420245797158958065078024853838771) +
  coefficientTerm 105
    (-(((1613 : ℚ) * 10 ^ 36 +
      170450578754187113664875608047773491))) +
  coefficientTerm 104
    (-(((21835 : ℚ) * 10 ^ 36 +
      855329074871209439970786676218209063))) +
  coefficientTerm 103
    ((107596 : ℚ) * 10 ^ 36 +
      482591299095251211202323863114511740)

/-- Internal datum. -/ def remainder2Coefficient0Chunk2 : Coefficient :=
  coefficientTerm 102
    ((1560530 : ℚ) * 10 ^ 36 +
      508013868545100650132777578578566977) +
  coefficientTerm 101
    (-(((7173045 : ℚ) * 10 ^ 36 +
      799197579454731740761038147002347352))) +
  coefficientTerm 100
    (-(((59718794 : ℚ) * 10 ^ 36 +
      864614781855680443009507852961443027))) +
  coefficientTerm 99
    ((329041432 : ℚ) * 10 ^ 36 +
      510035751706973504730628132940569628) +
  coefficientTerm 98
    ((1682596274 : ℚ) * 10 ^ 36 +
      192633024084773447547225160481835569) +
  coefficientTerm 97
    (-(((13080880038 : ℚ) * 10 ^ 36 +
      331164717498911381112159427479572402))) +
  coefficientTerm 96
    (-(((35682081868 : ℚ) * 10 ^ 36 +
      816433525662072854424923464803899505))) +
  coefficientTerm 95
    ((594888352697 : ℚ) * 10 ^ 36 +
      172539251946829237087330057928808919)

/-- Internal datum. -/ def remainder2Coefficient0Chunk3 : Coefficient :=
  coefficientTerm 94
    (-(((1609474925545 : ℚ) * 10 ^ 36 +
      182656633135617398099675121374668988))) +
  coefficientTerm 93
    (-(((7242965276005 : ℚ) * 10 ^ 36 +
      198687250854010145591748681377657456))) +
  coefficientTerm 92
    ((71047281503988 : ℚ) * 10 ^ 36 +
      594395292188314575685858281974979711) +
  coefficientTerm 91
    (-(((230300761212428 : ℚ) * 10 ^ 36 +
      877959999864514542636268972701952935))) +
  coefficientTerm 90
    ((85446096580397 : ℚ) * 10 ^ 36 +
      680979268746891364634839534831385470) +
  coefficientTerm 89
    ((2403877461037195 : ℚ) * 10 ^ 36 +
      963346376424656155043888088425166875) +
  coefficientTerm 88
    (-(((11482509351260787 : ℚ) * 10 ^ 36 +
      881775076202547517529217615946686081))) +
  coefficientTerm 87
    ((27180003515099636 : ℚ) * 10 ^ 36 +
      736288757639539073556892684559618223)

/-- Internal datum. -/ def remainder2Coefficient0Chunk4 : Coefficient :=
  coefficientTerm 86
    (-(((23045195150113390 : ℚ) * 10 ^ 36 +
      851533850503264632732698437216591192))) +
  coefficientTerm 85
    (-(((83054877363276582 : ℚ) * 10 ^ 36 +
      153572517801866795997624065665320178))) +
  coefficientTerm 84
    ((408293016549124941 : ℚ) * 10 ^ 36 +
      092699581346964679441895603795325958) +
  coefficientTerm 83
    (-(((950964642855568595 : ℚ) * 10 ^ 36 +
      917937148463566556455742041776139030))) +
  coefficientTerm 82
    ((1332657498309766410 : ℚ) * 10 ^ 36 +
      093961889457493240678510755788979622) +
  coefficientTerm 81
    (-(((736087488191373628 : ℚ) * 10 ^ 36 +
      403549815668351514898023125492160919))) +
  coefficientTerm 80
    (-(((1554480341109496625 : ℚ) * 10 ^ 36 +
      004429488308674062741406305645410850))) +
  coefficientTerm 79
    ((5142430892918680930 : ℚ) * 10 ^ 36 +
      903256032716510315963633132641078831)

/-- Internal datum. -/ def remainder2Coefficient0Chunk5 : Coefficient :=
  coefficientTerm 78
    (-(((8171004906960062150 : ℚ) * 10 ^ 36 +
      958281833795327043585118995535503793))) +
  coefficientTerm 77
    ((8874202635339496410 : ℚ) * 10 ^ 36 +
      647718336739457874613827537931241641) +
  coefficientTerm 76
    (-(((8281322558401235238 : ℚ) * 10 ^ 36 +
      033851106880737444484475822509353739))) +
  coefficientTerm 75
    ((10745817826620269598 : ℚ) * 10 ^ 36 +
      676200057421220998636038861351205476) +
  coefficientTerm 74
    (-(((19675967917793710704 : ℚ) * 10 ^ 36 +
      235343250800850601613615115738019326))) +
  coefficientTerm 73
    ((31217689682422219822 : ℚ) * 10 ^ 36 +
      285482974369168030034942981141275460) +
  coefficientTerm 72
    (-(((33394678553273738523 : ℚ) * 10 ^ 36 +
      894447672201797175806248079960824229))) +
  coefficientTerm 71
    ((14915691153763092973 : ℚ) * 10 ^ 36 +
      853852477020507767130725417493824916)

/-- Internal datum. -/ def remainder2Coefficient0Chunk6 : Coefficient :=
  coefficientTerm 70
    ((22622649723594544532 : ℚ) * 10 ^ 36 +
      826141549412266534983169558561402188) +
  coefficientTerm 69
    (-(((61687727358641659015 : ℚ) * 10 ^ 36 +
      289991008485945807169000866643639069))) +
  coefficientTerm 68
    ((80288771384155327696 : ℚ) * 10 ^ 36 +
      477068622320292133380775283507804161) +
  coefficientTerm 67
    (-(((68730293687975869875 : ℚ) * 10 ^ 36 +
      107587708993249866577186534605683258))) +
  coefficientTerm 66
    ((36416415138398479956 : ℚ) * 10 ^ 36 +
      000701682694083607585734323956960547) +
  coefficientTerm 65
    (-(((3178960320396938136 : ℚ) * 10 ^ 36 +
      119349815210378601274709185668604937))) +
  coefficientTerm 64
    (-(((15778242959145104133 : ℚ) * 10 ^ 36 +
      485300167950379020342628991290237379))) +
  coefficientTerm 63
    ((18090386868971818456 : ℚ) * 10 ^ 36 +
      858662029614161681345717082226652170)

/-- Internal datum. -/ def remainder2Coefficient0Chunk7 : Coefficient :=
  coefficientTerm 62
    (-(((11110284307128431035 : ℚ) * 10 ^ 36 +
      158933978291100334801954980947472146))) +
  coefficientTerm 61
    ((3459292504659497610 : ℚ) * 10 ^ 36 +
      979380743349758433450163007452524369) +
  coefficientTerm 60
    ((621725971190563657 : ℚ) * 10 ^ 36 +
      393235315757192056596706225030493894) +
  coefficientTerm 59
    (-(((1379867726824908573 : ℚ) * 10 ^ 36 +
      819612208907630171932514084636054614))) +
  coefficientTerm 58
    ((755349943097198560 : ℚ) * 10 ^ 36 +
      274645640023835200357276309089105499) +
  coefficientTerm 57
    (-(((147265800657316553 : ℚ) * 10 ^ 36 +
      789244740368621751889157008294390057))) +
  coefficientTerm 56
    (-(((74259866442592643 : ℚ) * 10 ^ 36 +
      309907716195443028789570438134352762))) +
  coefficientTerm 55
    ((66681838947911016 : ℚ) * 10 ^ 36 +
      521021237852219792660730576150126032)

/-- Internal datum. -/ def remainder2Coefficient0Chunk8 : Coefficient :=
  coefficientTerm 54
    (-(((18687086537014865 : ℚ) * 10 ^ 36 +
      119121801645888755694124474167125176))) +
  coefficientTerm 53
    (-(((2785848571080064 : ℚ) * 10 ^ 36 +
      457962537035628974255157624433659535))) +
  coefficientTerm 52
    ((4040747699608870 : ℚ) * 10 ^ 36 +
      687257985013647732806121074286902738) +
  coefficientTerm 51
    (-(((1133497054982079 : ℚ) * 10 ^ 36 +
      041065679089970365931806088756989147))) +
  coefficientTerm 50
    (-(((149432665535261 : ℚ) * 10 ^ 36 +
      992857347330551770721950842375691980))) +
  coefficientTerm 49
    ((193107590045649 : ℚ) * 10 ^ 36 +
      299339279328984668292960892819799483) +
  coefficientTerm 48
    (-(((40332554873310 : ℚ) * 10 ^ 36 +
      579622123872668669900409407948080662))) +
  coefficientTerm 47
    (-(((10475530471061 : ℚ) * 10 ^ 36 +
      913847079100899254638337734396287104)))

/-- Internal datum. -/ def remainder2Coefficient0Chunk9 : Coefficient :=
  coefficientTerm 46
    ((6947902940277 : ℚ) * 10 ^ 36 +
      472273331017092804828544810974028139) +
  coefficientTerm 45
    (-(((598801835612 : ℚ) * 10 ^ 36 +
      111105880235198090447628712531519493))) +
  coefficientTerm 44
    (-(((519630700961 : ℚ) * 10 ^ 36 +
      647778633579607877224146206648309539))) +
  coefficientTerm 43
    ((155606299034 : ℚ) * 10 ^ 36 +
      522954166844058198548068896279977537) +
  coefficientTerm 42
    ((14847492001 : ℚ) * 10 ^ 36 +
      852093904509154446647689144549047900) +
  coefficientTerm 41
    (-(((14533737069 : ℚ) * 10 ^ 36 +
      505132262481138493185774319227901666))) +
  coefficientTerm 40
    ((1070589103 : ℚ) * 10 ^ 36 +
      141380188990437600705938082237411849) +
  coefficientTerm 39
    ((854731750 : ℚ) * 10 ^ 36 +
      744759183117612048451503577686718350)

/-- Internal datum. -/ def remainder2Coefficient0Chunk10 : Coefficient :=
  coefficientTerm 38
    (-(((170616046 : ℚ) * 10 ^ 36 +
      135731321807523659719437449607831382))) +
  coefficientTerm 37
    (-(((33644919 : ℚ) * 10 ^ 36 +
      694007791905306165608311761387256527))) +
  coefficientTerm 36
    ((12747758 : ℚ) * 10 ^ 36 +
      848377365623179496199857217975063094) +
  coefficientTerm 35
    ((762752 : ℚ) * 10 ^ 36 +
      762879364689572744288733998737444098) +
  coefficientTerm 34
    (-(((681578 : ℚ) * 10 ^ 36 +
      237840065642926261228656071824770362))) +
  coefficientTerm 33
    ((3724 : ℚ) * 10 ^ 36 +
      415618239167221623117838218836606730) +
  coefficientTerm 32
    ((28927 : ℚ) * 10 ^ 36 +
      249338570910072158119743920309724861) +
  coefficientTerm 31
    (-(((1165 : ℚ) * 10 ^ 36 +
      280355746439384243786350455420790049)))

/-- Internal datum. -/ def remainder2Coefficient0Chunk11 : Coefficient :=
  coefficientTerm 30
    (-(((1037 : ℚ) * 10 ^ 36 +
      909449069702050995790634079279527234))) +
  coefficientTerm 29
    ((59 : ℚ) * 10 ^ 36 +
      173772590237271321614902242554864604) +
  coefficientTerm 28
    ((31 : ℚ) * 10 ^ 36 +
      358151232828134232489089258528740581) +
  coefficientTerm 27
    (-(((1 : ℚ) * 10 ^ 36 +
      614355931044266796217772307414613716))) +
  coefficientTerm 26
    (-((849488679231132760490374031074814762 : ℚ))) +
  coefficientTerm 25
    (31826313445941491054485986255887620 : ℚ) +
  coefficientTerm 24
    (17939832588070721406987746062937250 : ℚ) +
  coefficientTerm 23
    (-((54189002951574352392486001446389 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient0Chunk12 : Coefficient :=
  coefficientTerm 22
    (-((325902109613993235482591511158062 : ℚ))) +
  coefficientTerm 21
    (-((7632953412497286154928754530167 : ℚ))) +
  coefficientTerm 20
    (3839461295707575052402511711145 : ℚ) +
  coefficientTerm 19
    (253887039826360477352885637974 : ℚ) +
  coefficientTerm 18
    (-((29738389409425638678174724443 : ℚ))) +
  coefficientTerm 17
    (-((3234018323272692008644959524 : ℚ))) +
  coefficientTerm 16
    (76735418560623238749227979 : ℚ) +
  coefficientTerm 15
    (22027542795128115872321226 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient0Chunk13 : Coefficient :=
  coefficientTerm 14
    (409155522983929358223454 : ℚ) +
  coefficientTerm 13
    (-((66505908255265167228909 : ℚ))) +
  coefficientTerm 12
    (-((3131219520021488355261 : ℚ))) +
  coefficientTerm 11
    (73367409398595165996 : ℚ) +
  coefficientTerm 10
    (5905879565633563356 : ℚ) +
  coefficientTerm 9
    (-((9044841330557190 : ℚ))) +
  coefficientTerm 8
    (-((4242577921555076 : ℚ))) +
  coefficientTerm 7
    (10898850087779 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient0Chunk14 : Coefficient :=
  coefficientTerm 6
    (887174420015 : ℚ) +
  coefficientTerm 5
    (-((6591719746 : ℚ))) +
  coefficientTerm 4
    (1213258 : ℚ) +
  coefficientTerm 3
    (21998 : ℚ) +
  coefficientTerm 2
    (1 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient0Block0 : Coefficient :=
  remainder2Coefficient0Chunk0 +
  remainder2Coefficient0Chunk1 +
  remainder2Coefficient0Chunk2 +
  remainder2Coefficient0Chunk3 +
  remainder2Coefficient0Chunk4 +
  remainder2Coefficient0Chunk5 +
  remainder2Coefficient0Chunk6 +
  remainder2Coefficient0Chunk7 +
  remainder2Coefficient0Chunk8 +
  remainder2Coefficient0Chunk9 +
  remainder2Coefficient0Chunk10 +
  remainder2Coefficient0Chunk11

/-- Internal datum. -/ def remainder2Coefficient0Block1 : Coefficient :=
  remainder2Coefficient0Chunk12 +
  remainder2Coefficient0Chunk13 +
  remainder2Coefficient0Chunk14

/-- Internal datum. -/ def remainder2Coefficient0 : Coefficient :=
  remainder2Coefficient0Block0 +
  remainder2Coefficient0Block1

/-- Internal datum. -/ def remainder2Coefficient1Chunk0 : Coefficient :=
  coefficientTerm 114
    (-((2329 : ℚ))) +
  coefficientTerm 113
    (-((73283682580 : ℚ))) +
  coefficientTerm 112
    (-((9175063979244366 : ℚ))) +
  coefficientTerm 111
    (-((78293151035390302222 : ℚ))) +
  coefficientTerm 110
    (-((111124234857222285699352 : ℚ))) +
  coefficientTerm 109
    (-((20468171030108376511660993 : ℚ))) +
  coefficientTerm 108
    (23812113619150826247011739581 : ℚ) +
  coefficientTerm 107
    (12298617856096924713735520959259 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient1Chunk1 : Coefficient :=
  coefficientTerm 106
    (2347813443240803839127253112182995 : ℚ) +
  coefficientTerm 105
    (215088728471684776815229998500189364 : ℚ) +
  coefficientTerm 104
    ((9 : ℚ) * 10 ^ 36 +
      870924355153883672137796042767009143) +
  coefficientTerm 103
    ((210 : ℚ) * 10 ^ 36 +
      462081499466225006966235727856020684) +
  coefficientTerm 102
    ((1144 : ℚ) * 10 ^ 36 +
      241126005859139820446988485301202837) +
  coefficientTerm 101
    (-(((22496 : ℚ) * 10 ^ 36 +
      275929643517102918964098425632497513))) +
  coefficientTerm 100
    (-(((203715 : ℚ) * 10 ^ 36 +
      578909439757211547426606478810966882))) +
  coefficientTerm 99
    ((1821472 : ℚ) * 10 ^ 36 +
      109026745853271440556631226373021314)

/-- Internal datum. -/ def remainder2Coefficient1Chunk2 : Coefficient :=
  coefficientTerm 98
    ((12289823 : ℚ) * 10 ^ 36 +
      024352319415238577752859155764127964) +
  coefficientTerm 97
    (-(((125889998 : ℚ) * 10 ^ 36 +
      764741537441282873874599122737960653))) +
  coefficientTerm 96
    (-(((207268398 : ℚ) * 10 ^ 36 +
      832040207310409423826418713155088422))) +
  coefficientTerm 95
    ((5339749916 : ℚ) * 10 ^ 36 +
      684606161901804394069140621433038988) +
  coefficientTerm 94
    (-(((12329058152 : ℚ) * 10 ^ 36 +
      593188306493045475100783041995331638))) +
  coefficientTerm 93
    (-(((93293421963 : ℚ) * 10 ^ 36 +
      792147238755174843943741047526616373))) +
  coefficientTerm 92
    ((623068481933 : ℚ) * 10 ^ 36 +
      135245171317251061364802624893518330) +
  coefficientTerm 91
    (-(((607134815894 : ℚ) * 10 ^ 36 +
      910500975852149592281370663107412836)))

/-- Internal datum. -/ def remainder2Coefficient1Chunk3 : Coefficient :=
  coefficientTerm 90
    (-(((7861858706611 : ℚ) * 10 ^ 36 +
      913241008138397025016936982623538323))) +
  coefficientTerm 89
    ((38405088775242 : ℚ) * 10 ^ 36 +
      791785444052145651662155661340450784) +
  coefficientTerm 88
    (-(((46006234319931 : ℚ) * 10 ^ 36 +
      267767611476462716704253784042788995))) +
  coefficientTerm 87
    (-(((253453885906353 : ℚ) * 10 ^ 36 +
      008237761915978949606214749541567482))) +
  coefficientTerm 86
    ((1387738389012733 : ℚ) * 10 ^ 36 +
      836035583938650539472586594932267953) +
  coefficientTerm 85
    (-(((2839128411816168 : ℚ) * 10 ^ 36 +
      015048852376996962813972555961860067))) +
  coefficientTerm 84
    (-(((677576951413359 : ℚ) * 10 ^ 36 +
      118440884308755013409422520100772299))) +
  coefficientTerm 83
    ((22403057824211929 : ℚ) * 10 ^ 36 +
      525907520032123867309614792448565037)

/-- Internal datum. -/ def remainder2Coefficient1Chunk4 : Coefficient :=
  coefficientTerm 82
    (-(((73602963982873250 : ℚ) * 10 ^ 36 +
      007940517693601404642619624498649232))) +
  coefficientTerm 81
    ((122554917084065300 : ℚ) * 10 ^ 36 +
      320853867687274009809457937145411774) +
  coefficientTerm 80
    (-(((27628561411336868 : ℚ) * 10 ^ 36 +
      244991961003430565766835296129033560))) +
  coefficientTerm 79
    (-(((481557911681160080 : ℚ) * 10 ^ 36 +
      760038815346420927989652033326333172))) +
  coefficientTerm 78
    ((1626590872137609006 : ℚ) * 10 ^ 36 +
      190680264567211411675349780746126932) +
  coefficientTerm 77
    (-(((3108456926656432728 : ℚ) * 10 ^ 36 +
      504324865398422107582029442310965890))) +
  coefficientTerm 76
    ((3555925959456983574 : ℚ) * 10 ^ 36 +
      221159675035807265379863913865233933) +
  coefficientTerm 75
    (-(((576856191188187954 : ℚ) * 10 ^ 36 +
      714640719003699400531614494547848943)))

/-- Internal datum. -/ def remainder2Coefficient1Chunk5 : Coefficient :=
  coefficientTerm 74
    (-(((7829781767072193790 : ℚ) * 10 ^ 36 +
      940614855451749192419440213868793672))) +
  coefficientTerm 73
    ((20708736458340767299 : ℚ) * 10 ^ 36 +
      850218004237134122253863187163857273) +
  coefficientTerm 72
    (-(((32375243055288744739 : ℚ) * 10 ^ 36 +
      408246882573607354938322171631554325))) +
  coefficientTerm 71
    ((34112584794954398266 : ℚ) * 10 ^ 36 +
      833056348304426407178408948479890064) +
  coefficientTerm 70
    (-(((19868974027110136494 : ℚ) * 10 ^ 36 +
      621511363444536279163445865749406305))) +
  coefficientTerm 69
    (-(((7711495254258528833 : ℚ) * 10 ^ 36 +
      921041862212817265626987881284362859))) +
  coefficientTerm 68
    ((36645672164894523053 : ℚ) * 10 ^ 36 +
      962831347859804107942099887637523889) +
  coefficientTerm 67
    (-(((52531240047776006889 : ℚ) * 10 ^ 36 +
      528378892265661634330595770235940584)))

/-- Internal datum. -/ def remainder2Coefficient1Chunk6 : Coefficient :=
  coefficientTerm 66
    ((48304516639352681316 : ℚ) * 10 ^ 36 +
      629944664412575412448947881980741219) +
  coefficientTerm 65
    (-(((28791247917155730095 : ℚ) * 10 ^ 36 +
      191731668190079515844489164587793391))) +
  coefficientTerm 64
    ((6339784595116002229 : ℚ) * 10 ^ 36 +
      604274733098828450965141109605473566) +
  coefficientTerm 63
    ((8258351480991784408 : ℚ) * 10 ^ 36 +
      067572220378167800052511981920027684) +
  coefficientTerm 62
    (-(((11860302118566559246 : ℚ) * 10 ^ 36 +
      669520438814952811433639321036215419))) +
  coefficientTerm 61
    ((8245603275267371716 : ℚ) * 10 ^ 36 +
      190936967846421293904322573578120047) +
  coefficientTerm 60
    (-(((3125222676151354777 : ℚ) * 10 ^ 36 +
      987688904098109556790764257035467612))) +
  coefficientTerm 59
    (-(((51871866980317366 : ℚ) * 10 ^ 36 +
      272367580474309106861221427576714072)))

/-- Internal datum. -/ def remainder2Coefficient1Chunk7 : Coefficient :=
  coefficientTerm 58
    ((908998126415325120 : ℚ) * 10 ^ 36 +
      637565211799562731984882044711349612) +
  coefficientTerm 57
    (-(((595906504110546317 : ℚ) * 10 ^ 36 +
      847580435390630519293736106243862022))) +
  coefficientTerm 56
    ((156122700235894541 : ℚ) * 10 ^ 36 +
      215359928419238137620803549708792141) +
  coefficientTerm 55
    ((38708632590349550 : ℚ) * 10 ^ 36 +
      038909320209836313832035801399688659) +
  coefficientTerm 54
    (-(((51060801395036558 : ℚ) * 10 ^ 36 +
      645419750914266778279505713183364077))) +
  coefficientTerm 53
    ((17552225484796966 : ℚ) * 10 ^ 36 +
      209684620157723463839167888348993832) +
  coefficientTerm 52
    ((876307759424208 : ℚ) * 10 ^ 36 +
      137110477158844935261665956234512959) +
  coefficientTerm 51
    (-(((3146619741164609 : ℚ) * 10 ^ 36 +
      779553998395203135504539567542823798)))

/-- Internal datum. -/ def remainder2Coefficient1Chunk8 : Coefficient :=
  coefficientTerm 50
    ((1064558347078202 : ℚ) * 10 ^ 36 +
      935519998281089920262378412868830515) +
  coefficientTerm 49
    ((63358724873144 : ℚ) * 10 ^ 36 +
      633399933389938629023169622069684614) +
  coefficientTerm 48
    (-(((158544148055671 : ℚ) * 10 ^ 36 +
      054942981428221540990703068279312848))) +
  coefficientTerm 47
    ((39376151809298 : ℚ) * 10 ^ 36 +
      759682298403303322297574478351376786) +
  coefficientTerm 46
    ((7319164040280 : ℚ) * 10 ^ 36 +
      728673013255566132109193578495146294) +
  coefficientTerm 45
    (-(((6037767278326 : ℚ) * 10 ^ 36 +
      563296666525835768529343305035119745))) +
  coefficientTerm 44
    ((648401638615 : ℚ) * 10 ^ 36 +
      966186456668747610539522190161225558) +
  coefficientTerm 43
    ((432112768142 : ℚ) * 10 ^ 36 +
      442353814148894616481470942321809786)

/-- Internal datum. -/ def remainder2Coefficient1Chunk9 : Coefficient :=
  coefficientTerm 42
    (-(((139165872516 : ℚ) * 10 ^ 36 +
      838418896158854667393896510709872301))) +
  coefficientTerm 41
    (-(((11789716434 : ℚ) * 10 ^ 36 +
      675680598066479227024573301751833031))) +
  coefficientTerm 40
    ((12602628389 : ℚ) * 10 ^ 36 +
      526258851354891566204867902883476569) +
  coefficientTerm 39
    (-(((895207211 : ℚ) * 10 ^ 36 +
      253094452398187469388442171570590165))) +
  coefficientTerm 38
    (-(((744345593 : ℚ) * 10 ^ 36 +
      375753309946174316548546440583310611))) +
  coefficientTerm 37
    ((138143825 : ℚ) * 10 ^ 36 +
      322861061374501546913615689092833736) +
  coefficientTerm 36
    ((30845305 : ℚ) * 10 ^ 36 +
      703298606992929688144684386050348722) +
  coefficientTerm 35
    (-(((10178800 : ℚ) * 10 ^ 36 +
      343993652398732960755834833985355521)))

/-- Internal datum. -/ def remainder2Coefficient1Chunk10 : Coefficient :=
  coefficientTerm 34
    (-(((866296 : ℚ) * 10 ^ 36 +
      460575465796670455267867388753669369))) +
  coefficientTerm 33
    ((537688 : ℚ) * 10 ^ 36 +
      842212710594891401914117782804026329) +
  coefficientTerm 32
    ((12149 : ℚ) * 10 ^ 36 +
      129729855203374463191490851350845219) +
  coefficientTerm 31
    (-(((22434 : ℚ) * 10 ^ 36 +
      483518242757074625435655352319831718))) +
  coefficientTerm 30
    ((169 : ℚ) * 10 ^ 36 +
      100928911810487969607712933238095601) +
  coefficientTerm 29
    ((782 : ℚ) * 10 ^ 36 +
      884778513075620609733485006308898812) +
  coefficientTerm 28
    (-(((16 : ℚ) * 10 ^ 36 +
      302087361960395159433645119209771205))) +
  coefficientTerm 27
    (-(((22 : ℚ) * 10 ^ 36 +
      337226396841398490007237712497405760)))

/-- Internal datum. -/ def remainder2Coefficient1Chunk11 : Coefficient :=
  coefficientTerm 26
    (268943619019748947580124367300453358 : ℚ) +
  coefficientTerm 25
    (563370211501071328312802386841574086 : ℚ) +
  coefficientTerm 24
    (-((2125560260375172499905965264154931 : ℚ))) +
  coefficientTerm 23
    (-((10229350116733897326878981007695336 : ℚ))) +
  coefficientTerm 22
    (-((338050950523730163560503266156439 : ℚ))) +
  coefficientTerm 21
    (166980362579297990515818353437658 : ℚ) +
  coefficientTerm 20
    (7423831494855042805865550540966 : ℚ) +
  coefficientTerm 19
    (-((1476675698552842302366816083544 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient1Chunk12 : Coefficient :=
  coefficientTerm 18
    (-((152159977597680694262199235725 : ℚ))) +
  coefficientTerm 17
    (9371219754866468327646862794 : ℚ) +
  coefficientTerm 16
    (1336715720568965017819040794 : ℚ) +
  coefficientTerm 15
    (-((800944141195000428913534 : ℚ))) +
  coefficientTerm 14
    (-((7159433264249329204390444 : ℚ))) +
  coefficientTerm 13
    (-((230250439109250632924208 : ℚ))) +
  coefficientTerm 12
    (14904717066199156916092 : ℚ) +
  coefficientTerm 11
    (1057485838428164119588 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient1Chunk13 : Coefficient :=
  coefficientTerm 10
    (-((1401006467656754001 : ℚ))) +
  coefficientTerm 9
    (-((1511187499165252688 : ℚ))) +
  coefficientTerm 8
    (-((24940064428596179 : ℚ))) +
  coefficientTerm 7
    (809774120213950 : ℚ) +
  coefficientTerm 6
    (12713487257368 : ℚ) +
  coefficientTerm 5
    (-((182010007593 : ℚ))) +
  coefficientTerm 4
    (34314719 : ℚ) +
  coefficientTerm 3
    (991446 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient1Chunk14 : Coefficient :=
  coefficientTerm 2
    (-((23 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient1Block0 : Coefficient :=
  remainder2Coefficient1Chunk0 +
  remainder2Coefficient1Chunk1 +
  remainder2Coefficient1Chunk2 +
  remainder2Coefficient1Chunk3 +
  remainder2Coefficient1Chunk4 +
  remainder2Coefficient1Chunk5 +
  remainder2Coefficient1Chunk6 +
  remainder2Coefficient1Chunk7 +
  remainder2Coefficient1Chunk8 +
  remainder2Coefficient1Chunk9 +
  remainder2Coefficient1Chunk10 +
  remainder2Coefficient1Chunk11

/-- Internal datum. -/ def remainder2Coefficient1Block1 : Coefficient :=
  remainder2Coefficient1Chunk12 +
  remainder2Coefficient1Chunk13 +
  remainder2Coefficient1Chunk14

/-- Internal datum. -/ def remainder2Coefficient1 : Coefficient :=
  remainder2Coefficient1Block0 +
  remainder2Coefficient1Block1

/-- Internal datum. -/ def remainder2Coefficient2Chunk0 : Coefficient :=
  coefficientTerm 110
    (-((51573 : ℚ))) +
  coefficientTerm 109
    (-((652050755124 : ℚ))) +
  coefficientTerm 108
    (-((64927904208095868 : ℚ))) +
  coefficientTerm 107
    (-((501779026264199559586 : ℚ))) +
  coefficientTerm 106
    (-((670159624643932408123725 : ℚ))) +
  coefficientTerm 105
    (-((107108246602948219627108488 : ℚ))) +
  coefficientTerm 104
    (146759985850387230726504100304 : ℚ) +
  coefficientTerm 103
    (72409407582781145483944263813939 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient2Chunk1 : Coefficient :=
  coefficientTerm 102
    (13434993855594595313200186766745995 : ℚ) +
  coefficientTerm 101
    ((1 : ℚ) * 10 ^ 36 +
      194637032435987553021206513879586759) +
  coefficientTerm 100
    ((52 : ℚ) * 10 ^ 36 +
      670107788284021450360302716996142061) +
  coefficientTerm 99
    ((1048 : ℚ) * 10 ^ 36 +
      169345467189834459223669999805388521) +
  coefficientTerm 98
    ((4276 : ℚ) * 10 ^ 36 +
      345107771543602977611056688013695730) +
  coefficientTerm 97
    (-(((116373 : ℚ) * 10 ^ 36 +
      663553683193134387288647362283835662))) +
  coefficientTerm 96
    (-(((689559 : ℚ) * 10 ^ 36 +
      839019331475392630310000210966082902))) +
  coefficientTerm 95
    ((9544487 : ℚ) * 10 ^ 36 +
      399330554757158676424051318793601079)

/-- Internal datum. -/ def remainder2Coefficient2Chunk2 : Coefficient :=
  coefficientTerm 94
    ((24059355 : ℚ) * 10 ^ 36 +
      725455180799042198705904480461043314) +
  coefficientTerm 93
    (-(((550456158 : ℚ) * 10 ^ 36 +
      562506653336621803130388165662931223))) +
  coefficientTerm 92
    ((1018240205 : ℚ) * 10 ^ 36 +
      477540412855822089176105472928755355) +
  coefficientTerm 91
    ((14273231565 : ℚ) * 10 ^ 36 +
      335481826853527373072799059188163149) +
  coefficientTerm 90
    (-(((89078533405 : ℚ) * 10 ^ 36 +
      378437777254629262643671836316543284))) +
  coefficientTerm 89
    ((66396338492 : ℚ) * 10 ^ 36 +
      958840384238440883040076839006179064) +
  coefficientTerm 88
    ((1389497926404 : ℚ) * 10 ^ 36 +
      098434424065074976543906675101571844) +
  coefficientTerm 87
    (-(((7166161881916 : ℚ) * 10 ^ 36 +
      544493302082240165449128387975205734)))

/-- Internal datum. -/ def remainder2Coefficient2Chunk3 : Coefficient :=
  coefficientTerm 86
    ((13102113428101 : ℚ) * 10 ^ 36 +
      739796171669897021044885004664461850) +
  coefficientTerm 85
    ((20563020833383 : ℚ) * 10 ^ 36 +
      032925395632527410479791988032434095) +
  coefficientTerm 84
    (-(((196557836642283 : ℚ) * 10 ^ 36 +
      534697047644211206516321439411057301))) +
  coefficientTerm 83
    ((632998791593481 : ℚ) * 10 ^ 36 +
      447936066519187729024708835012469759) +
  coefficientTerm 82
    (-(((1331274173456511 : ℚ) * 10 ^ 36 +
      907919438594725763820832158714577799))) +
  coefficientTerm 81
    ((2065896304835761 : ℚ) * 10 ^ 36 +
      649251943716831980866030577957515476) +
  coefficientTerm 80
    (-(((1617129208214525 : ℚ) * 10 ^ 36 +
      261381795868878109914024559996222055))) +
  coefficientTerm 79
    (-(((6678185887679113 : ℚ) * 10 ^ 36 +
      978879893779456996358285735532600831)))

/-- Internal datum. -/ def remainder2Coefficient2Chunk4 : Coefficient :=
  coefficientTerm 78
    ((45386360278023680 : ℚ) * 10 ^ 36 +
      013645700893079549808710348930548432) +
  coefficientTerm 77
    (-(((157372325343559923 : ℚ) * 10 ^ 36 +
      726323337127466549384192698639398583))) +
  coefficientTerm 76
    ((366584368401704101 : ℚ) * 10 ^ 36 +
      976277645531771262385353107940980624) +
  coefficientTerm 75
    (-(((564991016999692029 : ℚ) * 10 ^ 36 +
      446018764889757617938403701678078705))) +
  coefficientTerm 74
    ((392237688207879363 : ℚ) * 10 ^ 36 +
      919257997622336249148473105005286291) +
  coefficientTerm 73
    ((686483490383149098 : ℚ) * 10 ^ 36 +
      892806185938995976957503070727261056) +
  coefficientTerm 72
    (-(((2931457099463060316 : ℚ) * 10 ^ 36 +
      626122280353009607683105193437588786))) +
  coefficientTerm 71
    ((5705497207972873863 : ℚ) * 10 ^ 36 +
      741156262146288455918503051039592232)

/-- Internal datum. -/ def remainder2Coefficient2Chunk5 : Coefficient :=
  coefficientTerm 70
    (-(((7326604306273382998 : ℚ) * 10 ^ 36 +
      540856475689939289657453030792291754))) +
  coefficientTerm 69
    ((5947980221735283329 : ℚ) * 10 ^ 36 +
      079546034089217488608089251159226427) +
  coefficientTerm 68
    (-(((1106074003431348533 : ℚ) * 10 ^ 36 +
      038327988318116756271265310580429811))) +
  coefficientTerm 67
    (-(((5380934413382372225 : ℚ) * 10 ^ 36 +
      945705328385940434925030704175890371))) +
  coefficientTerm 66
    ((10271392080142350163 : ℚ) * 10 ^ 36 +
      400890538150244156413129354716463194) +
  coefficientTerm 65
    (-(((11095624211693200169 : ℚ) * 10 ^ 36 +
      626657433590882947061261860714791864))) +
  coefficientTerm 64
    ((7885431843716856959 : ℚ) * 10 ^ 36 +
      097308802487289055487254456220717047) +
  coefficientTerm 63
    (-(((2955020422515185124 : ℚ) * 10 ^ 36 +
      782343060600033722414367750058355978)))

/-- Internal datum. -/ def remainder2Coefficient2Chunk6 : Coefficient :=
  coefficientTerm 62
    (-(((960911468360702951 : ℚ) * 10 ^ 36 +
      128952679877965771978837619685617985))) +
  coefficientTerm 61
    ((2509200902385440664 : ℚ) * 10 ^ 36 +
      953022249445148973518340614987880093) +
  coefficientTerm 60
    (-(((2098753766765376407 : ℚ) * 10 ^ 36 +
      345665535213072040606392112829547991))) +
  coefficientTerm 59
    ((978196998031577665 : ℚ) * 10 ^ 36 +
      015792587746535197881512952913834490) +
  coefficientTerm 58
    (-(((125530495858012148 : ℚ) * 10 ^ 36 +
      433203924611989214856807873955938686))) +
  coefficientTerm 57
    (-(((187699197498287563 : ℚ) * 10 ^ 36 +
      968038848157611949857405459666624355))) +
  coefficientTerm 56
    ((160256410638548767 : ℚ) * 10 ^ 36 +
      738242077468342234931330147932565108) +
  coefficientTerm 55
    (-(((55264383613182431 : ℚ) * 10 ^ 36 +
      624803628335662273260436933996676443)))

/-- Internal datum. -/ def remainder2Coefficient2Chunk7 : Coefficient :=
  coefficientTerm 54
    (-(((3359642529712813 : ℚ) * 10 ^ 36 +
      552784602758031437157300360833007150))) +
  coefficientTerm 53
    ((12919974019283142 : ℚ) * 10 ^ 36 +
      044299163386735064499292846351870647) +
  coefficientTerm 52
    (-(((5647611372358746 : ℚ) * 10 ^ 36 +
      763496541225068797862088473076319126))) +
  coefficientTerm 51
    ((286105840767256 : ℚ) * 10 ^ 36 +
      631723520274510890065023572362924729) +
  coefficientTerm 50
    ((793414301057079 : ℚ) * 10 ^ 36 +
      276958444135752994668657004652391566) +
  coefficientTerm 49
    (-(((344058533433772 : ℚ) * 10 ^ 36 +
      745293613097758239454232314009302575))) +
  coefficientTerm 48
    ((8750926432463 : ℚ) * 10 ^ 36 +
      064317977843549196908261718546612891) +
  coefficientTerm 47
    ((42291960744969 : ℚ) * 10 ^ 36 +
      586573911774792841144736581005599284)

/-- Internal datum. -/ def remainder2Coefficient2Chunk8 : Coefficient :=
  coefficientTerm 46
    (-(((13522380586587 : ℚ) * 10 ^ 36 +
      904137675170102049123376972642598255))) +
  coefficientTerm 45
    (-(((1198159366924 : ℚ) * 10 ^ 36 +
      519362911282886347893563461138591211))) +
  coefficientTerm 44
    ((1744552560514 : ℚ) * 10 ^ 36 +
      683292522850401633464103487164073490) +
  coefficientTerm 43
    (-(((272368018417 : ℚ) * 10 ^ 36 +
      738155386465688834341829656727182307))) +
  coefficientTerm 42
    (-(((107804191716 : ℚ) * 10 ^ 36 +
      905270671379301045017348646752444777))) +
  coefficientTerm 41
    ((43883561445 : ℚ) * 10 ^ 36 +
      677244621270552241179903867916776540) +
  coefficientTerm 40
    ((1470706088 : ℚ) * 10 ^ 36 +
      616565346583942807448141460401188945) +
  coefficientTerm 39
    (-(((3579749608 : ℚ) * 10 ^ 36 +
      066737552394659611752271346887827974)))

/-- Internal datum. -/ def remainder2Coefficient2Chunk9 : Coefficient :=
  coefficientTerm 38
    ((378998640 : ℚ) * 10 ^ 36 +
      258419723632070884120051362325277745) +
  coefficientTerm 37
    ((192741970 : ℚ) * 10 ^ 36 +
      197878757144563539088813369313968168) +
  coefficientTerm 36
    (-(((44072802 : ℚ) * 10 ^ 36 +
      935403696670155203768536842732121167))) +
  coefficientTerm 35
    (-(((6992542 : ℚ) * 10 ^ 36 +
      448096665025565927640957960661978556))) +
  coefficientTerm 34
    ((2934737 : ℚ) * 10 ^ 36 +
      362609721978989121199535211802940135) +
  coefficientTerm 33
    ((141516 : ℚ) * 10 ^ 36 +
      256736775030680012138512082832312497) +
  coefficientTerm 32
    (-(((143971 : ℚ) * 10 ^ 36 +
      490148075201103356211213635554595906))) +
  coefficientTerm 31
    ((1277 : ℚ) * 10 ^ 36 +
      630644490436651545302781724918563567)

/-- Internal datum. -/ def remainder2Coefficient2Chunk10 : Coefficient :=
  coefficientTerm 30
    ((5594 : ℚ) * 10 ^ 36 +
      738952022077263553172674468414526285) +
  coefficientTerm 29
    (-(((225 : ℚ) * 10 ^ 36 +
      651086921399577429239301721385471573))) +
  coefficientTerm 28
    (-(((182 : ℚ) * 10 ^ 36 +
      892475529011048951487063637634553314))) +
  coefficientTerm 27
    ((10 : ℚ) * 10 ^ 36 +
      977775776437172250288677711940278903) +
  coefficientTerm 26
    ((4 : ℚ) * 10 ^ 36 +
      809921067274839057864714570624963506) +
  coefficientTerm 25
    (-((272065361572137179529501208609249331 : ℚ))) +
  coefficientTerm 24
    (-((120219085005287976859016785080841404 : ℚ))) +
  coefficientTerm 23
    (7168047773872259887036010762730379 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient2Chunk11 : Coefficient :=
  coefficientTerm 22
    (1998385302311546909527456011604480 : ℚ) +
  coefficientTerm 21
    (-((44113655110558033415564496971977 : ℚ))) +
  coefficientTerm 20
    (-((39010431621283220839231554468746 : ℚ))) +
  coefficientTerm 19
    (928321599646397579187788779389 : ℚ) +
  coefficientTerm 18
    (357912551995618314750281664824 : ℚ) +
  coefficientTerm 17
    (10609409481487786287893449330 : ℚ) +
  coefficientTerm 16
    (-((3838383077263422427097601024 : ℚ))) +
  coefficientTerm 15
    (-((100565161540304756843088699 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient2Chunk12 : Coefficient :=
  coefficientTerm 14
    (15998025457352783001220174 : ℚ) +
  coefficientTerm 13
    (1038308847642591349427606 : ℚ) +
  coefficientTerm 12
    (-((44370403879186022184327 : ℚ))) +
  coefficientTerm 11
    (-((3305729713116580021438 : ℚ))) +
  coefficientTerm 10
    (44894677717832501843 : ℚ) +
  coefficientTerm 9
    (4429251272553627031 : ℚ) +
  coefficientTerm 8
    (-((53104121001510770 : ℚ))) +
  coefficientTerm 7
    (-((1634796781931808 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient2Chunk13 : Coefficient :=
  coefficientTerm 6
    (64443948614929 : ℚ) +
  coefficientTerm 5
    (-((726119201869 : ℚ))) +
  coefficientTerm 4
    (-((1179368522 : ℚ))) +
  coefficientTerm 3
    (18508415 : ℚ) +
  coefficientTerm 2
    (-((4313 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient2Block0 : Coefficient :=
  remainder2Coefficient2Chunk0 +
  remainder2Coefficient2Chunk1 +
  remainder2Coefficient2Chunk2 +
  remainder2Coefficient2Chunk3 +
  remainder2Coefficient2Chunk4 +
  remainder2Coefficient2Chunk5 +
  remainder2Coefficient2Chunk6 +
  remainder2Coefficient2Chunk7 +
  remainder2Coefficient2Chunk8 +
  remainder2Coefficient2Chunk9 +
  remainder2Coefficient2Chunk10 +
  remainder2Coefficient2Chunk11

/-- Internal datum. -/ def remainder2Coefficient2Block1 : Coefficient :=
  remainder2Coefficient2Chunk12 +
  remainder2Coefficient2Chunk13

/-- Internal datum. -/ def remainder2Coefficient2 : Coefficient :=
  remainder2Coefficient2Block0 +
  remainder2Coefficient2Block1

/-- Internal datum. -/ def remainder2Coefficient3Chunk0 : Coefficient :=
  coefficientTerm 106
    (-((794294 : ℚ))) +
  coefficientTerm 105
    (-((3772299553634 : ℚ))) +
  coefficientTerm 104
    (-((267857578388844983 : ℚ))) +
  coefficientTerm 103
    (-((1765206011740968795608 : ℚ))) +
  coefficientTerm 102
    (-((2132096922036802698650356 : ℚ))) +
  coefficientTerm 101
    (-((258756034495996674981616083 : ℚ))) +
  coefficientTerm 100
    (482011122008097505290949836698 : ℚ) +
  coefficientTerm 99
    (222522177019934397987749429416808 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient3Chunk1 : Coefficient :=
  coefficientTerm 98
    (39742507950836905779404512839757906 : ℚ) +
  coefficientTerm 97
    ((3 : ℚ) * 10 ^ 36 +
      415621928189986890998128674465258779) +
  coefficientTerm 96
    ((144 : ℚ) * 10 ^ 36 +
      957512445012928435501885822570771046) +
  coefficientTerm 95
    ((2730 : ℚ) * 10 ^ 36 +
      140599159216551065616103945835624732) +
  coefficientTerm 94
    ((8991 : ℚ) * 10 ^ 36 +
      237744046789505603825182565214706852) +
  coefficientTerm 93
    (-(((292540 : ℚ) * 10 ^ 36 +
      411516541400976854683925085011124788))) +
  coefficientTerm 92
    (-(((1241360 : ℚ) * 10 ^ 36 +
      921762821318591252624819852067585689))) +
  coefficientTerm 91
    ((22019885 : ℚ) * 10 ^ 36 +
      059282066352198371338729758987417033)

/-- Internal datum. -/ def remainder2Coefficient3Chunk2 : Coefficient :=
  coefficientTerm 90
    ((11753883 : ℚ) * 10 ^ 36 +
      545940184043689853651614097074310681) +
  coefficientTerm 89
    (-(((995591552 : ℚ) * 10 ^ 36 +
      697449920616804017169423479210992753))) +
  coefficientTerm 88
    ((3490413213 : ℚ) * 10 ^ 36 +
      896667872921484488540653929129509249) +
  coefficientTerm 87
    ((13779964434 : ℚ) * 10 ^ 36 +
      773641076795436769502131326743233685) +
  coefficientTerm 86
    (-(((141326484419 : ℚ) * 10 ^ 36 +
      013466682318415823838359102645815341))) +
  coefficientTerm 85
    ((336721822876 : ℚ) * 10 ^ 36 +
      300553696392160754947126360892447982) +
  coefficientTerm 84
    ((926599088367 : ℚ) * 10 ^ 36 +
      198945920418698771499128199733035260) +
  coefficientTerm 83
    (-(((8747969004708 : ℚ) * 10 ^ 36 +
      684199605992861862970138447612526507)))

/-- Internal datum. -/ def remainder2Coefficient3Chunk3 : Coefficient :=
  coefficientTerm 82
    ((24851537352247 : ℚ) * 10 ^ 36 +
      083860767221184131530805323720822241) +
  coefficientTerm 81
    (-(((7140027856396 : ℚ) * 10 ^ 36 +
      353107780592363086475355669233733768))) +
  coefficientTerm 80
    (-(((203349744888727 : ℚ) * 10 ^ 36 +
      517211709358660650029083115727665296))) +
  coefficientTerm 79
    ((839159059157663 : ℚ) * 10 ^ 36 +
      174522296883868759738485717148535281) +
  coefficientTerm 78
    (-(((1678360061583332 : ℚ) * 10 ^ 36 +
      653851771133247003577297695703634195))) +
  coefficientTerm 77
    ((830245972089719 : ℚ) * 10 ^ 36 +
      503095319268574266026478437444563336) +
  coefficientTerm 76
    ((6148808417178414 : ℚ) * 10 ^ 36 +
      816994974845600455137044668236983729) +
  coefficientTerm 75
    (-(((23922300774913644 : ℚ) * 10 ^ 36 +
      624801096610556066181099864130444627)))

/-- Internal datum. -/ def remainder2Coefficient3Chunk4 : Coefficient :=
  coefficientTerm 74
    ((49212362666451763 : ℚ) * 10 ^ 36 +
      724724451742959451554558004333520726) +
  coefficientTerm 73
    (-(((60110943040894486 : ℚ) * 10 ^ 36 +
      198742741258328108783002759133650284))) +
  coefficientTerm 72
    ((15764024619483439 : ℚ) * 10 ^ 36 +
      326093495308983445835761470859004150) +
  coefficientTerm 71
    ((119023298000490316 : ℚ) * 10 ^ 36 +
      931922150843289794983990553606648252) +
  coefficientTerm 70
    (-(((328582041573588224 : ℚ) * 10 ^ 36 +
      747298523953274430364919446483101658))) +
  coefficientTerm 69
    ((516912697505258064 : ℚ) * 10 ^ 36 +
      725658443400572658051263163444854079) +
  coefficientTerm 68
    (-(((540472668043227544 : ℚ) * 10 ^ 36 +
      901564871029126882753385776539977491))) +
  coefficientTerm 67
    ((307039001341708743 : ℚ) * 10 ^ 36 +
      292866630993907577620549133022106270)

/-- Internal datum. -/ def remainder2Coefficient3Chunk5 : Coefficient :=
  coefficientTerm 66
    ((128285820961084225 : ℚ) * 10 ^ 36 +
      455490897714271781640264571770333288) +
  coefficientTerm 65
    (-(((565007106884647134 : ℚ) * 10 ^ 36 +
      434957499720230902141386345251579967))) +
  coefficientTerm 64
    ((780972389252802949 : ℚ) * 10 ^ 36 +
      479690830881112451831860821719407528) +
  coefficientTerm 63
    (-(((686623311988715580 : ℚ) * 10 ^ 36 +
      285156571990752862180113043652979055))) +
  coefficientTerm 62
    ((379361394804245037 : ℚ) * 10 ^ 36 +
      899965367824579083277847555619049027) +
  coefficientTerm 61
    (-(((55673262195842482 : ℚ) * 10 ^ 36 +
      703446022644446419291453166881173181))) +
  coefficientTerm 60
    (-(((133590640082852617 : ℚ) * 10 ^ 36 +
      628624946301179103567220806508211600))) +
  coefficientTerm 59
    ((162413156184027760 : ℚ) * 10 ^ 36 +
      713153186952743394367606631091432890)

/-- Internal datum. -/ def remainder2Coefficient3Chunk6 : Coefficient :=
  coefficientTerm 58
    (-(((100248785764461368 : ℚ) * 10 ^ 36 +
      577107612512630767697897557742058640))) +
  coefficientTerm 57
    ((30175747630459063 : ℚ) * 10 ^ 36 +
      031095711692767385422885342369621140) +
  coefficientTerm 56
    ((6710727525884742 : ℚ) * 10 ^ 36 +
      257164468557671762523932017203572218) +
  coefficientTerm 55
    (-(((12769021039988110 : ℚ) * 10 ^ 36 +
      628010405073972212117566839200854058))) +
  coefficientTerm 54
    ((6528414277076057 : ℚ) * 10 ^ 36 +
      223769874840538652984052724118938262) +
  coefficientTerm 53
    (-(((981393607761442 : ℚ) * 10 ^ 36 +
      560978477872434481245809405708939563))) +
  coefficientTerm 52
    (-(((813491307248877 : ℚ) * 10 ^ 36 +
      463559718692386536313840641770494930))) +
  coefficientTerm 51
    ((592882251057240 : ℚ) * 10 ^ 36 +
      725870784756053567465215899867346951)

/-- Internal datum. -/ def remainder2Coefficient3Chunk7 : Coefficient :=
  coefficientTerm 50
    (-(((129417700013243 : ℚ) * 10 ^ 36 +
      732828864495397861779997637217283505))) +
  coefficientTerm 49
    (-(((42344753845482 : ℚ) * 10 ^ 36 +
      499724650697994842686063694746861454))) +
  coefficientTerm 48
    ((36471586247137 : ℚ) * 10 ^ 36 +
      802510340750755657550865252238338051) +
  coefficientTerm 47
    (-(((7193139565494 : ℚ) * 10 ^ 36 +
      378284995111613989859487638048123699))) +
  coefficientTerm 46
    (-(((2466916198420 : ℚ) * 10 ^ 36 +
      109254297779917252601204358032259112))) +
  coefficientTerm 45
    ((1666429559828 : ℚ) * 10 ^ 36 +
      701409885735644943615103733639282975) +
  coefficientTerm 44
    (-(((186243573966 : ℚ) * 10 ^ 36 +
      169544428262160522130926648718617077))) +
  coefficientTerm 43
    (-(((134953349921 : ℚ) * 10 ^ 36 +
      645771473991539178865612758973748641)))

/-- Internal datum. -/ def remainder2Coefficient3Chunk8 : Coefficient :=
  coefficientTerm 42
    ((51990963322 : ℚ) * 10 ^ 36 +
      906723698998517920121619253352666777) +
  coefficientTerm 41
    ((1616550411 : ℚ) * 10 ^ 36 +
      635808977878116633631418844750306089) +
  coefficientTerm 40
    (-(((5095472275 : ℚ) * 10 ^ 36 +
      444967680452415046527764847424531289))) +
  coefficientTerm 39
    ((802671472 : ℚ) * 10 ^ 36 +
      616779569307783777750692615093839523) +
  coefficientTerm 38
    ((278531489 : ℚ) * 10 ^ 36 +
      455583671983182498987984801222166978) +
  coefficientTerm 37
    (-(((103196802 : ℚ) * 10 ^ 36 +
      034186994620357192376772393313934948))) +
  coefficientTerm 36
    (-(((5972615 : ℚ) * 10 ^ 36 +
      649185960823655997056577502238520819))) +
  coefficientTerm 35
    ((7636922 : ℚ) * 10 ^ 36 +
      589519785821039428126710304963391474)

/-- Internal datum. -/ def remainder2Coefficient3Chunk9 : Coefficient :=
  coefficientTerm 34
    (-(((429472 : ℚ) * 10 ^ 36 +
      406512399769223982788343766418493177))) +
  coefficientTerm 33
    (-(((408975 : ℚ) * 10 ^ 36 +
      986341552459375411106638462660105392))) +
  coefficientTerm 32
    ((55384 : ℚ) * 10 ^ 36 +
      268122777797849118807530568108578721) +
  coefficientTerm 31
    ((17255 : ℚ) * 10 ^ 36 +
      211102769595505069781743533790106948) +
  coefficientTerm 30
    (-(((3554 : ℚ) * 10 ^ 36 +
      003684411565316456393508546234911994))) +
  coefficientTerm 29
    (-(((602 : ℚ) * 10 ^ 36 +
      614607404782543474794065438144304736))) +
  coefficientTerm 28
    ((161 : ℚ) * 10 ^ 36 +
      459061594926880905641512579200311762) +
  coefficientTerm 27
    ((19 : ℚ) * 10 ^ 36 +
      364984958319004293618854497598764168)

/-- Internal datum. -/ def remainder2Coefficient3Chunk10 : Coefficient :=
  coefficientTerm 26
    (-(((5 : ℚ) * 10 ^ 36 +
      891690741671953724981053994148980820))) +
  coefficientTerm 25
    (-((539992111689709489806039449053330902 : ℚ))) +
  coefficientTerm 24
    (155940408479648275346173351208713541 : ℚ) +
  coefficientTerm 23
    (17502796376348235058891317421237394 : ℚ) +
  coefficientTerm 22
    (-((3770195349740932032386184257945046 : ℚ))) +
  coefficientTerm 21
    (-((355895040729730830597860482259151 : ℚ))) +
  coefficientTerm 20
    (46104552010704738459147239845351 : ℚ) +
  coefficientTerm 19
    (9227650503192677672918781534744 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient3Chunk11 : Coefficient :=
  coefficientTerm 18
    (-((650549405351974257520118427995 : ℚ))) +
  coefficientTerm 17
    (-((101571790718327454660827242646 : ℚ))) +
  coefficientTerm 16
    (-((54569879067551627558148355 : ℚ))) +
  coefficientTerm 15
    (1205027831713483381382352925 : ℚ) +
  coefficientTerm 14
    (19081312682070323987420769 : ℚ) +
  coefficientTerm 13
    (-((5350675907080725328279101 : ℚ))) +
  coefficientTerm 12
    (-((323012681716189718208053 : ℚ))) +
  coefficientTerm 11
    (14495384085042601774868 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient3Chunk12 : Coefficient :=
  coefficientTerm 10
    (1186110264949517701774 : ℚ) +
  coefficientTerm 9
    (-((7664712791670880689 : ℚ))) +
  coefficientTerm 8
    (-((1890393992552803819 : ℚ))) +
  coefficientTerm 7
    (-((6226391170151878 : ℚ))) +
  coefficientTerm 6
    (1120623009347098 : ℚ) +
  coefficientTerm 5
    (-((1446040827081 : ℚ))) +
  coefficientTerm 4
    (-((114233123413 : ℚ))) +
  coefficientTerm 3
    (337210200 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient3Chunk13 : Coefficient :=
  coefficientTerm 2
    (144992 : ℚ) +
  coefficientTerm 1
    (-((60 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient3Block0 : Coefficient :=
  remainder2Coefficient3Chunk0 +
  remainder2Coefficient3Chunk1 +
  remainder2Coefficient3Chunk2 +
  remainder2Coefficient3Chunk3 +
  remainder2Coefficient3Chunk4 +
  remainder2Coefficient3Chunk5 +
  remainder2Coefficient3Chunk6 +
  remainder2Coefficient3Chunk7 +
  remainder2Coefficient3Chunk8 +
  remainder2Coefficient3Chunk9 +
  remainder2Coefficient3Chunk10 +
  remainder2Coefficient3Chunk11

/-- Internal datum. -/ def remainder2Coefficient3Block1 : Coefficient :=
  remainder2Coefficient3Chunk12 +
  remainder2Coefficient3Chunk13

/-- Internal datum. -/ def remainder2Coefficient3 : Coefficient :=
  remainder2Coefficient3Block0 +
  remainder2Coefficient3Block1

/-- Internal datum. -/ def remainder2Coefficient4Chunk0 : Coefficient :=
  coefficientTerm 102
    (-((9250026 : ℚ))) +
  coefficientTerm 101
    (-((16728815392683 : ℚ))) +
  coefficientTerm 100
    (-((755768532071763755 : ℚ))) +
  coefficientTerm 99
    (-((3878580211389726856884 : ℚ))) +
  coefficientTerm 98
    (-((3936944843241963325483716 : ℚ))) +
  coefficientTerm 97
    (-((215132251974574146416121296 : ℚ))) +
  coefficientTerm 96
    (939164548290806025064203691306 : ℚ) +
  coefficientTerm 95
    (390118339111116952445252584220795 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient4Chunk1 : Coefficient :=
  coefficientTerm 94
    (65698345123983352604138413107212789 : ℚ) +
  coefficientTerm 93
    ((5 : ℚ) * 10 ^ 36 +
      397653765049896892328607975682692166) +
  coefficientTerm 92
    ((220 : ℚ) * 10 ^ 36 +
      383357605673005449700582181334082101) +
  coefficientTerm 91
    ((3998 : ℚ) * 10 ^ 36 +
      392909408417154375212108573971126095) +
  coefficientTerm 90
    ((12319 : ℚ) * 10 ^ 36 +
      330366236617959699752080407913790123) +
  coefficientTerm 89
    (-(((403947 : ℚ) * 10 ^ 36 +
      522433154763994537377347421116546424))) +
  coefficientTerm 88
    (-(((1543504 : ℚ) * 10 ^ 36 +
      786611669941401850724286147096140207))) +
  coefficientTerm 87
    ((28253243 : ℚ) * 10 ^ 36 +
      546566767172168785893940385861585496)

/-- Internal datum. -/ def remainder2Coefficient4Chunk2 : Coefficient :=
  coefficientTerm 86
    ((1168967 : ℚ) * 10 ^ 36 +
      674723539927797550980063930000826216) +
  coefficientTerm 85
    (-(((1108541808 : ℚ) * 10 ^ 36 +
      326678930214575740370730576125023045))) +
  coefficientTerm 84
    ((4405610885 : ℚ) * 10 ^ 36 +
      467658215728651561274847243551785183) +
  coefficientTerm 83
    ((8766011014 : ℚ) * 10 ^ 36 +
      486695941776157846266783124975520055) +
  coefficientTerm 82
    (-(((125515986126 : ℚ) * 10 ^ 36 +
      920090053261260794941424373115036152))) +
  coefficientTerm 81
    ((391988867676 : ℚ) * 10 ^ 36 +
      424019441773103447860968897246402867) +
  coefficientTerm 80
    ((41103553665 : ℚ) * 10 ^ 36 +
      028866702092783573336178371067872994) +
  coefficientTerm 79
    (-(((4470227893646 : ℚ) * 10 ^ 36 +
      445815672202856041563204717756135371)))

/-- Internal datum. -/ def remainder2Coefficient4Chunk3 : Coefficient :=
  coefficientTerm 78
    ((16873132029904 : ℚ) * 10 ^ 36 +
      715975144283624084105259274856352785) +
  coefficientTerm 77
    (-(((28226822940414 : ℚ) * 10 ^ 36 +
      173111034757461886101215568527671949))) +
  coefficientTerm 76
    (-(((8425469595670 : ℚ) * 10 ^ 36 +
      461199404319368098727400289044590510))) +
  coefficientTerm 75
    ((180092494351645 : ℚ) * 10 ^ 36 +
      424091732349753438665506657826740768) +
  coefficientTerm 74
    (-(((535092720771623 : ℚ) * 10 ^ 36 +
      363396985167307577928365692065974083))) +
  coefficientTerm 73
    ((919773290386774 : ℚ) * 10 ^ 36 +
      278560369110956023102289357227011826) +
  coefficientTerm 72
    (-(((855610967830138 : ℚ) * 10 ^ 36 +
      214679424247973466442497801794595178))) +
  coefficientTerm 71
    (-(((355308909916774 : ℚ) * 10 ^ 36 +
      060665370153856512577405243427200776)))

/-- Internal datum. -/ def remainder2Coefficient4Chunk4 : Coefficient :=
  coefficientTerm 70
    ((3219440258276007 : ℚ) * 10 ^ 36 +
      637241900872819713062091450575441678) +
  coefficientTerm 69
    (-(((7445759028232835 : ℚ) * 10 ^ 36 +
      325223788537982047007543276937229425))) +
  coefficientTerm 68
    ((11415768083294728 : ℚ) * 10 ^ 36 +
      785940734875671568824441361346817452) +
  coefficientTerm 67
    (-(((12241834034897506 : ℚ) * 10 ^ 36 +
      887363455958967121012693100190156582))) +
  coefficientTerm 66
    ((7085160897111292 : ℚ) * 10 ^ 36 +
      059077791287867026927987327952014566) +
  coefficientTerm 65
    ((4325601937530417 : ℚ) * 10 ^ 36 +
      313343374923753902307504119361121808) +
  coefficientTerm 64
    (-(((17819254933458328 : ℚ) * 10 ^ 36 +
      320669253465733783739288751672154723))) +
  coefficientTerm 63
    ((26214602613453567 : ℚ) * 10 ^ 36 +
      649132125504002244590507094605348433)

/-- Internal datum. -/ def remainder2Coefficient4Chunk5 : Coefficient :=
  coefficientTerm 62
    (-(((24260889690025450 : ℚ) * 10 ^ 36 +
      128779071629645492560555871074703942))) +
  coefficientTerm 61
    ((13137889188370020 : ℚ) * 10 ^ 36 +
      679157083869417823052352801227592109) +
  coefficientTerm 60
    ((124873650185766 : ℚ) * 10 ^ 36 +
      338123408195979723000643560020942470) +
  coefficientTerm 59
    (-(((8203512958915321 : ℚ) * 10 ^ 36 +
      638917069527219780641033470636605772))) +
  coefficientTerm 58
    ((8760490003044905 : ℚ) * 10 ^ 36 +
      330957105454623115941276373458917434) +
  coefficientTerm 57
    (-(((4785959974880926 : ℚ) * 10 ^ 36 +
      339643565685229096339862358294612527))) +
  coefficientTerm 56
    ((742127755010771 : ℚ) * 10 ^ 36 +
      180546078381774652053372379927188243) +
  coefficientTerm 55
    ((1057521205019777 : ℚ) * 10 ^ 36 +
      592525830018825566490236496451057365)

/-- Internal datum. -/ def remainder2Coefficient4Chunk6 : Coefficient :=
  coefficientTerm 54
    (-(((966410230161405 : ℚ) * 10 ^ 36 +
      973775927755796471384338588517172481))) +
  coefficientTerm 53
    ((320673134121474 : ℚ) * 10 ^ 36 +
      499950016185509383657477202553957550) +
  coefficientTerm 52
    ((58164678579912 : ℚ) * 10 ^ 36 +
      948160930285935213101064005480685185) +
  coefficientTerm 51
    (-(((104159695137006 : ℚ) * 10 ^ 36 +
      962784475162704718105817439999544319))) +
  coefficientTerm 50
    ((37356252392369 : ℚ) * 10 ^ 36 +
      544133903144701282118686545444589085) +
  coefficientTerm 49
    ((4076918239957 : ℚ) * 10 ^ 36 +
      814399829082024624735469727184086254) +
  coefficientTerm 48
    (-(((8340536903252 : ℚ) * 10 ^ 36 +
      677298548724493654868460098424907864))) +
  coefficientTerm 47
    ((2318639987710 : ℚ) * 10 ^ 36 +
      616732879835244395478339063614734231)

/-- Internal datum. -/ def remainder2Coefficient4Chunk7 : Coefficient :=
  coefficientTerm 46
    ((535034283561 : ℚ) * 10 ^ 36 +
      283993430861041226970857196747060306) +
  coefficientTerm 45
    (-(((492964048180 : ℚ) * 10 ^ 36 +
      503567794237322887238239808056091730))) +
  coefficientTerm 44
    ((60699672912 : ℚ) * 10 ^ 36 +
      375196361252975647329068625681778521) +
  coefficientTerm 43
    ((46882454155 : ℚ) * 10 ^ 36 +
      572735710251684103067266472037240530) +
  coefficientTerm 42
    (-(((17328442228 : ℚ) * 10 ^ 36 +
      565544484785993690729563650850253531))) +
  coefficientTerm 41
    (-(((1692827534 : ℚ) * 10 ^ 36 +
      970199296655865543170820237029316689))) +
  coefficientTerm 40
    ((2053117137 : ℚ) * 10 ^ 36 +
      312446097252905665708171293294955350) +
  coefficientTerm 39
    (-(((159946346 : ℚ) * 10 ^ 36 +
      627034111492081833052243935085826347)))

/-- Internal datum. -/ def remainder2Coefficient4Chunk8 : Coefficient :=
  coefficientTerm 38
    (-(((158956189 : ℚ) * 10 ^ 36 +
      353983597640140225968330405329202570))) +
  coefficientTerm 37
    ((32298868 : ℚ) * 10 ^ 36 +
      767447754344864573417396398055540391) +
  coefficientTerm 36
    ((8787953 : ℚ) * 10 ^ 36 +
      787800057138534507392612999025079156) +
  coefficientTerm 35
    (-(((3089012 : ℚ) * 10 ^ 36 +
      035874903642467874332463622276635518))) +
  coefficientTerm 34
    (-(((348412 : ℚ) * 10 ^ 36 +
      100404979138215482684611103879238099))) +
  coefficientTerm 33
    ((212028 : ℚ) * 10 ^ 36 +
      110350396528738533651857411112191845) +
  coefficientTerm 32
    ((9159 : ℚ) * 10 ^ 36 +
      932449270445531476273128321321702802) +
  coefficientTerm 31
    (-(((11573 : ℚ) * 10 ^ 36 +
      839367349732358281411554026148918924)))

/-- Internal datum. -/ def remainder2Coefficient4Chunk9 : Coefficient :=
  coefficientTerm 30
    (-(((117 : ℚ) * 10 ^ 36 +
      040313349008727634316589506249842791))) +
  coefficientTerm 29
    ((526 : ℚ) * 10 ^ 36 +
      180748310193457410819886811775418595) +
  coefficientTerm 28
    (-((919451315218442547947728140666856922 : ℚ))) +
  coefficientTerm 27
    (-(((19 : ℚ) * 10 ^ 36 +
      964503768396229430711371608755978186))) +
  coefficientTerm 26
    (-((128962834558277521146661286351655984 : ℚ))) +
  coefficientTerm 25
    (653378206831544942846275668563282656 : ℚ) +
  coefficientTerm 24
    (11305178887891113532147551672536495 : ℚ) +
  coefficientTerm 23
    (-((15850906589950836393883262015590003 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient4Chunk10 : Coefficient :=
  coefficientTerm 22
    (-((995548660916269458131140851756424 : ℚ))) +
  coefficientTerm 21
    (366155791030503869533800181563968 : ℚ) +
  coefficientTerm 20
    (21083279719613282317534843566219 : ℚ) +
  coefficientTerm 19
    (-((3481706658519367446286379590379 : ℚ))) +
  coefficientTerm 18
    (-((761593636281390880971590410869 : ℚ))) +
  coefficientTerm 17
    (54895998869065053760926250741 : ℚ) +
  coefficientTerm 16
    (6122558870452026951957834792 : ℚ) +
  coefficientTerm 15
    (245658066250066217208463354 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient4Chunk11 : Coefficient :=
  coefficientTerm 14
    (-((87249910341251524126232233 : ℚ))) +
  coefficientTerm 13
    (-((1731033120215705441743047 : ℚ))) +
  coefficientTerm 12
    (200113653847991665364200 : ℚ) +
  coefficientTerm 11
    (26993499243638401662348 : ℚ) +
  coefficientTerm 10
    (-((337144865784472729422 : ℚ))) +
  coefficientTerm 9
    (-((65646022796329222704 : ℚ))) +
  coefficientTerm 8
    (-((1201518328513847068 : ℚ))) +
  coefficientTerm 7
    (75891265047055987 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient4Chunk12 : Coefficient :=
  coefficientTerm 6
    (1782788153023498 : ℚ) +
  coefficientTerm 5
    (-((30208061652185 : ℚ))) +
  coefficientTerm 4
    (-((437160397729 : ℚ))) +
  coefficientTerm 3
    (3515040321 : ℚ) +
  coefficientTerm 2
    (1844025 : ℚ) +
  coefficientTerm 1
    (-((4484 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient4Block0 : Coefficient :=
  remainder2Coefficient4Chunk0 +
  remainder2Coefficient4Chunk1 +
  remainder2Coefficient4Chunk2 +
  remainder2Coefficient4Chunk3 +
  remainder2Coefficient4Chunk4 +
  remainder2Coefficient4Chunk5 +
  remainder2Coefficient4Chunk6 +
  remainder2Coefficient4Chunk7 +
  remainder2Coefficient4Chunk8 +
  remainder2Coefficient4Chunk9 +
  remainder2Coefficient4Chunk10 +
  remainder2Coefficient4Chunk11

/-- Internal datum. -/ def remainder2Coefficient4Block1 : Coefficient :=
  remainder2Coefficient4Chunk12

/-- Internal datum. -/ def remainder2Coefficient4 : Coefficient :=
  remainder2Coefficient4Block0 +
  remainder2Coefficient4Block1

/-- Internal datum. -/ def remainder2Coefficient5Chunk0 : Coefficient :=
  coefficientTerm 98
    (-((84879584 : ℚ))) +
  coefficientTerm 97
    (-((62108676656411 : ℚ))) +
  coefficientTerm 96
    (-((1661458723421419362 : ℚ))) +
  coefficientTerm 95
    (-((6000547169591553991323 : ℚ))) +
  coefficientTerm 94
    (-((4534798300274140721268369 : ℚ))) +
  coefficientTerm 93
    (309822799767340730668764003 : ℚ) +
  coefficientTerm 92
    (1197901248587625823394131256191 : ℚ) +
  coefficientTerm 91
    (418819725802625644021293199369765 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient5Chunk1 : Coefficient :=
  coefficientTerm 90
    (63506625011524370119277185841139399 : ℚ) +
  coefficientTerm 89
    ((4 : ℚ) * 10 ^ 36 +
      809272671110001400826091023037899395) +
  coefficientTerm 88
    ((183 : ℚ) * 10 ^ 36 +
      377772338127822273190994703138876095) +
  coefficientTerm 87
    ((3122 : ℚ) * 10 ^ 36 +
      163349981012136172833905772391019781) +
  coefficientTerm 86
    ((8331 : ℚ) * 10 ^ 36 +
      610236584716832086290155981013157605) +
  coefficientTerm 85
    (-(((300251 : ℚ) * 10 ^ 36 +
      147139026137458381741843066253390545))) +
  coefficientTerm 84
    (-(((1019998 : ℚ) * 10 ^ 36 +
      825567616745605344467509616177727522))) +
  coefficientTerm 83
    ((19844078 : ℚ) * 10 ^ 36 +
      368367647479805269940340036920130269)

/-- Internal datum. -/ def remainder2Coefficient5Chunk2 : Coefficient :=
  coefficientTerm 82
    (-(((3671711 : ℚ) * 10 ^ 36 +
      776486332869099310649452547803580870))) +
  coefficientTerm 81
    (-(((733117506 : ℚ) * 10 ^ 36 +
      467283953626185539260366384756126532))) +
  coefficientTerm 80
    ((3002133683 : ℚ) * 10 ^ 36 +
      565988392458948980633539621521290947) +
  coefficientTerm 79
    ((5086554838 : ℚ) * 10 ^ 36 +
      729128011357916514757208966931108845) +
  coefficientTerm 78
    (-(((79970716861 : ℚ) * 10 ^ 36 +
      673357875251224597009651876784519597))) +
  coefficientTerm 77
    ((254735917876 : ℚ) * 10 ^ 36 +
      843325547217135374763303741153870467) +
  coefficientTerm 76
    ((3807677038 : ℚ) * 10 ^ 36 +
      252640414310368810121093925398743568) +
  coefficientTerm 75
    (-(((2776079750871 : ℚ) * 10 ^ 36 +
      447450040554150772889836624742403460)))

/-- Internal datum. -/ def remainder2Coefficient5Chunk3 : Coefficient :=
  coefficientTerm 74
    ((10467065061107 : ℚ) * 10 ^ 36 +
      254327435430760433350574226355396713) +
  coefficientTerm 73
    (-(((16752041284191 : ℚ) * 10 ^ 36 +
      756224890747636760189106858007365013))) +
  coefficientTerm 72
    (-(((9067085802950 : ℚ) * 10 ^ 36 +
      879916402351125455550792960048428609))) +
  coefficientTerm 71
    ((118291409856805 : ℚ) * 10 ^ 36 +
      654155265315825055214060283244115820) +
  coefficientTerm 70
    (-(((317279331924508 : ℚ) * 10 ^ 36 +
      839779158647612370746188168316281419))) +
  coefficientTerm 69
    ((451941038044837 : ℚ) * 10 ^ 36 +
      849384065317876121764680852616234936) +
  coefficientTerm 68
    (-(((181307121752543 : ℚ) * 10 ^ 36 +
      769113092165260465525831938245452680))) +
  coefficientTerm 67
    (-(((782020535002471 : ℚ) * 10 ^ 36 +
      299227450895820569521667112384018964)))

/-- Internal datum. -/ def remainder2Coefficient5Chunk4 : Coefficient :=
  coefficientTerm 66
    ((2229408024555610 : ℚ) * 10 ^ 36 +
      605875320579090371052347830568858257) +
  coefficientTerm 65
    (-(((3262110651062154 : ℚ) * 10 ^ 36 +
      797891480141719997226909503679611118))) +
  coefficientTerm 64
    ((2795730063013252 : ℚ) * 10 ^ 36 +
      313772849604653854918973775121773327) +
  coefficientTerm 63
    (-(((547879151578059 : ℚ) * 10 ^ 36 +
      857926911438579520090404041947816918))) +
  coefficientTerm 62
    (-(((2426562057443760 : ℚ) * 10 ^ 36 +
      437955479795717455422957310538712072))) +
  coefficientTerm 61
    ((4374189055099625 : ℚ) * 10 ^ 36 +
      082866580706568063519555735942802816) +
  coefficientTerm 60
    (-(((4213993205963876 : ℚ) * 10 ^ 36 +
      886713791483973426125072084952402930))) +
  coefficientTerm 59
    ((2355888510834570 : ℚ) * 10 ^ 36 +
      221982904312471436476951726541414062)

/-- Internal datum. -/ def remainder2Coefficient5Chunk5 : Coefficient :=
  coefficientTerm 58
    (-(((214009112868664 : ℚ) * 10 ^ 36 +
      380275346632408479348707168575965346))) +
  coefficientTerm 57
    (-(((1010285970366236 : ℚ) * 10 ^ 36 +
      261311586117768254048794953317061497))) +
  coefficientTerm 56
    ((1092445794418350 : ℚ) * 10 ^ 36 +
      991227293304062352945919761085569406) +
  coefficientTerm 55
    (-(((578627282538253 : ℚ) * 10 ^ 36 +
      583321543106577877607366906622185027))) +
  coefficientTerm 54
    ((93164830782748 : ℚ) * 10 ^ 36 +
      409651416769751500784564105781779151) +
  coefficientTerm 53
    ((106536583640868 : ℚ) * 10 ^ 36 +
      574405256960339526933228721070489684) +
  coefficientTerm 52
    (-(((95220340007489 : ℚ) * 10 ^ 36 +
      739605214981707878241588414868276620))) +
  coefficientTerm 51
    ((30849558643173 : ℚ) * 10 ^ 36 +
      766701288435074088248503281094991097)

/-- Internal datum. -/ def remainder2Coefficient5Chunk6 : Coefficient :=
  coefficientTerm 50
    ((4536997018687 : ℚ) * 10 ^ 36 +
      278322071825226880515848890525143295) +
  coefficientTerm 49
    (-(((8665970048652 : ℚ) * 10 ^ 36 +
      318840432392931146127238888078672941))) +
  coefficientTerm 48
    ((3120093033409 : ℚ) * 10 ^ 36 +
      065786758827883803080316430806655045) +
  coefficientTerm 47
    ((217432829839 : ℚ) * 10 ^ 36 +
      310336002817984518166135227832232782) +
  coefficientTerm 46
    (-(((596676247251 : ℚ) * 10 ^ 36 +
      947916726407473354347441926711917636))) +
  coefficientTerm 45
    ((178205050773 : ℚ) * 10 ^ 36 +
      421933199244930914495314572679868757) +
  coefficientTerm 44
    ((27161067309 : ℚ) * 10 ^ 36 +
      970447311973679620919266785043335179) +
  coefficientTerm 43
    (-(((31726243031 : ℚ) * 10 ^ 36 +
      577828134638573492632902354471093984)))

/-- Internal datum. -/ def remainder2Coefficient5Chunk7 : Coefficient :=
  coefficientTerm 42
    ((5210269669 : ℚ) * 10 ^ 36 +
      951627349681283239449495527787077121) +
  coefficientTerm 41
    ((2396380361 : ℚ) * 10 ^ 36 +
      633016720239785833367126775002379437) +
  coefficientTerm 40
    (-(((1099916178 : ℚ) * 10 ^ 36 +
      960450575915685818529555687157919662))) +
  coefficientTerm 39
    (-(((20984404 : ℚ) * 10 ^ 36 +
      370839676984211613442320871622164412))) +
  coefficientTerm 38
    ((108107639 : ℚ) * 10 ^ 36 +
      108100048200385184492677540844180312) +
  coefficientTerm 37
    (-(((15713983 : ℚ) * 10 ^ 36 +
      361751386062903313597586957964997198))) +
  coefficientTerm 36
    (-(((6686117 : ℚ) * 10 ^ 36 +
      133490773997916420110131588575194757))) +
  coefficientTerm 35
    ((2069187 : ℚ) * 10 ^ 36 +
      720024328570227264006657291355787421)

/-- Internal datum. -/ def remainder2Coefficient5Chunk8 : Coefficient :=
  coefficientTerm 34
    ((252102 : ℚ) * 10 ^ 36 +
      819302740101766946367034325092681392) +
  coefficientTerm 33
    (-(((163589 : ℚ) * 10 ^ 36 +
      430880070156827029618454308988307158))) +
  coefficientTerm 32
    (-(((2380 : ℚ) * 10 ^ 36 +
      408842837340426918169537663901078116))) +
  coefficientTerm 31
    ((9692 : ℚ) * 10 ^ 36 +
      705499083531167630753290409160783478) +
  coefficientTerm 30
    (-(((412 : ℚ) * 10 ^ 36 +
      588225219251476476316758306081249061))) +
  coefficientTerm 29
    (-(((466 : ℚ) * 10 ^ 36 +
      785756737243618782844261631760400715))) +
  coefficientTerm 28
    ((34 : ℚ) * 10 ^ 36 +
      285205475050473373020125037058876286) +
  coefficientTerm 27
    ((19 : ℚ) * 10 ^ 36 +
      132701444277355709761164775195411393)

/-- Internal datum. -/ def remainder2Coefficient5Chunk9 : Coefficient :=
  coefficientTerm 26
    (-(((1 : ℚ) * 10 ^ 36 +
      590442759177347388958151340464345290))) +
  coefficientTerm 25
    (-((676296360117176906042635167860569831 : ℚ))) +
  coefficientTerm 24
    (48030170025326506913702104280824156 : ℚ) +
  coefficientTerm 23
    (20888946531069052727010274247959325 : ℚ) +
  coefficientTerm 22
    (-((973972135415319263109760588480179 : ℚ))) +
  coefficientTerm 21
    (-((509558385722369015881141643744004 : ℚ))) +
  coefficientTerm 20
    (2185427701132490215696739421726 : ℚ) +
  coefficientTerm 19
    (10589490421697306581022864221125 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient5Chunk10 : Coefficient :=
  coefficientTerm 18
    (215558598921243747288171008522 : ℚ) +
  coefficientTerm 17
    (-((125392070547471792509348429414 : ℚ))) +
  coefficientTerm 16
    (-((10949556985199660678063311825 : ℚ))) +
  coefficientTerm 15
    (1281528474945542949359844633 : ℚ) +
  coefficientTerm 14
    (113435219738758599710588858 : ℚ) +
  coefficientTerm 13
    (-((1516553408964565706773563 : ℚ))) +
  coefficientTerm 12
    (-((1038032059894976781868696 : ℚ))) +
  coefficientTerm 11
    (-((11117019750973116692969 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient5Chunk11 : Coefficient :=
  coefficientTerm 10
    (2708132833691499223520 : ℚ) +
  coefficientTerm 9
    (140981990055572131702 : ℚ) +
  coefficientTerm 8
    (-((4010384813694609235 : ℚ))) +
  coefficientTerm 7
    (-((239337682022022144 : ℚ))) +
  coefficientTerm 6
    (1321979052167081 : ℚ) +
  coefficientTerm 5
    (152811697040613 : ℚ) +
  coefficientTerm 4
    (-((826150121927 : ℚ))) +
  coefficientTerm 3
    (-((13173586573 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient5Chunk12 : Coefficient :=
  coefficientTerm 2
    (58202904 : ℚ) +
  coefficientTerm 1
    (-((4584 : ℚ))) +
  coefficientTerm 0
    (-((8 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient5Block0 : Coefficient :=
  remainder2Coefficient5Chunk0 +
  remainder2Coefficient5Chunk1 +
  remainder2Coefficient5Chunk2 +
  remainder2Coefficient5Chunk3 +
  remainder2Coefficient5Chunk4 +
  remainder2Coefficient5Chunk5 +
  remainder2Coefficient5Chunk6 +
  remainder2Coefficient5Chunk7 +
  remainder2Coefficient5Chunk8 +
  remainder2Coefficient5Chunk9 +
  remainder2Coefficient5Chunk10 +
  remainder2Coefficient5Chunk11

/-- Internal datum. -/ def remainder2Coefficient5Block1 : Coefficient :=
  remainder2Coefficient5Chunk12

/-- Internal datum. -/ def remainder2Coefficient5 : Coefficient :=
  remainder2Coefficient5Block0 +
  remainder2Coefficient5Block1

/-- Internal datum. -/ def remainder2Coefficient6Chunk0 : Coefficient :=
  coefficientTerm 95
    (-((1 : ℚ))) +
  coefficientTerm 94
    (-((629591425 : ℚ))) +
  coefficientTerm 93
    (-((199417564971929 : ℚ))) +
  coefficientTerm 92
    (-((3092981143429333279 : ℚ))) +
  coefficientTerm 91
    (-((7229173878372384068265 : ℚ))) +
  coefficientTerm 90
    (-((3292471087723803892438322 : ℚ))) +
  coefficientTerm 89
    (1107378815922411149079177229 : ℚ) +
  coefficientTerm 88
    (1089413395938381807202776494154 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient6Chunk1 : Coefficient :=
  coefficientTerm 87
    (286363027698652162782785744858111 : ℚ) +
  coefficientTerm 86
    (34944721186945926298271664519464594 : ℚ) +
  coefficientTerm 85
    ((2 : ℚ) * 10 ^ 36 +
      171214875594016473752712052888364881) +
  coefficientTerm 84
    ((68 : ℚ) * 10 ^ 36 +
      165293576858192487165357082552974621) +
  coefficientTerm 83
    ((931 : ℚ) * 10 ^ 36 +
      515776698594048009905810307361214858) +
  coefficientTerm 82
    ((806 : ℚ) * 10 ^ 36 +
      770333612448780191069553229078389783) +
  coefficientTerm 81
    (-(((79855 : ℚ) * 10 ^ 36 +
      619076933278288806586082688280262928))) +
  coefficientTerm 80
    (-(((130364 : ℚ) * 10 ^ 36 +
      068837196412915331835983767607389036)))

/-- Internal datum. -/ def remainder2Coefficient6Chunk2 : Coefficient :=
  coefficientTerm 79
    ((4212045 : ℚ) * 10 ^ 36 +
      223053116439059613323987782256717639) +
  coefficientTerm 78
    (-(((4657048 : ℚ) * 10 ^ 36 +
      383506180696440995131466651437813763))) +
  coefficientTerm 77
    (-(((116621656 : ℚ) * 10 ^ 36 +
      765750600540617213369055032965477929))) +
  coefficientTerm 76
    ((520301936 : ℚ) * 10 ^ 36 +
      077397947184043319587679666723442887) +
  coefficientTerm 75
    ((407325991 : ℚ) * 10 ^ 36 +
      422521290337696636708310350463817027) +
  coefficientTerm 74
    (-(((9904927975 : ℚ) * 10 ^ 36 +
      710995422196730406795647174801069171))) +
  coefficientTerm 73
    ((31287071019 : ℚ) * 10 ^ 36 +
      551607357660603537375697104621823622) +
  coefficientTerm 72
    (-(((5743205394 : ℚ) * 10 ^ 36 +
      693217441326578355115890903196243276)))

/-- Internal datum. -/ def remainder2Coefficient6Chunk3 : Coefficient :=
  coefficientTerm 71
    (-(((259796156938 : ℚ) * 10 ^ 36 +
      576126935931880575940133496455929373))) +
  coefficientTerm 70
    ((907052891357 : ℚ) * 10 ^ 36 +
      068529730115275023977792560595353116) +
  coefficientTerm 69
    (-(((1259284677279 : ℚ) * 10 ^ 36 +
      418318144667404132063930058303046310))) +
  coefficientTerm 68
    (-(((932324612480 : ℚ) * 10 ^ 36 +
      629040663752920016275618786874393818))) +
  coefficientTerm 67
    ((8088426106972 : ℚ) * 10 ^ 36 +
      228431048023598589508535972069747653) +
  coefficientTerm 66
    (-(((17939533405231 : ℚ) * 10 ^ 36 +
      251363616472490566952428926934345738))) +
  coefficientTerm 65
    ((19420671632102 : ℚ) * 10 ^ 36 +
      037980135832791336634529791939084307) +
  coefficientTerm 64
    ((1760996210278 : ℚ) * 10 ^ 36 +
      097879640123794600894772440302289074)

/-- Internal datum. -/ def remainder2Coefficient6Chunk4 : Coefficient :=
  coefficientTerm 63
    (-(((46171373163504 : ℚ) * 10 ^ 36 +
      543158557914214045685537226653625329))) +
  coefficientTerm 62
    ((88311380474228 : ℚ) * 10 ^ 36 +
      653853967785701384992363103654210137) +
  coefficientTerm 61
    (-(((90077395241547 : ℚ) * 10 ^ 36 +
      150221305671591175204232776602561308))) +
  coefficientTerm 60
    ((36264262946462 : ℚ) * 10 ^ 36 +
      470264963478808724054066882211552046) +
  coefficientTerm 59
    ((43474965187021 : ℚ) * 10 ^ 36 +
      755618392755436146346521712452303683) +
  coefficientTerm 58
    (-(((95585932980783 : ℚ) * 10 ^ 36 +
      456538720432113582851069188735402901))) +
  coefficientTerm 57
    ((89385293720112 : ℚ) * 10 ^ 36 +
      488291822566607840486914388527327607) +
  coefficientTerm 56
    (-(((41253678474640 : ℚ) * 10 ^ 36 +
      061179888179619384622750096492600682)))

/-- Internal datum. -/ def remainder2Coefficient6Chunk5 : Coefficient :=
  coefficientTerm 55
    (-(((6727489552838 : ℚ) * 10 ^ 36 +
      408179719537274002341989653780935383))) +
  coefficientTerm 54
    ((26291104706672 : ℚ) * 10 ^ 36 +
      415387657384787000492935607658169965) +
  coefficientTerm 53
    (-(((19732291277255 : ℚ) * 10 ^ 36 +
      062629310930650026635106843797097302))) +
  coefficientTerm 52
    ((5652777509329 : ℚ) * 10 ^ 36 +
      527173079846530507218923725434481468) +
  coefficientTerm 51
    ((2410820301271 : ℚ) * 10 ^ 36 +
      893278955207186857464670676422527112) +
  coefficientTerm 50
    (-(((3121040979427 : ℚ) * 10 ^ 36 +
      526931885619959908673567118952942816))) +
  coefficientTerm 49
    ((1131726611565 : ℚ) * 10 ^ 36 +
      921421877434735816529017800358660734) +
  coefficientTerm 48
    ((159166271221 : ℚ) * 10 ^ 36 +
      174898678323869034613115263357675153)

/-- Internal datum. -/ def remainder2Coefficient6Chunk6 : Coefficient :=
  coefficientTerm 47
    (-(((317667961885 : ℚ) * 10 ^ 36 +
      729755212373371552547149669387921084))) +
  coefficientTerm 46
    ((101615939163 : ℚ) * 10 ^ 36 +
      603552285300697518056435893445132998) +
  coefficientTerm 45
    ((19324817302 : ℚ) * 10 ^ 36 +
      042652217758620587384065055762449306) +
  coefficientTerm 44
    (-(((23751755542 : ℚ) * 10 ^ 36 +
      444203265532361883311010910235695327))) +
  coefficientTerm 43
    ((4377108880 : ℚ) * 10 ^ 36 +
      256740642198220811140850983490192676) +
  coefficientTerm 42
    ((2198291250 : ℚ) * 10 ^ 36 +
      583775650210278270666734838628936545) +
  coefficientTerm 41
    (-(((1140838767 : ℚ) * 10 ^ 36 +
      007516959294651878397634074067432175))) +
  coefficientTerm 40
    (-(((14699805 : ℚ) * 10 ^ 36 +
      210117737208311297643153352365036420)))

/-- Internal datum. -/ def remainder2Coefficient6Chunk7 : Coefficient :=
  coefficientTerm 39
    ((134638847 : ℚ) * 10 ^ 36 +
      786245837888592364557673177253229780) +
  coefficientTerm 38
    (-(((22643107 : ℚ) * 10 ^ 36 +
      225379856272866206550665913259766049))) +
  coefficientTerm 37
    (-(((9820907 : ℚ) * 10 ^ 36 +
      169482207987595217407352126266374824))) +
  coefficientTerm 36
    ((3467010 : ℚ) * 10 ^ 36 +
      735621713056201496621093019705005373) +
  coefficientTerm 35
    ((424684 : ℚ) * 10 ^ 36 +
      769546239265370557834075128561258657) +
  coefficientTerm 34
    (-(((321295 : ℚ) * 10 ^ 36 +
      042349681723632820191220560028096900))) +
  coefficientTerm 33
    (-(((3068 : ℚ) * 10 ^ 36 +
      732178837805852846609862113546712980))) +
  coefficientTerm 32
    ((22303 : ℚ) * 10 ^ 36 +
      221764783494685504179773267006285479)

/-- Internal datum. -/ def remainder2Coefficient6Chunk8 : Coefficient :=
  coefficientTerm 31
    (-(((1140 : ℚ) * 10 ^ 36 +
      152263465682044046210616394825658004))) +
  coefficientTerm 30
    (-(((1258 : ℚ) * 10 ^ 36 +
      161069668623656362952421948325399372))) +
  coefficientTerm 29
    ((106 : ℚ) * 10 ^ 36 +
      109478758528122081569249927892450975) +
  coefficientTerm 28
    ((60 : ℚ) * 10 ^ 36 +
      367025213541084292114337935339630656) +
  coefficientTerm 27
    (-(((5 : ℚ) * 10 ^ 36 +
      716537617376765869030209898778114261))) +
  coefficientTerm 26
    (-(((2 : ℚ) * 10 ^ 36 +
      519572862830697884162971473184893653))) +
  coefficientTerm 25
    (210316203154359032521086649236863646 : ℚ) +
  coefficientTerm 24
    (90957482947576568207820968873219052 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient6Chunk9 : Coefficient :=
  coefficientTerm 23
    (-((4973479925282740496115957637429406 : ℚ))) +
  coefficientTerm 22
    (-((2756851892830333293894575180613507 : ℚ))) +
  coefficientTerm 21
    (46764779696712004097218540893258 : ℚ) +
  coefficientTerm 20
    (65342815875548638995525416873715 : ℚ) +
  coefficientTerm 19
    (1703605390132880923263815628087 : ℚ) +
  coefficientTerm 18
    (-((1147978231603713844269051911554 : ℚ))) +
  coefficientTerm 17
    (-((74615194376512967677074331502 : ℚ))) +
  coefficientTerm 16
    (11931824111968927302483079140 : ℚ)

/-- Internal datum. -/ def remainder2Coefficient6Chunk10 : Coefficient :=
  coefficientTerm 15
    (1557412099701861736209197599 : ℚ) +
  coefficientTerm 14
    (-((61507058526884679075023217 : ℚ))) +
  coefficientTerm 13
    (-((14893034520022581397395970 : ℚ))) +
  coefficientTerm 12
    (-((339731311869300366432704 : ℚ))) +
  coefficientTerm 11
    (80975272851461060031324 : ℚ) +
  coefficientTerm 10
    (3980510503323414556252 : ℚ) +
  coefficientTerm 9
    (-((122739733042983787952 : ℚ))) +
  coefficientTerm 8
    (-((15092317899760440692 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient6Chunk11 : Coefficient :=
  coefficientTerm 7
    (-((60757622243990768 : ℚ))) +
  coefficientTerm 6
    (17822290888370542 : ℚ) +
  coefficientTerm 5
    (237849108519302 : ℚ) +
  coefficientTerm 4
    (-((7907413645917 : ℚ))) +
  coefficientTerm 3
    (-((43610885488 : ℚ))) +
  coefficientTerm 2
    (656868640 : ℚ) +
  coefficientTerm 1
    (-((264384 : ℚ))) +
  coefficientTerm 0
    (-((606 : ℚ)))

/-- Internal datum. -/ def remainder2Coefficient6Block0 : Coefficient :=
  remainder2Coefficient6Chunk0 +
  remainder2Coefficient6Chunk1 +
  remainder2Coefficient6Chunk2 +
  remainder2Coefficient6Chunk3 +
  remainder2Coefficient6Chunk4 +
  remainder2Coefficient6Chunk5 +
  remainder2Coefficient6Chunk6 +
  remainder2Coefficient6Chunk7 +
  remainder2Coefficient6Chunk8 +
  remainder2Coefficient6Chunk9 +
  remainder2Coefficient6Chunk10 +
  remainder2Coefficient6Chunk11

/-- Internal datum. -/ def remainder2Coefficient6 : Coefficient :=
  remainder2Coefficient6Block0

/-- Internal datum. -/ def remainder2 : Bivariate :=
  outerTerm 0 remainder2Coefficient0 +
  outerTerm 1 remainder2Coefficient1 +
  outerTerm 2 remainder2Coefficient2 +
  outerTerm 3 remainder2Coefficient3 +
  outerTerm 4 remainder2Coefficient4 +
  outerTerm 5 remainder2Coefficient5 +
  outerTerm 6 remainder2Coefficient6

/-- Internal datum. -/ def quotient0Coefficient0Chunk0 : Coefficient :=
  coefficientTerm 104
    (-((57 : ℚ))) +
  coefficientTerm 103
    (-((3841077559 : ℚ))) +
  coefficientTerm 102
    (-((558067833557316 : ℚ))) +
  coefficientTerm 101
    (-((5066009545098773248 : ℚ))) +
  coefficientTerm 100
    (-((7431822221033001450133 : ℚ))) +
  coefficientTerm 99
    (-((1425733554768857866708704 : ℚ))) +
  coefficientTerm 98
    (1592529083219420427108698213 : ℚ) +
  coefficientTerm 97
    (826166890267273732990563553819 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient0Chunk1 : Coefficient :=
  coefficientTerm 96
    (156012893817345338591694801923432 : ℚ) +
  coefficientTerm 95
    (13883195483569650444712053468569500 : ℚ) +
  coefficientTerm 94
    (599693446652242855277545195144030688 : ℚ) +
  coefficientTerm 93
    ((11 : ℚ) * 10 ^ 36 +
      208110790713224153547100355318734909) +
  coefficientTerm 92
    ((29 : ℚ) * 10 ^ 36 +
      487774488452272410823752871291719963) +
  coefficientTerm 91
    (-(((1268 : ℚ) * 10 ^ 36 +
      831496984146699078769999066488746279))) +
  coefficientTerm 90
    (-(((3705 : ℚ) * 10 ^ 36 +
      910088348871363357335410246233125409))) +
  coefficientTerm 89
    ((95269 : ℚ) * 10 ^ 36 +
      015246636957457351986796813433257888)

/-- Internal datum. -/ def quotient0Coefficient0Chunk2 : Coefficient :=
  coefficientTerm 88
    (-(((99881 : ℚ) * 10 ^ 36 +
      647275966607940553618323962817830189))) +
  coefficientTerm 87
    (-(((3620186 : ℚ) * 10 ^ 36 +
      223345637897607978845582551241048764))) +
  coefficientTerm 86
    ((19293968 : ℚ) * 10 ^ 36 +
      898836195070328893925426509016960339) +
  coefficientTerm 85
    ((8297911 : ℚ) * 10 ^ 36 +
      474665038304066619664342547699570521) +
  coefficientTerm 84
    (-(((457187030 : ℚ) * 10 ^ 36 +
      448033945181230592017538929018883219))) +
  coefficientTerm 83
    ((1939738536 : ℚ) * 10 ^ 36 +
      306659416722445035092212488279772019) +
  coefficientTerm 82
    (-(((1930955462 : ℚ) * 10 ^ 36 +
      975201415426067039280099837649787428))) +
  coefficientTerm 81
    (-(((15203943609 : ℚ) * 10 ^ 36 +
      941285531610228887628241295954851843)))

/-- Internal datum. -/ def quotient0Coefficient0Chunk3 : Coefficient :=
  coefficientTerm 80
    ((81365404028 : ℚ) * 10 ^ 36 +
      609359486030024536122951045118208972) +
  coefficientTerm 79
    (-(((186830193197 : ℚ) * 10 ^ 36 +
      146349959604718814335939574685876851))) +
  coefficientTerm 78
    ((108350315113 : ℚ) * 10 ^ 36 +
      769829866504336051835220853269454841) +
  coefficientTerm 77
    ((740453728976 : ℚ) * 10 ^ 36 +
      758811535560599367453384399635411191) +
  coefficientTerm 76
    (-(((2951878808363 : ℚ) * 10 ^ 36 +
      198739315049360222566098838550979900))) +
  coefficientTerm 75
    ((5832895691897 : ℚ) * 10 ^ 36 +
      081630224339257327658198732800393118) +
  coefficientTerm 74
    (-(((5934276340376 : ℚ) * 10 ^ 36 +
      107396070292060159108412137379806622))) +
  coefficientTerm 73
    (-(((2181820204593 : ℚ) * 10 ^ 36 +
      295797906213045874303473715555540824)))

/-- Internal datum. -/ def quotient0Coefficient0Chunk4 : Coefficient :=
  coefficientTerm 72
    ((21062062706562 : ℚ) * 10 ^ 36 +
      445200809480287904284491592933277538) +
  coefficientTerm 71
    (-(((44021961472992 : ℚ) * 10 ^ 36 +
      892378227762405959623352784956238864))) +
  coefficientTerm 70
    ((54787985936853 : ℚ) * 10 ^ 36 +
      478810180428882850489202271345742399) +
  coefficientTerm 69
    (-(((38020099043798 : ℚ) * 10 ^ 36 +
      267030784902603052073682266107061228))) +
  coefficientTerm 68
    (-(((5597732883359 : ℚ) * 10 ^ 36 +
      569495074607981737641551498522953047))) +
  coefficientTerm 67
    ((54644368966381 : ℚ) * 10 ^ 36 +
      791193010950830064152486286224567935) +
  coefficientTerm 66
    (-(((80718454021070 : ℚ) * 10 ^ 36 +
      884056874524868947698447631051411851))) +
  coefficientTerm 65
    ((70299822644477 : ℚ) * 10 ^ 36 +
      667941452127959338915293618752830183)

/-- Internal datum. -/ def quotient0Coefficient0Chunk5 : Coefficient :=
  coefficientTerm 64
    (-(((34538013985636 : ℚ) * 10 ^ 36 +
      064667206143319544546755854928713846))) +
  coefficientTerm 63
    (-(((1758593889773 : ℚ) * 10 ^ 36 +
      238890591584348803874809527718546283))) +
  coefficientTerm 62
    ((20185626919330 : ℚ) * 10 ^ 36 +
      063376494903481103222669296951232969) +
  coefficientTerm 61
    (-(((19301316870042 : ℚ) * 10 ^ 36 +
      222352220547331443962931908421834011))) +
  coefficientTerm 60
    ((9466032222995 : ℚ) * 10 ^ 36 +
      478665830380703287631803876655800618) +
  coefficientTerm 59
    (-(((1093631450404 : ℚ) * 10 ^ 36 +
      734160541562225877176813739692545496))) +
  coefficientTerm 58
    (-(((2057368131317 : ℚ) * 10 ^ 36 +
      145845040596610518578486940162978737))) +
  coefficientTerm 57
    ((1662073346899 : ℚ) * 10 ^ 36 +
      705557441354765904480445308356704039)

/-- Internal datum. -/ def quotient0Coefficient0Chunk6 : Coefficient :=
  coefficientTerm 56
    (-(((496857512888 : ℚ) * 10 ^ 36 +
      182157778393749836888571626516520834))) +
  coefficientTerm 55
    (-(((101064362484 : ℚ) * 10 ^ 36 +
      563484480441648768891290133554063264))) +
  coefficientTerm 54
    ((154244272622 : ℚ) * 10 ^ 36 +
      717300818580446641376793093788445846) +
  coefficientTerm 53
    (-(((51988993790 : ℚ) * 10 ^ 36 +
      539244626473754583381625978162517581))) +
  coefficientTerm 52
    (-(((5314206956 : ℚ) * 10 ^ 36 +
      824349042145064388104675507355359014))) +
  coefficientTerm 51
    ((10599341839 : ℚ) * 10 ^ 36 +
      838439697488380894151634541348727206) +
  coefficientTerm 50
    (-(((2944156687 : ℚ) * 10 ^ 36 +
      634303761661249423726667917953968009))) +
  coefficientTerm 49
    (-(((552254000 : ℚ) * 10 ^ 36 +
      654569021336979613432730637573065685)))

/-- Internal datum. -/ def quotient0Coefficient0Chunk7 : Coefficient :=
  coefficientTerm 48
    ((552360270 : ℚ) * 10 ^ 36 +
      398818319353145489782353749547768392) +
  coefficientTerm 47
    (-(((80287391 : ℚ) * 10 ^ 36 +
      666913031597414352953107736313155352))) +
  coefficientTerm 46
    (-(((43938240 : ℚ) * 10 ^ 36 +
      558633471165913731717007250944680444))) +
  coefficientTerm 45
    ((18316270 : ℚ) * 10 ^ 36 +
      119387302608617076638031504382930764) +
  coefficientTerm 44
    ((751294 : ℚ) * 10 ^ 36 +
      374573681326568722390841199327865851) +
  coefficientTerm 43
    (-(((1845720 : ℚ) * 10 ^ 36 +
      346253634112937529242426123520438512))) +
  coefficientTerm 42
    ((229696 : ℚ) * 10 ^ 36 +
      215916838287844471534450095836001924) +
  coefficientTerm 41
    ((117352 : ℚ) * 10 ^ 36 +
      377668326104205605237262843048477766)

/-- Internal datum. -/ def quotient0Coefficient0Chunk8 : Coefficient :=
  coefficientTerm 40
    (-(((32103 : ℚ) * 10 ^ 36 +
      660145362354445103781428166011131493))) +
  coefficientTerm 39
    (-(((4753 : ℚ) * 10 ^ 36 +
      283411438709372552875113705271279091))) +
  coefficientTerm 38
    ((2555 : ℚ) * 10 ^ 36 +
      938129246194720590112239616693000020) +
  coefficientTerm 37
    ((82 : ℚ) * 10 ^ 36 +
      326641957987786879718580083577907450) +
  coefficientTerm 36
    (-(((149 : ℚ) * 10 ^ 36 +
      980499066025303602005399368074448023))) +
  coefficientTerm 35
    ((4 : ℚ) * 10 ^ 36 +
      079529447827005131185289041235434152) +
  coefficientTerm 34
    ((7 : ℚ) * 10 ^ 36 +
      069891411659644855630511660994748613) +
  coefficientTerm 33
    (-((423131389177557560428397844609842056 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient0Chunk9 : Coefficient :=
  coefficientTerm 32
    (-((279389140688565796632021279627337453 : ℚ))) +
  coefficientTerm 31
    (20056248896191962936929031950383668 : ℚ) +
  coefficientTerm 30
    (9501116146563065684294201094454656 : ℚ) +
  coefficientTerm 29
    (-((629671073029109682253342012618565 : ℚ))) +
  coefficientTerm 28
    (-((272398061476342579731396716983408 : ℚ))) +
  coefficientTerm 27
    (11739970290127260095584556846711 : ℚ) +
  coefficientTerm 26
    (6654841919451331408891801590104 : ℚ) +
  coefficientTerm 25
    (-((111611684894280328313118668572 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient0Chunk10 : Coefficient :=
  coefficientTerm 24
    (-((119091945645922091095772206765 : ℚ))) +
  coefficientTerm 23
    (-((2861630946803502003617509347 : ℚ))) +
  coefficientTerm 22
    (1710809968047024442055543571 : ℚ) +
  coefficientTerm 21
    (77172407633275668389936753 : ℚ) +
  coefficientTerm 20
    (-((12854263960194121150106084 : ℚ))) +
  coefficientTerm 19
    (-((1325696787606155637293254 : ℚ))) +
  coefficientTerm 18
    (62016529276748932297653 : ℚ) +
  coefficientTerm 17
    (8595427171361775791882 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient0Chunk11 : Coefficient :=
  coefficientTerm 16
    (34837264144506240089 : ℚ) +
  coefficientTerm 15
    (-((32160039337216517647 : ℚ))) +
  coefficientTerm 14
    (-((666926610021921301 : ℚ))) +
  coefficientTerm 13
    (46854160160082869 : ℚ) +
  coefficientTerm 12
    (1314858434525532 : ℚ) +
  coefficientTerm 11
    (-((31851577396100 : ℚ))) +
  coefficientTerm 10
    (-((440863440487 : ℚ))) +
  coefficientTerm 9
    (6366265563 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient0Chunk12 : Coefficient :=
  coefficientTerm 8
    (-((2864498 : ℚ))) +
  coefficientTerm 7
    (-((21582 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient0Block0 : Coefficient :=
  quotient0Coefficient0Chunk0 +
  quotient0Coefficient0Chunk1 +
  quotient0Coefficient0Chunk2 +
  quotient0Coefficient0Chunk3 +
  quotient0Coefficient0Chunk4 +
  quotient0Coefficient0Chunk5 +
  quotient0Coefficient0Chunk6 +
  quotient0Coefficient0Chunk7 +
  quotient0Coefficient0Chunk8 +
  quotient0Coefficient0Chunk9 +
  quotient0Coefficient0Chunk10 +
  quotient0Coefficient0Chunk11

/-- Internal datum. -/ def quotient0Coefficient0Block1 : Coefficient :=
  quotient0Coefficient0Chunk12

/-- Internal datum. -/ def quotient0Coefficient0 : Coefficient :=
  quotient0Coefficient0Block0 +
  quotient0Coefficient0Block1

/-- Internal datum. -/ def quotient0Coefficient1Chunk0 : Coefficient :=
  coefficientTerm 100
    (-((1531 : ℚ))) +
  coefficientTerm 99
    (-((19508574327 : ℚ))) +
  coefficientTerm 98
    (-((1361523289628637 : ℚ))) +
  coefficientTerm 97
    (-((7299353148702413880 : ℚ))) +
  coefficientTerm 96
    (-((6502350181368034712763 : ℚ))) +
  coefficientTerm 95
    (288655663175867489950135 : ℚ) +
  coefficientTerm 94
    (1648620916447399278461326599 : ℚ) +
  coefficientTerm 93
    (557252100670274443417011605672 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient1Chunk1 : Coefficient :=
  coefficientTerm 92
    (77539676403259514938207129980570 : ℚ) +
  coefficientTerm 91
    (5090601387856462948934217281806340 : ℚ) +
  coefficientTerm 90
    (154222645142817402644473207358422676 : ℚ) +
  coefficientTerm 89
    ((1 : ℚ) * 10 ^ 36 +
      615571980043112719569623158364205401) +
  coefficientTerm 88
    (-(((10 : ℚ) * 10 ^ 36 +
      055164469298150458742893065860659389))) +
  coefficientTerm 87
    (-(((193 : ℚ) * 10 ^ 36 +
      151339290816315333847107320405976202))) +
  coefficientTerm 86
    ((954 : ℚ) * 10 ^ 36 +
      092094431019472771782159927380222806) +
  coefficientTerm 85
    ((8792 : ℚ) * 10 ^ 36 +
      855151120065358686591897330090534643)

/-- Internal datum. -/ def quotient0Coefficient1Chunk2 : Coefficient :=
  coefficientTerm 84
    (-(((76315 : ℚ) * 10 ^ 36 +
      488999635155158751168372949589777694))) +
  coefficientTerm 83
    ((16152 : ℚ) * 10 ^ 36 +
      964517463575093839276134853639694869) +
  coefficientTerm 82
    ((2076939 : ℚ) * 10 ^ 36 +
      322048601889913755583458772698575783) +
  coefficientTerm 81
    (-(((9971963 : ℚ) * 10 ^ 36 +
      602687910226050756374369694151792579))) +
  coefficientTerm 80
    ((7609860 : ℚ) * 10 ^ 36 +
      460180642473499012505913502264232057) +
  coefficientTerm 79
    ((115009232 : ℚ) * 10 ^ 36 +
      112661448436470339689627893951420532) +
  coefficientTerm 78
    (-(((584937072 : ℚ) * 10 ^ 36 +
      782688058640230387654434667395702370))) +
  coefficientTerm 77
    ((1218543360 : ℚ) * 10 ^ 36 +
      987616250085822477038126829345378970)

/-- Internal datum. -/ def quotient0Coefficient1Chunk3 : Coefficient :=
  coefficientTerm 76
    ((217969810 : ℚ) * 10 ^ 36 +
      151095599808106734488297548209016277) +
  coefficientTerm 75
    (-(((9366556112 : ℚ) * 10 ^ 36 +
      428762901032001639672769867229036125))) +
  coefficientTerm 74
    ((30886621644 : ℚ) * 10 ^ 36 +
      787390828670882288028462212077960282) +
  coefficientTerm 73
    (-(((53150121957 : ℚ) * 10 ^ 36 +
      270377552179100341374748169469956912))) +
  coefficientTerm 72
    ((31444497051 : ℚ) * 10 ^ 36 +
      388428810972208917878251640725218998) +
  coefficientTerm 71
    ((98666660042 : ℚ) * 10 ^ 36 +
      972348520591832105027207769601021857) +
  coefficientTerm 70
    (-(((352884454899 : ℚ) * 10 ^ 36 +
      322579325495572354117085114002464702))) +
  coefficientTerm 69
    ((613658221721 : ℚ) * 10 ^ 36 +
      192935025510985209643722882871353918)

/-- Internal datum. -/ def quotient0Coefficient1Chunk4 : Coefficient :=
  coefficientTerm 68
    (-(((638832428835 : ℚ) * 10 ^ 36 +
      754843603677749060080200565223838833))) +
  coefficientTerm 67
    ((232662009007 : ℚ) * 10 ^ 36 +
      902219478431629970599731359931053468) +
  coefficientTerm 66
    ((527454977549 : ℚ) * 10 ^ 36 +
      844590822104908107448536953922421221) +
  coefficientTerm 65
    (-(((1248486674040 : ℚ) * 10 ^ 36 +
      766899731060425676364317443245073545))) +
  coefficientTerm 64
    ((1480352301487 : ℚ) * 10 ^ 36 +
      300359781874275121389443788520067013) +
  coefficientTerm 63
    (-(((1079499079306 : ℚ) * 10 ^ 36 +
      098984399575451557791060681701494527))) +
  coefficientTerm 62
    ((330016998954 : ℚ) * 10 ^ 36 +
      277610605244145184785146902390984504) +
  coefficientTerm 61
    ((300535025710 : ℚ) * 10 ^ 36 +
      172943165400570469078287748786305190)

/-- Internal datum. -/ def quotient0Coefficient1Chunk5 : Coefficient :=
  coefficientTerm 60
    (-(((527184883530 : ℚ) * 10 ^ 36 +
      608894932288955386670071957906729292))) +
  coefficientTerm 59
    ((398603335529 : ℚ) * 10 ^ 36 +
      860997458303913236750269595057320131) +
  coefficientTerm 58
    (-(((153687963264 : ℚ) * 10 ^ 36 +
      394442277389481941991047997078379056))) +
  coefficientTerm 57
    (-(((12908526305 : ℚ) * 10 ^ 36 +
      989130995134542937547253706208276149))) +
  coefficientTerm 56
    ((57160165034 : ℚ) * 10 ^ 36 +
      902565890073385547697987345564545403) +
  coefficientTerm 55
    (-(((34817621958 : ℚ) * 10 ^ 36 +
      616343895445980966855604232771052465))) +
  coefficientTerm 54
    ((6878221841 : ℚ) * 10 ^ 36 +
      328787632623371996059510490741350444) +
  coefficientTerm 53
    ((4158248618 : ℚ) * 10 ^ 36 +
      228302285003712110516417796043393319)

/-- Internal datum. -/ def quotient0Coefficient1Chunk6 : Coefficient :=
  coefficientTerm 52
    (-(((3550939024 : ℚ) * 10 ^ 36 +
      861251564120809240554925628481570702))) +
  coefficientTerm 51
    ((837504706 : ℚ) * 10 ^ 36 +
      043774702834468102660808822097000867) +
  coefficientTerm 50
    ((280120353 : ℚ) * 10 ^ 36 +
      134608492929679562186979307304847074) +
  coefficientTerm 49
    (-(((245918172 : ℚ) * 10 ^ 36 +
      576833114711094410084637845128230945))) +
  coefficientTerm 48
    ((43333622 : ℚ) * 10 ^ 36 +
      225918610214120797168867774194119033) +
  coefficientTerm 47
    ((21110668 : ℚ) * 10 ^ 36 +
      165097783616467376712632569224419138) +
  coefficientTerm 46
    (-(((11842284 : ℚ) * 10 ^ 36 +
      245865537136284438219417414485096950))) +
  coefficientTerm 45
    ((518431 : ℚ) * 10 ^ 36 +
      993223087537975526771010941342927537)

/-- Internal datum. -/ def quotient0Coefficient1Chunk7 : Coefficient :=
  coefficientTerm 44
    ((1231453 : ℚ) * 10 ^ 36 +
      999702133079997255344828642389852440) +
  coefficientTerm 43
    (-(((318969 : ℚ) * 10 ^ 36 +
      361024936271305358537600439111573093))) +
  coefficientTerm 42
    (-(((60847 : ℚ) * 10 ^ 36 +
      106322343676626652213824785148193877))) +
  coefficientTerm 41
    ((39916 : ℚ) * 10 ^ 36 +
      622700707566812125049833759215244158) +
  coefficientTerm 40
    (-(((858 : ℚ) * 10 ^ 36 +
      152470059101019551612633365299595905))) +
  coefficientTerm 39
    (-(((3077 : ℚ) * 10 ^ 36 +
      614441391900031809069429197296730900))) +
  coefficientTerm 38
    ((426 : ℚ) * 10 ^ 36 +
      353206251106313762093471106979394022) +
  coefficientTerm 37
    ((169 : ℚ) * 10 ^ 36 +
      021921197898676958225179248914576926)

/-- Internal datum. -/ def quotient0Coefficient1Chunk8 : Coefficient :=
  coefficientTerm 36
    (-(((42 : ℚ) * 10 ^ 36 +
      064902512836031203023118672944784137))) +
  coefficientTerm 35
    (-(((6 : ℚ) * 10 ^ 36 +
      935930160999324847036645185586456463))) +
  coefficientTerm 34
    ((2 : ℚ) * 10 ^ 36 +
      728539161879094571186897729814333951) +
  coefficientTerm 33
    (218316328701493849693480575251262413 : ℚ) +
  coefficientTerm 32
    (-((135329937992902457292393253211411395 : ℚ))) +
  coefficientTerm 31
    (-((5699917732135604507328129721146354 : ℚ))) +
  coefficientTerm 30
    (5416093870330328397553412866586344 : ℚ) +
  coefficientTerm 29
    (153461612694452264741837511467568 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient1Chunk9 : Coefficient :=
  coefficientTerm 28
    (-((175632861210694561491084918729304 : ℚ))) +
  coefficientTerm 27
    (-((5883531089150031115473414956207 : ℚ))) +
  coefficientTerm 26
    (4654485097878207575566112700836 : ℚ) +
  coefficientTerm 25
    (212155700639831396108305279949 : ℚ) +
  coefficientTerm 24
    (-((90992745106661092225338763540 : ℚ))) +
  coefficientTerm 23
    (-((7016442066894601479079518334 : ℚ))) +
  coefficientTerm 22
    (1374091711593647292499522918 : ℚ) +
  coefficientTerm 21
    (133042470506134468666792555 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient1Chunk10 : Coefficient :=
  coefficientTerm 20
    (-((10697048678883217194921494 : ℚ))) +
  coefficientTerm 19
    (-((1948642613308156963670915 : ℚ))) +
  coefficientTerm 18
    (42692752520473949232726 : ℚ) +
  coefficientTerm 17
    (14099044438710390596545 : ℚ) +
  coefficientTerm 16
    (275358222874500289366 : ℚ) +
  coefficientTerm 15
    (-((60394147656376777131 : ℚ))) +
  coefficientTerm 14
    (-((2199978029779503099 : ℚ))) +
  coefficientTerm 13
    (112132100318902326 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient1Chunk11 : Coefficient :=
  coefficientTerm 12
    (4966335493743703 : ℚ) +
  coefficientTerm 11
    (-((92085082189664 : ℚ))) +
  coefficientTerm 10
    (-((3387523570717 : ℚ))) +
  coefficientTerm 9
    (49618523266 : ℚ) +
  coefficientTerm 8
    (-((7568055 : ℚ))) +
  coefficientTerm 7
    (-((484576 : ℚ))) +
  coefficientTerm 6
    (-((4 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient1Block0 : Coefficient :=
  quotient0Coefficient1Chunk0 +
  quotient0Coefficient1Chunk1 +
  quotient0Coefficient1Chunk2 +
  quotient0Coefficient1Chunk3 +
  quotient0Coefficient1Chunk4 +
  quotient0Coefficient1Chunk5 +
  quotient0Coefficient1Chunk6 +
  quotient0Coefficient1Chunk7 +
  quotient0Coefficient1Chunk8 +
  quotient0Coefficient1Chunk9 +
  quotient0Coefficient1Chunk10 +
  quotient0Coefficient1Chunk11

/-- Internal datum. -/ def quotient0Coefficient1 : Coefficient :=
  quotient0Coefficient1Block0

/-- Internal datum. -/ def quotient0Coefficient2Chunk0 : Coefficient :=
  coefficientTerm 96
    (-((25750 : ℚ))) +
  coefficientTerm 95
    (-((83167292058 : ℚ))) +
  coefficientTerm 94
    (-((2891372126766717 : ℚ))) +
  coefficientTerm 93
    (-((9172158236559578474 : ℚ))) +
  coefficientTerm 92
    (-((4537484998612223680007 : ℚ))) +
  coefficientTerm 91
    (1540194182288886525888031 : ℚ) +
  coefficientTerm 90
    (1417890093311519999193047462 : ℚ) +
  coefficientTerm 89
    (333590014353568038002713312800 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient2Chunk1 : Coefficient :=
  coefficientTerm 88
    (34076089071682545795084507109160 : ℚ) +
  coefficientTerm 87
    (1609655546689880121268292411012491 : ℚ) +
  coefficientTerm 86
    (31823772338529309642301643658243618 : ℚ) +
  coefficientTerm 85
    (93970372516824763235483755314568020 : ℚ) +
  coefficientTerm 84
    (-(((3 : ℚ) * 10 ^ 36 +
      449574917401770956247079745178126774))) +
  coefficientTerm 83
    (-(((8 : ℚ) * 10 ^ 36 +
      928966730820390463677811026790737009))) +
  coefficientTerm 82
    ((243 : ℚ) * 10 ^ 36 +
      368976775315530496595057612022073118) +
  coefficientTerm 81
    (-(((403 : ℚ) * 10 ^ 36 +
      877296097042371714864795310056041463)))

/-- Internal datum. -/ def quotient0Coefficient2Chunk2 : Coefficient :=
  coefficientTerm 80
    (-(((7565 : ℚ) * 10 ^ 36 +
      870317897577405308877748748840565596))) +
  coefficientTerm 79
    ((46129 : ℚ) * 10 ^ 36 +
      764026455522095839608347282901193764) +
  coefficientTerm 78
    (-(((34233 : ℚ) * 10 ^ 36 +
      276808254818735103112578634310512834))) +
  coefficientTerm 77
    (-(((715965 : ℚ) * 10 ^ 36 +
      434310262519037357606934823556752944))) +
  coefficientTerm 76
    ((3715053 : ℚ) * 10 ^ 36 +
      763367529599791290656450552544008393) +
  coefficientTerm 75
    (-(((6989869 : ℚ) * 10 ^ 36 +
      975572323171047070780148317541031073))) +
  coefficientTerm 74
    (-(((9460371 : ℚ) * 10 ^ 36 +
      232043755812809387729409416024031755))) +
  coefficientTerm 73
    ((95488502 : ℚ) * 10 ^ 36 +
      063443278800189890533710173637177223)

/-- Internal datum. -/ def quotient0Coefficient2Chunk3 : Coefficient :=
  coefficientTerm 72
    (-(((281320180 : ℚ) * 10 ^ 36 +
      782127282391738270639125710999606746))) +
  coefficientTerm 71
    ((405372153 : ℚ) * 10 ^ 36 +
      910984918674785256936197689269217885) +
  coefficientTerm 70
    ((70449429 : ℚ) * 10 ^ 36 +
      981754642243504091990063973166452711) +
  coefficientTerm 69
    (-(((1857372005 : ℚ) * 10 ^ 36 +
      713985556891348449360485196531335705))) +
  coefficientTerm 68
    ((4917602229 : ℚ) * 10 ^ 36 +
      435822907591915362152817594863603093) +
  coefficientTerm 67
    (-(((7369657998 : ℚ) * 10 ^ 36 +
      971932954659052875660267876770997778))) +
  coefficientTerm 66
    ((5787948680 : ℚ) * 10 ^ 36 +
      313063096903652044447376878067560391) +
  coefficientTerm 65
    ((2124329905 : ℚ) * 10 ^ 36 +
      774056417215774494366549192936610425)

/-- Internal datum. -/ def quotient0Coefficient2Chunk4 : Coefficient :=
  coefficientTerm 64
    (-(((14214019389 : ℚ) * 10 ^ 36 +
      949760884844494838235439664788953854))) +
  coefficientTerm 63
    ((23696600537 : ℚ) * 10 ^ 36 +
      194338190632202224855763783912980846) +
  coefficientTerm 62
    (-(((23789459336 : ℚ) * 10 ^ 36 +
      976277923667922224048561014518844313))) +
  coefficientTerm 61
    ((13601299857 : ℚ) * 10 ^ 36 +
      733694200537262497624371341987855217) +
  coefficientTerm 60
    ((615780994 : ℚ) * 10 ^ 36 +
      916954551980106456386513701361405627) +
  coefficientTerm 59
    (-(((10495605795 : ℚ) * 10 ^ 36 +
      565835998028013090933460214886066408))) +
  coefficientTerm 58
    ((12035855339 : ℚ) * 10 ^ 36 +
      604144601027091825638749030086630395) +
  coefficientTerm 57
    (-(((7513258259 : ℚ) * 10 ^ 36 +
      749288085114841966547564756093355776)))

/-- Internal datum. -/ def quotient0Coefficient2Chunk5 : Coefficient :=
  coefficientTerm 56
    ((2024407506 : ℚ) * 10 ^ 36 +
      965143815856935604990559397813411111) +
  coefficientTerm 55
    ((1020401583 : ℚ) * 10 ^ 36 +
      645898393104470110463543781416719156) +
  coefficientTerm 54
    (-(((1417538045 : ℚ) * 10 ^ 36 +
      588066769669660771900484418480220087))) +
  coefficientTerm 53
    ((676460203 : ℚ) * 10 ^ 36 +
      782702057168525958539824664996275344) +
  coefficientTerm 52
    (-(((54067255 : ℚ) * 10 ^ 36 +
      306728858782368818798351361518837273))) +
  coefficientTerm 51
    (-(((127142562 : ℚ) * 10 ^ 36 +
      591637417691940418063203906289973526))) +
  coefficientTerm 50
    ((76070574 : ℚ) * 10 ^ 36 +
      609815413212506241966898427134865279) +
  coefficientTerm 49
    (-(((10328207 : ℚ) * 10 ^ 36 +
      991786207632563429664530944041926224)))

/-- Internal datum. -/ def quotient0Coefficient2Chunk6 : Coefficient :=
  coefficientTerm 48
    (-(((9322995 : ℚ) * 10 ^ 36 +
      504676213823968966801065503466658954))) +
  coefficientTerm 47
    ((5268471 : ℚ) * 10 ^ 36 +
      356524295142193893118675213361557371) +
  coefficientTerm 46
    (-(((395101 : ℚ) * 10 ^ 36 +
      801284030737524863574361444791291078))) +
  coefficientTerm 45
    (-(((624651 : ℚ) * 10 ^ 36 +
      893529042611517926028589566906242880))) +
  coefficientTerm 44
    ((229670 : ℚ) * 10 ^ 36 +
      623019736832670312582140237967045717) +
  coefficientTerm 43
    ((17533 : ℚ) * 10 ^ 36 +
      375962294492323536022346884851760276) +
  coefficientTerm 42
    (-(((30175 : ℚ) * 10 ^ 36 +
      883531207304943769052000530415462043))) +
  coefficientTerm 41
    ((4397 : ℚ) * 10 ^ 36 +
      994144722095879900956813914064183152)

/-- Internal datum. -/ def quotient0Coefficient2Chunk7 : Coefficient :=
  coefficientTerm 40
    ((2151 : ℚ) * 10 ^ 36 +
      028308744458506206653516302777951945) +
  coefficientTerm 39
    (-(((754 : ℚ) * 10 ^ 36 +
      665678511508528496742586870577169218))) +
  coefficientTerm 38
    (-(((72 : ℚ) * 10 ^ 36 +
      996148841994610391657073094465578469))) +
  coefficientTerm 37
    ((68 : ℚ) * 10 ^ 36 +
      620462361949395139291744902585778801) +
  coefficientTerm 36
    (-(((2 : ℚ) * 10 ^ 36 +
      219135772113072452125954692610455561))) +
  coefficientTerm 35
    (-(((4 : ℚ) * 10 ^ 36 +
      426171050094070954838695687984716438))) +
  coefficientTerm 34
    (490394863990936799934104069250741456 : ℚ) +
  coefficientTerm 33
    (223011096413205337712537800511282733 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient2Chunk8 : Coefficient :=
  coefficientTerm 32
    (-((37875590857859039451231678432041034 : ℚ))) +
  coefficientTerm 31
    (-((9343003705456348557554461798998359 : ℚ))) +
  coefficientTerm 30
    (1982125513907587869602408912813891 : ℚ) +
  coefficientTerm 29
    (342129069075553919599778648961330 : ℚ) +
  coefficientTerm 28
    (-((77524261115340784408041508354115 : ℚ))) +
  coefficientTerm 27
    (-((11480852063153265274455308035432 : ℚ))) +
  coefficientTerm 26
    (2341629857656435721707885525774 : ℚ) +
  coefficientTerm 25
    (338330489343888433544541654419 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient2Chunk9 : Coefficient :=
  coefficientTerm 24
    (-((50521217924705503559856096052 : ℚ))) +
  coefficientTerm 23
    (-((8830045754664496088332750664 : ℚ))) +
  coefficientTerm 22
    (790259792484551577528762729 : ℚ) +
  coefficientTerm 21
    (165421629512326192104093364 : ℚ) +
  coefficientTerm 20
    (-((5131091365156461657199775 : ℚ))) +
  coefficientTerm 19
    (-((2385052930883836778019889 : ℚ))) +
  coefficientTerm 18
    (-((14379220689494170206379 : ℚ))) +
  coefficientTerm 17
    (19630502355127126742444 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient2Chunk10 : Coefficient :=
  coefficientTerm 16
    (779947681495430720669 : ℚ) +
  coefficientTerm 15
    (-((90100638135880633385 : ℚ))) +
  coefficientTerm 14
    (-((6164201415425497878 : ℚ))) +
  coefficientTerm 13
    (232704760607420390 : ℚ) +
  coefficientTerm 12
    (14147694263118429 : ℚ) +
  coefficientTerm 11
    (-((78957366730782 : ℚ))) +
  coefficientTerm 10
    (-((21293749409575 : ℚ))) +
  coefficientTerm 9
    (307611992394 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient2Chunk11 : Coefficient :=
  coefficientTerm 8
    (311204553 : ℚ) +
  coefficientTerm 7
    (-((7725207 : ℚ))) +
  coefficientTerm 6
    (-((86 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient2Block0 : Coefficient :=
  quotient0Coefficient2Chunk0 +
  quotient0Coefficient2Chunk1 +
  quotient0Coefficient2Chunk2 +
  quotient0Coefficient2Chunk3 +
  quotient0Coefficient2Chunk4 +
  quotient0Coefficient2Chunk5 +
  quotient0Coefficient2Chunk6 +
  quotient0Coefficient2Chunk7 +
  quotient0Coefficient2Chunk8 +
  quotient0Coefficient2Chunk9 +
  quotient0Coefficient2Chunk10 +
  quotient0Coefficient2Chunk11

/-- Internal datum. -/ def quotient0Coefficient2 : Coefficient :=
  quotient0Coefficient2Block0

/-- Internal datum. -/ def quotient0Coefficient3Chunk0 : Coefficient :=
  coefficientTerm 92
    (-((303937 : ℚ))) +
  coefficientTerm 91
    (-((299164604271 : ℚ))) +
  coefficientTerm 90
    (-((5328011309881598 : ℚ))) +
  coefficientTerm 89
    (-((9913167942352697220 : ℚ))) +
  coefficientTerm 88
    (-((2023473448342483712342 : ℚ))) +
  coefficientTerm 87
    (2165972038945346047943265 : ℚ) +
  coefficientTerm 86
    (1053793484017038359296089179 : ℚ) +
  coefficientTerm 85
    (176795165309804489456799201484 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient3Chunk1 : Coefficient :=
  coefficientTerm 84
    (13077827931658811054836738952827 : ℚ) +
  coefficientTerm 83
    (426827358055646164883214402527881 : ℚ) +
  coefficientTerm 82
    (4696289429638570279750641031414248 : ℚ) +
  coefficientTerm 81
    (-((26715676181108534800175883720595637 : ℚ))) +
  coefficientTerm 80
    (-((513645650487594088757921249974877900 : ℚ))) +
  coefficientTerm 79
    ((2 : ℚ) * 10 ^ 36 +
      652806959138657713028756641301490733) +
  coefficientTerm 78
    ((19 : ℚ) * 10 ^ 36 +
      486344807443029423124007085296231137) +
  coefficientTerm 77
    (-(((186 : ℚ) * 10 ^ 36 +
      492008686107144904218481279792905257)))

/-- Internal datum. -/ def quotient0Coefficient3Chunk2 : Coefficient :=
  coefficientTerm 76
    ((211 : ℚ) * 10 ^ 36 +
      316084501257639321926025247393117590) +
  coefficientTerm 75
    ((3647 : ℚ) * 10 ^ 36 +
      345632920552303743118073558066586212) +
  coefficientTerm 74
    (-(((20863 : ℚ) * 10 ^ 36 +
      958948163368078504152034250067472727))) +
  coefficientTerm 73
    ((35923 : ℚ) * 10 ^ 36 +
      857305273616720759574038505731628344) +
  coefficientTerm 72
    ((110437 : ℚ) * 10 ^ 36 +
      769859509160706669259202756467638921) +
  coefficientTerm 71
    (-(((821717 : ℚ) * 10 ^ 36 +
      819266669657667159226412380458974392))) +
  coefficientTerm 70
    ((2238500 : ℚ) * 10 ^ 36 +
      094622305378600228512965915760402577) +
  coefficientTerm 69
    (-(((2412929 : ℚ) * 10 ^ 36 +
      954105070612473940457164809933378343)))

/-- Internal datum. -/ def quotient0Coefficient3Chunk3 : Coefficient :=
  coefficientTerm 68
    (-(((4643589 : ℚ) * 10 ^ 36 +
      979530424671489526055936295545168041))) +
  coefficientTerm 67
    ((26162761 : ℚ) * 10 ^ 36 +
      765121026995855325277912879213511339) +
  coefficientTerm 66
    (-(((58712580 : ℚ) * 10 ^ 36 +
      131711339948083134467244716563863198))) +
  coefficientTerm 65
    ((74415484 : ℚ) * 10 ^ 36 +
      103604268814160326571051131628317422) +
  coefficientTerm 64
    (-(((27213947 : ℚ) * 10 ^ 36 +
      453610353394363681790529711415281254))) +
  coefficientTerm 63
    (-(((106880266 : ℚ) * 10 ^ 36 +
      706709065026745083990731642211029874))) +
  coefficientTerm 62
    ((282297316 : ℚ) * 10 ^ 36 +
      478537405901204746077702038575271085) +
  coefficientTerm 61
    (-(((387984421 : ℚ) * 10 ^ 36 +
      154417778534136612196003371884477224)))

/-- Internal datum. -/ def quotient0Coefficient3Chunk4 : Coefficient :=
  coefficientTerm 60
    ((327132586 : ℚ) * 10 ^ 36 +
      223969798904673831183731123848618258) +
  coefficientTerm 59
    (-(((110263549 : ℚ) * 10 ^ 36 +
      698481150134100466554312735392454720))) +
  coefficientTerm 58
    (-(((136963721 : ℚ) * 10 ^ 36 +
      798051201847001223735617600737974957))) +
  coefficientTerm 57
    ((271955913 : ℚ) * 10 ^ 36 +
      806321337249542965642072613525390551) +
  coefficientTerm 56
    (-(((246651924 : ℚ) * 10 ^ 36 +
      790899095374913182138249604833984830))) +
  coefficientTerm 55
    ((126545359 : ℚ) * 10 ^ 36 +
      006979656707688482743694304170952744) +
  coefficientTerm 54
    (-(((13909327 : ℚ) * 10 ^ 36 +
      717431842826682413728726273226009203))) +
  coefficientTerm 53
    (-(((35884329 : ℚ) * 10 ^ 36 +
      092808484384448150339914163779861737)))

/-- Internal datum. -/ def quotient0Coefficient3Chunk5 : Coefficient :=
  coefficientTerm 52
    ((32358974 : ℚ) * 10 ^ 36 +
      218785347309114475844694618188947554) +
  coefficientTerm 51
    (-(((11982894 : ℚ) * 10 ^ 36 +
      089821765926701208612001567756777782))) +
  coefficientTerm 50
    (-(((974065 : ℚ) * 10 ^ 36 +
      509903710553491983204391114952000721))) +
  coefficientTerm 49
    ((3379264 : ℚ) * 10 ^ 36 +
      686930544784678604032943569828428578) +
  coefficientTerm 48
    (-(((1511667 : ℚ) * 10 ^ 36 +
      937237677869118325238041088518524606))) +
  coefficientTerm 47
    ((31920 : ℚ) * 10 ^ 36 +
      926193338418685907459192160849973580) +
  coefficientTerm 46
    ((259970 : ℚ) * 10 ^ 36 +
      699767071903022629053463669380216369) +
  coefficientTerm 45
    (-(((103599 : ℚ) * 10 ^ 36 +
      515142569286875433230663989124308728)))

/-- Internal datum. -/ def quotient0Coefficient3Chunk6 : Coefficient :=
  coefficientTerm 44
    (-(((4547 : ℚ) * 10 ^ 36 +
      377160161093026418128027062905576185))) +
  coefficientTerm 43
    ((16134 : ℚ) * 10 ^ 36 +
      091404392427325291958401101819933322) +
  coefficientTerm 42
    (-(((3891 : ℚ) * 10 ^ 36 +
      010678417256966572037062004871165634))) +
  coefficientTerm 41
    (-(((994 : ℚ) * 10 ^ 36 +
      967622744195774498132990021873115217))) +
  coefficientTerm 40
    ((662 : ℚ) * 10 ^ 36 +
      863147743656830959582425611993782334) +
  coefficientTerm 39
    (-(((28 : ℚ) * 10 ^ 36 +
      078526536621326708012722038632158878))) +
  coefficientTerm 38
    (-(((59 : ℚ) * 10 ^ 36 +
      470756462425594249486956320279496025))) +
  coefficientTerm 37
    ((11 : ℚ) * 10 ^ 36 +
      826283318045360302995529039207955467)

/-- Internal datum. -/ def quotient0Coefficient3Chunk7 : Coefficient :=
  coefficientTerm 36
    ((3 : ℚ) * 10 ^ 36 +
      346611202976544139280840460921882630) +
  coefficientTerm 35
    (-(((1 : ℚ) * 10 ^ 36 +
      310887539843140282509881475215651821))) +
  coefficientTerm 34
    (-((105681782850671362388866823584189470 : ℚ))) +
  coefficientTerm 33
    (95549505185486757554763653295653824 : ℚ) +
  coefficientTerm 32
    (-((393431259780188679456731834807031 : ℚ))) +
  coefficientTerm 31
    (-((5322760256676029373990130662386364 : ℚ))) +
  coefficientTerm 30
    (261318150070219697901177283608723 : ℚ) +
  coefficientTerm 29
    (241293585624076651740512094972086 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient3Chunk8 : Coefficient :=
  coefficientTerm 28
    (-((16698691657524772577779134235397 : ℚ))) +
  coefficientTerm 27
    (-((9219127942324567058747388513351 : ℚ))) +
  coefficientTerm 26
    (637090995602420017426470181042 : ℚ) +
  coefficientTerm 25
    (294977929282859060618208210433 : ℚ) +
  coefficientTerm 24
    (-((14744989777398189839624767537 : ℚ))) +
  coefficientTerm 23
    (-((7874899476205531189382649809 : ℚ))) +
  coefficientTerm 22
    (176267444790494932501024926 : ℚ) +
  coefficientTerm 21
    (159764303715713423965685533 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient3Chunk9 : Coefficient :=
  coefficientTerm 20
    (1857309441223727914260021 : ℚ) +
  coefficientTerm 19
    (-((2342977067456632053901191 : ℚ))) +
  coefficientTerm 18
    (-((108288433650915271159425 : ℚ))) +
  coefficientTerm 17
    (23453339391942664361944 : ℚ) +
  coefficientTerm 16
    (1428747991079374297140 : ℚ) +
  coefficientTerm 15
    (-((84081296495205342270 : ℚ))) +
  coefficientTerm 14
    (-((15546618304142000891 : ℚ))) +
  coefficientTerm 13
    (502131862979834019 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient3Chunk10 : Coefficient :=
  coefficientTerm 12
    (24671122866508415 : ℚ) +
  coefficientTerm 11
    (949446328414170 : ℚ) +
  coefficientTerm 10
    (-((107438482381220 : ℚ))) +
  coefficientTerm 9
    (1456040255495 : ℚ) +
  coefficientTerm 8
    (6363364716 : ℚ) +
  coefficientTerm 7
    (-((92416745 : ℚ))) +
  coefficientTerm 6
    (-((3163 : ℚ))) +
  coefficientTerm 5
    (5 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient3Block0 : Coefficient :=
  quotient0Coefficient3Chunk0 +
  quotient0Coefficient3Chunk1 +
  quotient0Coefficient3Chunk2 +
  quotient0Coefficient3Chunk3 +
  quotient0Coefficient3Chunk4 +
  quotient0Coefficient3Chunk5 +
  quotient0Coefficient3Chunk6 +
  quotient0Coefficient3Chunk7 +
  quotient0Coefficient3Chunk8 +
  quotient0Coefficient3Chunk9 +
  quotient0Coefficient3Chunk10

/-- Internal datum. -/ def quotient0Coefficient3 : Coefficient :=
  quotient0Coefficient3Block0

/-- Internal datum. -/ def quotient0Coefficient4Chunk0 : Coefficient :=
  coefficientTerm 88
    (-((2673890 : ℚ))) +
  coefficientTerm 87
    (-((910484455959 : ℚ))) +
  coefficientTerm 86
    (-((8474990142441975 : ℚ))) +
  coefficientTerm 85
    (-((8976297583049020809 : ℚ))) +
  coefficientTerm 84
    (382182453703402612819 : ℚ) +
  coefficientTerm 83
    (2210814488069412581600934 : ℚ) +
  coefficientTerm 82
    (685958202356794728769046714 : ℚ) +
  coefficientTerm 81
    (82332278229449477571423288247 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient4Chunk1 : Coefficient :=
  coefficientTerm 80
    (4303279813658084927069419704961 : ℚ) +
  coefficientTerm 79
    (90331020104597750187962065463888 : ℚ) +
  coefficientTerm 78
    (292083667599852916901731352230604 : ℚ) +
  coefficientTerm 77
    (-((9372307263317671890019040199002640 : ℚ))) +
  coefficientTerm 76
    (-((20348041802493287508938930185921082 : ℚ))) +
  coefficientTerm 75
    (611112281764443610431976433030330162 : ℚ) +
  coefficientTerm 74
    (-(((1 : ℚ) * 10 ^ 36 +
      396214119607146984854970683972883881))) +
  coefficientTerm 73
    (-(((14 : ℚ) * 10 ^ 36 +
      583696151451930748933399335484815969)))

/-- Internal datum. -/ def quotient0Coefficient4Chunk2 : Coefficient :=
  coefficientTerm 72
    ((103 : ℚ) * 10 ^ 36 +
      020208422500000329824929067014354859) +
  coefficientTerm 71
    (-(((174 : ℚ) * 10 ^ 36 +
      232963020669431770128084989238879561))) +
  coefficientTerm 70
    (-(((886 : ℚ) * 10 ^ 36 +
      296591839590123384958910265806413085))) +
  coefficientTerm 69
    ((6067 : ℚ) * 10 ^ 36 +
      846612886637116213249177572053737012) +
  coefficientTerm 68
    (-(((15578 : ℚ) * 10 ^ 36 +
      996124582459717343263307525371486914))) +
  coefficientTerm 67
    ((8784 : ℚ) * 10 ^ 36 +
      136484398744648907385884214585397125) +
  coefficientTerm 66
    ((75593 : ℚ) * 10 ^ 36 +
      327440467561055257575708180973076441) +
  coefficientTerm 65
    (-(((304332 : ℚ) * 10 ^ 36 +
      985635104404056333898578194110853610)))

/-- Internal datum. -/ def quotient0Coefficient4Chunk3 : Coefficient :=
  coefficientTerm 64
    ((602834 : ℚ) * 10 ^ 36 +
      214772172596365659433694671067329909) +
  coefficientTerm 63
    (-(((586408 : ℚ) * 10 ^ 36 +
      707429224611777545987204637919818720))) +
  coefficientTerm 62
    (-(((332070 : ℚ) * 10 ^ 36 +
      439883906554173708904865263792047028))) +
  coefficientTerm 61
    ((2358127 : ℚ) * 10 ^ 36 +
      108636909204290676264390297313290815) +
  coefficientTerm 60
    (-(((4652062 : ℚ) * 10 ^ 36 +
      193654214833820112316770961075564904))) +
  coefficientTerm 59
    ((5482848 : ℚ) * 10 ^ 36 +
      305495771294998713766963704794439701) +
  coefficientTerm 58
    (-(((3551556 : ℚ) * 10 ^ 36 +
      770969898414672220207555562653619776))) +
  coefficientTerm 57
    (-(((570250 : ℚ) * 10 ^ 36 +
      920296818323722843488705139242755281)))

/-- Internal datum. -/ def quotient0Coefficient4Chunk4 : Coefficient :=
  coefficientTerm 56
    ((4518808 : ℚ) * 10 ^ 36 +
      505203460785693029669526305906852427) +
  coefficientTerm 55
    (-(((5976730 : ℚ) * 10 ^ 36 +
      365985482923909407709154392903186088))) +
  coefficientTerm 54
    ((4542197 : ℚ) * 10 ^ 36 +
      982978408614789910737024922685844213) +
  coefficientTerm 53
    (-(((1791836 : ℚ) * 10 ^ 36 +
      272853732511140234482632822366156474))) +
  coefficientTerm 52
    (-(((328123 : ℚ) * 10 ^ 36 +
      735192731488415696327003969118441062))) +
  coefficientTerm 51
    ((1006573 : ℚ) * 10 ^ 36 +
      143143101214044829759166055541283615) +
  coefficientTerm 50
    (-(((687651 : ℚ) * 10 ^ 36 +
      878609285223742844594645340036482103))) +
  coefficientTerm 49
    ((184969 : ℚ) * 10 ^ 36 +
      719964274822014649751611234792750845)

/-- Internal datum. -/ def quotient0Coefficient4Chunk5 : Coefficient :=
  coefficientTerm 48
    ((66219 : ℚ) * 10 ^ 36 +
      801284159977537914401348468437333673) +
  coefficientTerm 47
    (-(((81908 : ℚ) * 10 ^ 36 +
      840356374637492170166969059160536588))) +
  coefficientTerm 46
    ((27397 : ℚ) * 10 ^ 36 +
      993650964841821020300395880985237743) +
  coefficientTerm 45
    ((3667 : ℚ) * 10 ^ 36 +
      141716264580653646778880115960761847) +
  coefficientTerm 44
    (-(((6511 : ℚ) * 10 ^ 36 +
      271179939376179513961015768874038233))) +
  coefficientTerm 43
    ((1822 : ℚ) * 10 ^ 36 +
      945513834174664128808254338790226215) +
  coefficientTerm 42
    ((389 : ℚ) * 10 ^ 36 +
      506345508500985727564777575117122396) +
  coefficientTerm 41
    (-(((377 : ℚ) * 10 ^ 36 +
      393676370318348440472729680346650399)))

/-- Internal datum. -/ def quotient0Coefficient4Chunk6 : Coefficient :=
  coefficientTerm 40
    ((51 : ℚ) * 10 ^ 36 +
      389310909927136535857423488950998657) +
  coefficientTerm 39
    ((33 : ℚ) * 10 ^ 36 +
      371664508033950977524496502525308934) +
  coefficientTerm 38
    (-(((13 : ℚ) * 10 ^ 36 +
      002100740599315503889750517475407357))) +
  coefficientTerm 37
    (-((974495041299364780047511291290015914 : ℚ))) +
  coefficientTerm 36
    ((1 : ℚ) * 10 ^ 36 +
      415350185517956754066934546705386531) +
  coefficientTerm 35
    (-((122881845570822122089011336985907745 : ℚ))) +
  coefficientTerm 34
    (-((100468257830384702757335039636566723 : ℚ))) +
  coefficientTerm 33
    (20385543555790384530631025904009301 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient4Chunk7 : Coefficient :=
  coefficientTerm 32
    (5116372813695732464445141599498466 : ℚ) +
  coefficientTerm 31
    (-((1707315156240628111604854552323602 : ℚ))) +
  coefficientTerm 30
    (-((194333840859280341302346862858910 : ℚ))) +
  coefficientTerm 29
    (102003177287084344186883180054583 : ℚ) +
  coefficientTerm 28
    (5798618805985789625732707405735 : ℚ) +
  coefficientTerm 27
    (-((4742893882675797959664177032509 : ℚ))) +
  coefficientTerm 26
    (-((164087310262297437649508313388 : ℚ))) +
  coefficientTerm 25
    (176917188219470759863880584344 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient4Chunk8 : Coefficient :=
  coefficientTerm 24
    (5668017982424196080524238677 : ℚ) +
  coefficientTerm 23
    (-((5162902212602155187663562023 : ℚ))) +
  coefficientTerm 22
    (-((252859814896005881556905595 : ℚ))) +
  coefficientTerm 21
    (121534630105616638237115755 : ℚ) +
  coefficientTerm 20
    (6958611081791263843115336 : ℚ) +
  coefficientTerm 19
    (-((1662057670964276866988237 : ℚ))) +
  coefficientTerm 18
    (-((223909179915510525494986 : ℚ))) +
  coefficientTerm 17
    (25745932755290118181680 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient4Chunk9 : Coefficient :=
  coefficientTerm 16
    (1608102169988115365171 : ℚ) +
  coefficientTerm 15
    (43487621407607986999 : ℚ) +
  coefficientTerm 14
    (-((36753547802550158561 : ℚ))) +
  coefficientTerm 13
    (1357556462471007703 : ℚ) +
  coefficientTerm 12
    (-((4292975750189007 : ℚ))) +
  coefficientTerm 11
    (6715245028035276 : ℚ) +
  coefficientTerm 10
    (-((422168963072479 : ℚ))) +
  coefficientTerm 9
    (4700543123429 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient4Chunk10 : Coefficient :=
  coefficientTerm 8
    (70744071279 : ℚ) +
  coefficientTerm 7
    (-((845687417 : ℚ))) +
  coefficientTerm 6
    (-((174984 : ℚ))) +
  coefficientTerm 5
    (447 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient4Block0 : Coefficient :=
  quotient0Coefficient4Chunk0 +
  quotient0Coefficient4Chunk1 +
  quotient0Coefficient4Chunk2 +
  quotient0Coefficient4Chunk3 +
  quotient0Coefficient4Chunk4 +
  quotient0Coefficient4Chunk5 +
  quotient0Coefficient4Chunk6 +
  quotient0Coefficient4Chunk7 +
  quotient0Coefficient4Chunk8 +
  quotient0Coefficient4Chunk9 +
  quotient0Coefficient4Chunk10

/-- Internal datum. -/ def quotient0Coefficient4 : Coefficient :=
  quotient0Coefficient4Block0

/-- Internal datum. -/ def quotient0Coefficient5Chunk0 : Coefficient :=
  coefficientTerm 84
    (-((18172790 : ℚ))) +
  coefficientTerm 83
    (-((2345264519847 : ℚ))) +
  coefficientTerm 82
    (-((11539354857324391 : ℚ))) +
  coefficientTerm 81
    (-((6403438061520571055 : ℚ))) +
  coefficientTerm 80
    (2129499066500592753637 : ℚ) +
  coefficientTerm 79
    (1860166179562943154124327 : ℚ) +
  coefficientTerm 78
    (391683688535626828772062405 : ℚ) +
  coefficientTerm 77
    (33272956336166072105177852323 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient5Chunk1 : Coefficient :=
  coefficientTerm 76
    (1179929095570195433409983478718 : ℚ) +
  coefficientTerm 75
    (13623662741557871900073710546447 : ℚ) +
  coefficientTerm 74
    (-((71495379700010210574718746292654 : ℚ))) +
  coefficientTerm 73
    (-((1351851725576665339701584491111473 : ℚ))) +
  coefficientTerm 72
    (7351716302379532560604052133584781 : ℚ) +
  coefficientTerm 71
    (40415752293110493502110952264664951 : ℚ) +
  coefficientTerm 70
    (-((437246694210993687599360265940206802 : ℚ))) +
  coefficientTerm 69
    (859685981268844531402829791241112310 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient5Chunk2 : Coefficient :=
  coefficientTerm 68
    ((5 : ℚ) * 10 ^ 36 +
      401341098695920951870555161393956126) +
  coefficientTerm 67
    (-(((38 : ℚ) * 10 ^ 36 +
      614218981771631173475254045432102312))) +
  coefficientTerm 66
    ((95 : ℚ) * 10 ^ 36 +
      295901322160262422256719223094942870) +
  coefficientTerm 65
    ((16 : ℚ) * 10 ^ 36 +
      447319924496665304716518951618333492) +
  coefficientTerm 64
    (-(((869 : ℚ) * 10 ^ 36 +
      131984503380978935008998376888281156))) +
  coefficientTerm 63
    ((3013 : ℚ) * 10 ^ 36 +
      788997703794413581719040469314403324) +
  coefficientTerm 62
    (-(((5258 : ℚ) * 10 ^ 36 +
      589908251790740411809147939036948695))) +
  coefficientTerm 61
    ((2662 : ℚ) * 10 ^ 36 +
      328884328778632350327435073333949630)

/-- Internal datum. -/ def quotient0Coefficient5Chunk3 : Coefficient :=
  coefficientTerm 60
    ((11835 : ℚ) * 10 ^ 36 +
      132264545174501991259742714141677773) +
  coefficientTerm 59
    (-(((39256 : ℚ) * 10 ^ 36 +
      237809535914543265650493773303701907))) +
  coefficientTerm 58
    ((65513 : ℚ) * 10 ^ 36 +
      299934133967291491224896463921920226) +
  coefficientTerm 57
    (-(((64849 : ℚ) * 10 ^ 36 +
      592613485954925302531061798519722941))) +
  coefficientTerm 56
    ((21088 : ℚ) * 10 ^ 36 +
      287137499585162619212867395738220039) +
  coefficientTerm 55
    ((50587 : ℚ) * 10 ^ 36 +
      831320381659353631322608622675881807) +
  coefficientTerm 54
    (-(((108032 : ℚ) * 10 ^ 36 +
      211337673614908296391711065320896588))) +
  coefficientTerm 53
    ((115368 : ℚ) * 10 ^ 36 +
      522873478347148060778916378148792141)

/-- Internal datum. -/ def quotient0Coefficient5Chunk4 : Coefficient :=
  coefficientTerm 52
    (-(((73608 : ℚ) * 10 ^ 36 +
      853374116620776271042360542189273595))) +
  coefficientTerm 51
    ((17015 : ℚ) * 10 ^ 36 +
      662543098188107523060991855560693937) +
  coefficientTerm 50
    ((19168 : ℚ) * 10 ^ 36 +
      927812447376939420201682520816511926) +
  coefficientTerm 49
    (-(((24953 : ℚ) * 10 ^ 36 +
      357733903081678771275187270196050790))) +
  coefficientTerm 48
    ((13605 : ℚ) * 10 ^ 36 +
      161479938208492330752217864497542950) +
  coefficientTerm 47
    (-(((2152 : ℚ) * 10 ^ 36 +
      308770064237127132524531763156832807))) +
  coefficientTerm 46
    (-(((2313 : ℚ) * 10 ^ 36 +
      397951131299979484562234548645331533))) +
  coefficientTerm 45
    ((1843 : ℚ) * 10 ^ 36 +
      633365605491117655945097149061072270)

/-- Internal datum. -/ def quotient0Coefficient5Chunk5 : Coefficient :=
  coefficientTerm 44
    (-(((432 : ℚ) * 10 ^ 36 +
      478511147513082610114886620476674225))) +
  coefficientTerm 43
    (-(((171 : ℚ) * 10 ^ 36 +
      647949602554757907859912445768359022))) +
  coefficientTerm 42
    ((150 : ℚ) * 10 ^ 36 +
      121309469371876471156908431491985576) +
  coefficientTerm 41
    (-(((26 : ℚ) * 10 ^ 36 +
      648575737039101570600873687276979544))) +
  coefficientTerm 40
    (-(((14 : ℚ) * 10 ^ 36 +
      386346286868004463684035741939008829))) +
  coefficientTerm 39
    ((8 : ℚ) * 10 ^ 36 +
      067332249366823161333717763424130444) +
  coefficientTerm 38
    (-((248937506416243363803508856353346985 : ℚ))) +
  coefficientTerm 37
    (-((918289105320866357623717135258683398 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient5Chunk6 : Coefficient :=
  coefficientTerm 36
    (219456391203069055732897905934964318 : ℚ) +
  coefficientTerm 35
    (54334890927183028405764922381206176 : ℚ) +
  coefficientTerm 34
    (-((29601398194489273973937145812047364 : ℚ))) +
  coefficientTerm 33
    (-((633964987663398401564010119059768 : ℚ))) +
  coefficientTerm 32
    (2464692001528789975526417926818752 : ℚ) +
  coefficientTerm 31
    (-((202872511799384382578893522026010 : ℚ))) +
  coefficientTerm 30
    (-((150900341882269328967095537217479 : ℚ))) +
  coefficientTerm 29
    (23108647651715198218873805266691 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient5Chunk7 : Coefficient :=
  coefficientTerm 28
    (7343881952910678415893607501227 : ℚ) +
  coefficientTerm 27
    (-((1499709758153528624535232405078 : ℚ))) +
  coefficientTerm 26
    (-((307494022452497489822952820306 : ℚ))) +
  coefficientTerm 25
    (71274264407267811802259730770 : ℚ) +
  coefficientTerm 24
    (10854571412262273986236317034 : ℚ) +
  coefficientTerm 23
    (-((2311068646611267066727456909 : ℚ))) +
  coefficientTerm 22
    (-((408203335028467760455663167 : ℚ))) +
  coefficientTerm 21
    (71839931249992601846909184 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient5Chunk8 : Coefficient :=
  coefficientTerm 20
    (7858491969148126336058950 : ℚ) +
  coefficientTerm 19
    (-((495676701722465043589307 : ℚ))) +
  coefficientTerm 18
    (-((334455467890816440182439 : ℚ))) +
  coefficientTerm 17
    (29360863297948165874590 : ℚ) +
  coefficientTerm 16
    (327477749468849145981 : ℚ) +
  coefficientTerm 15
    (404905425969228264700 : ℚ) +
  coefficientTerm 14
    (-((79275757486581053046 : ℚ))) +
  coefficientTerm 13
    (3840723934632384010 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient5Chunk9 : Coefficient :=
  coefficientTerm 12
    (-((183682841725198734 : ℚ))) +
  coefficientTerm 11
    (25325158003665245 : ℚ) +
  coefficientTerm 10
    (-((1220059648982744 : ℚ))) +
  coefficientTerm 9
    (5699276158673 : ℚ) +
  coefficientTerm 8
    (542530075591 : ℚ) +
  coefficientTerm 7
    (-((5881433547 : ℚ))) +
  coefficientTerm 6
    (-((5022398 : ℚ))) +
  coefficientTerm 5
    (15313 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient5Block0 : Coefficient :=
  quotient0Coefficient5Chunk0 +
  quotient0Coefficient5Chunk1 +
  quotient0Coefficient5Chunk2 +
  quotient0Coefficient5Chunk3 +
  quotient0Coefficient5Chunk4 +
  quotient0Coefficient5Chunk5 +
  quotient0Coefficient5Chunk6 +
  quotient0Coefficient5Chunk7 +
  quotient0Coefficient5Chunk8 +
  quotient0Coefficient5Chunk9

/-- Internal datum. -/ def quotient0Coefficient5 : Coefficient :=
  quotient0Coefficient5Block0

/-- Internal datum. -/ def quotient0Coefficient6Chunk0 : Coefficient :=
  coefficientTerm 81
    (-((1 : ℚ))) +
  coefficientTerm 80
    (-((97572766 : ℚ))) +
  coefficientTerm 79
    (-((5102338021913 : ℚ))) +
  coefficientTerm 78
    (-((13261583204744022 : ℚ))) +
  coefficientTerm 77
    (-((2891813895722644350 : ℚ))) +
  coefficientTerm 76
    (2970141993124317056434 : ℚ) +
  coefficientTerm 75
    (1340338557356751208265939 : ℚ) +
  coefficientTerm 74
    (195020638397294814686802379 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient6Chunk1 : Coefficient :=
  coefficientTerm 73
    (11450436569085763108743288466 : ℚ) +
  coefficientTerm 72
    (256426264743023879579053497735 : ℚ) +
  coefficientTerm 71
    (889224828242588088737059409384 : ℚ) +
  coefficientTerm 70
    (-((25436865498387988317023256723039 : ℚ))) +
  coefficientTerm 69
    (-((42312252127065537944134556777347 : ℚ))) +
  coefficientTerm 68
    (1498256133436424954561059992838287 : ℚ) +
  coefficientTerm 67
    (-((4364623398082170155929768295277959 : ℚ))) +
  coefficientTerm 66
    (-((24706242248721125396113437178438076 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient6Chunk2 : Coefficient :=
  coefficientTerm 65
    (210798886427101452376082992232889082 : ℚ) +
  coefficientTerm 64
    (-((520842368476867525166125926094060383 : ℚ))) +
  coefficientTerm 63
    (-((594968323721703038099999833033676217 : ℚ))) +
  coefficientTerm 62
    ((7 : ℚ) * 10 ^ 36 +
      986168455681384854946205786135808102) +
  coefficientTerm 61
    (-(((25 : ℚ) * 10 ^ 36 +
      663336417407572316827841553584171371))) +
  coefficientTerm 60
    ((37 : ℚ) * 10 ^ 36 +
      805700183925095344355345685755724930) +
  coefficientTerm 59
    ((14 : ℚ) * 10 ^ 36 +
      353750698742284928075779013156239715) +
  coefficientTerm 58
    (-(((210 : ℚ) * 10 ^ 36 +
      248376039189960005190809071640437697)))

/-- Internal datum. -/ def quotient0Coefficient6Chunk3 : Coefficient :=
  coefficientTerm 57
    ((540 : ℚ) * 10 ^ 36 +
      616379353376639775096911599261311018) +
  coefficientTerm 56
    (-(((786 : ℚ) * 10 ^ 36 +
      051338457473510936896803835185225535))) +
  coefficientTerm 55
    ((580 : ℚ) * 10 ^ 36 +
      191290776888559515288235162651563633) +
  coefficientTerm 54
    ((259 : ℚ) * 10 ^ 36 +
      869251767663678142569067427397008325) +
  coefficientTerm 53
    (-(((1409 : ℚ) * 10 ^ 36 +
      474749579081132448667942254732823778))) +
  coefficientTerm 52
    ((2151 : ℚ) * 10 ^ 36 +
      430477078128547237935923252042742117) +
  coefficientTerm 51
    (-(((1958 : ℚ) * 10 ^ 36 +
      474579018592967267098045919399628614))) +
  coefficientTerm 50
    ((984 : ℚ) * 10 ^ 36 +
      488879150759898792696538388614004018)

/-- Internal datum. -/ def quotient0Coefficient6Chunk4 : Coefficient :=
  coefficientTerm 49
    ((77 : ℚ) * 10 ^ 36 +
      515950338811536372073128793021933263) +
  coefficientTerm 48
    (-(((620 : ℚ) * 10 ^ 36 +
      204020922678957940099914061403113441))) +
  coefficientTerm 47
    ((565 : ℚ) * 10 ^ 36 +
      389401152865633030320943013502632223) +
  coefficientTerm 46
    (-(((247 : ℚ) * 10 ^ 36 +
      769199650870296456704407785664631206))) +
  coefficientTerm 45
    ((4 : ℚ) * 10 ^ 36 +
      263429450523067153732741849660688326) +
  coefficientTerm 44
    ((65 : ℚ) * 10 ^ 36 +
      675449582666739069410985856624873469) +
  coefficientTerm 43
    (-(((38 : ℚ) * 10 ^ 36 +
      701803310593846229062654847486635735))) +
  coefficientTerm 42
    ((5 : ℚ) * 10 ^ 36 +
      110887608705158139083365945572970131)

/-- Internal datum. -/ def quotient0Coefficient6Chunk5 : Coefficient :=
  coefficientTerm 41
    ((5 : ℚ) * 10 ^ 36 +
      525660295922360344913444727713875447) +
  coefficientTerm 40
    (-(((3 : ℚ) * 10 ^ 36 +
      206581093524314506743485191281289412))) +
  coefficientTerm 39
    (235073162098786623818572555357369455 : ℚ) +
  coefficientTerm 38
    (421808874825335547805812492882480525 : ℚ) +
  coefficientTerm 37
    (-((156099771908046732846854122367405314 : ℚ))) +
  coefficientTerm 36
    (-((15096478338857847085818432196687179 : ℚ))) +
  coefficientTerm 35
    (22285864445381525598271668890634638 : ℚ) +
  coefficientTerm 34
    (-((2794325699465810853254425485129652 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient6Chunk6 : Coefficient :=
  coefficientTerm 33
    (-((1786341224624752423746346975408639 : ℚ))) +
  coefficientTerm 32
    (533921343697901042818556377332562 : ℚ) +
  coefficientTerm 31
    (84449677588104908055902532915694 : ℚ) +
  coefficientTerm 30
    (-((51640288946197131041543923514255 : ℚ))) +
  coefficientTerm 29
    (-((1331814964844011093986695819234 : ℚ))) +
  coefficientTerm 28
    (3512399043214523186614924500957 : ℚ) +
  coefficientTerm 27
    (-((123762974448814357559457019392 : ℚ))) +
  coefficientTerm 26
    (-((190604790782476691186670687635 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient6Chunk7 : Coefficient :=
  coefficientTerm 25
    (13643425459374195935648264278 : ℚ) +
  coefficientTerm 24
    (7825504639460634817134125227 : ℚ) +
  coefficientTerm 23
    (-((448287998858452409721338522 : ℚ))) +
  coefficientTerm 22
    (-((347670190789769133130685133 : ℚ))) +
  coefficientTerm 21
    (30903896442780015565151603 : ℚ) +
  coefficientTerm 20
    (5220729225597893552085590 : ℚ) +
  coefficientTerm 19
    (648839497039813578833199 : ℚ) +
  coefficientTerm 18
    (-((396621712348203407148353 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient6Chunk8 : Coefficient :=
  coefficientTerm 17
    (34864162851813120801175 : ℚ) +
  coefficientTerm 16
    (-((2633342091567474515292 : ℚ))) +
  coefficientTerm 15
    (991767771069764886687 : ℚ) +
  coefficientTerm 14
    (-((142359733512149749544 : ℚ))) +
  coefficientTerm 13
    (8540762942250678347 : ℚ) +
  coefficientTerm 12
    (-((604004923305461578 : ℚ))) +
  coefficientTerm 11
    (60943750854305368 : ℚ) +
  coefficientTerm 10
    (-((2224373241547435 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient6Chunk9 : Coefficient :=
  coefficientTerm 9
    (-((38564589883913 : ℚ))) +
  coefficientTerm 8
    (3034245317600 : ℚ) +
  coefficientTerm 7
    (-((30053433569 : ℚ))) +
  coefficientTerm 6
    (-((84066643 : ℚ))) +
  coefficientTerm 5
    (288784 : ℚ) +
  coefficientTerm 4
    (32 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient6Block0 : Coefficient :=
  quotient0Coefficient6Chunk0 +
  quotient0Coefficient6Chunk1 +
  quotient0Coefficient6Chunk2 +
  quotient0Coefficient6Chunk3 +
  quotient0Coefficient6Chunk4 +
  quotient0Coefficient6Chunk5 +
  quotient0Coefficient6Chunk6 +
  quotient0Coefficient6Chunk7 +
  quotient0Coefficient6Chunk8 +
  quotient0Coefficient6Chunk9

/-- Internal datum. -/ def quotient0Coefficient6 : Coefficient :=
  quotient0Coefficient6Block0

/-- Internal datum. -/ def quotient0Coefficient7Chunk0 : Coefficient :=
  coefficientTerm 77
    (-((43 : ℚ))) +
  coefficientTerm 76
    (-((419598563 : ℚ))) +
  coefficientTerm 75
    (-((9330033834383 : ℚ))) +
  coefficientTerm 74
    (-((12529815173464867 : ℚ))) +
  coefficientTerm 73
    (527093011382691541 : ℚ) +
  coefficientTerm 72
    (2980025976250693236866 : ℚ) +
  coefficientTerm 71
    (836004043805329651935018 : ℚ) +
  coefficientTerm 70
    (83635391946776520830357994 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient7Chunk1 : Coefficient :=
  coefficientTerm 69
    (3258293082213397858191266080 : ℚ) +
  coefficientTerm 68
    (39456986556847189126116870071 : ℚ) +
  coefficientTerm 67
    (-((193285316510054997967317826154 : ℚ))) +
  coefficientTerm 66
    (-((3508820487250468352518182223017 : ℚ))) +
  coefficientTerm 65
    (20205442639256315248370163270020 : ℚ) +
  coefficientTerm 64
    (75255155126756179798999627653240 : ℚ) +
  coefficientTerm 63
    (-((968545076358056587349262780643708 : ℚ))) +
  coefficientTerm 62
    (2626230744660991436800741384796602 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient7Chunk2 : Coefficient :=
  coefficientTerm 61
    (5593336951671834263309807309306030 : ℚ) +
  coefficientTerm 60
    (-((60653051641946939409231279121149535 : ℚ))) +
  coefficientTerm 59
    (188528950900822113875930382951948758 : ℚ) +
  coefficientTerm 58
    (-((209597856889332351039656264397456595 : ℚ))) +
  coefficientTerm 57
    (-((517537885543886041934039820247525476 : ℚ))) +
  coefficientTerm 56
    ((2 : ℚ) * 10 ^ 36 +
      819997744791136701916828401744090859) +
  coefficientTerm 55
    (-(((6 : ℚ) * 10 ^ 36 +
      308585137426494286094116712299375628))) +
  coefficientTerm 54
    ((7 : ℚ) * 10 ^ 36 +
      784858089638462342984197594472022006)

/-- Internal datum. -/ def quotient0Coefficient7Chunk3 : Coefficient :=
  coefficientTerm 53
    (-(((2 : ℚ) * 10 ^ 36 +
      264959973111221416061274971320189478))) +
  coefficientTerm 52
    (-(((12 : ℚ) * 10 ^ 36 +
      046187972585781537117607053346062156))) +
  coefficientTerm 51
    ((28 : ℚ) * 10 ^ 36 +
      999468920723720028059671361507354944) +
  coefficientTerm 50
    (-(((36 : ℚ) * 10 ^ 36 +
      907683248160869317462678045044837275))) +
  coefficientTerm 49
    ((28 : ℚ) * 10 ^ 36 +
      469031666076094571410921478553852446) +
  coefficientTerm 48
    (-(((8 : ℚ) * 10 ^ 36 +
      509257221457057384451816019577474465))) +
  coefficientTerm 47
    (-(((9 : ℚ) * 10 ^ 36 +
      718405548490138775765589633223512665))) +
  coefficientTerm 46
    ((16 : ℚ) * 10 ^ 36 +
      277664941190342204989207282149580322)

/-- Internal datum. -/ def quotient0Coefficient7Chunk4 : Coefficient :=
  coefficientTerm 45
    (-(((11 : ℚ) * 10 ^ 36 +
      823415230716139070104336818703405160))) +
  coefficientTerm 44
    ((4 : ℚ) * 10 ^ 36 +
      020182749037194466364907417616004348) +
  coefficientTerm 43
    (808519573805719665735637557558005551 : ℚ) +
  coefficientTerm 42
    (-(((1 : ℚ) * 10 ^ 36 +
      661209594069037812097039710297876348))) +
  coefficientTerm 41
    (752820755516327057846659699544196104 : ℚ) +
  coefficientTerm 40
    (-((7338014528329733179895845294974533 : ℚ))) +
  coefficientTerm 39
    (-((151924451869101972163409427155197537 : ℚ))) +
  coefficientTerm 38
    (63040554902159098530428415838255374 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient7Chunk5 : Coefficient :=
  coefficientTerm 37
    (3234269370485591183751189122325329 : ℚ) +
  coefficientTerm 36
    (-((10899692477960598875819283141538731 : ℚ))) +
  coefficientTerm 35
    (2633806207672305968035004775269916 : ℚ) +
  coefficientTerm 34
    (769823720081050434042795690041083 : ℚ) +
  coefficientTerm 33
    (-((486373462464709501205860039993770 : ℚ))) +
  coefficientTerm 32
    (8608827881152548395753889197111 : ℚ) +
  coefficientTerm 31
    (47738761963556718289858620945151 : ℚ) +
  coefficientTerm 30
    (-((7633385138039147411040833047368 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient7Chunk6 : Coefficient :=
  coefficientTerm 29
    (-((3109779768004375275896025051696 : ℚ))) +
  coefficientTerm 28
    (900356003608224312409190309219 : ℚ) +
  coefficientTerm 27
    (147754557576228989765121304073 : ℚ) +
  coefficientTerm 26
    (-((69016793786107459665459181869 : ℚ))) +
  coefficientTerm 25
    (-((4435745134342878483208643902 : ℚ))) +
  coefficientTerm 24
    (3485656991424683445880244386 : ℚ) +
  coefficientTerm 23
    (260590961349608777277181911 : ℚ) +
  coefficientTerm 22
    (-((200740678648083753522232703 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient7Chunk7 : Coefficient :=
  coefficientTerm 21
    (6581630101489075287103271 : ℚ) +
  coefficientTerm 20
    (1936789087027061765323727 : ℚ) +
  coefficientTerm 19
    (1196927331791225707689885 : ℚ) +
  coefficientTerm 18
    (-((360773927826019022224598 : ℚ))) +
  coefficientTerm 17
    (35021569906368039279442 : ℚ) +
  coefficientTerm 16
    (-((5385534252140378584364 : ℚ))) +
  coefficientTerm 15
    (1473742288849378812178 : ℚ) +
  coefficientTerm 14
    (-((188317122673899942244 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient7Chunk8 : Coefficient :=
  coefficientTerm 13
    (12248835066627578624 : ℚ) +
  coefficientTerm 12
    (-((976136936762882823 : ℚ))) +
  coefficientTerm 11
    (83146675654615525 : ℚ) +
  coefficientTerm 10
    (-((695296107701598 : ℚ))) +
  coefficientTerm 9
    (-((293731156008885 : ℚ))) +
  coefficientTerm 8
    (12447587616605 : ℚ) +
  coefficientTerm 7
    (-((102490377973 : ℚ))) +
  coefficientTerm 6
    (-((920903373 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient7Chunk9 : Coefficient :=
  coefficientTerm 5
    (3410229 : ℚ) +
  coefficientTerm 4
    (1644 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient7Block0 : Coefficient :=
  quotient0Coefficient7Chunk0 +
  quotient0Coefficient7Chunk1 +
  quotient0Coefficient7Chunk2 +
  quotient0Coefficient7Chunk3 +
  quotient0Coefficient7Chunk4 +
  quotient0Coefficient7Chunk5 +
  quotient0Coefficient7Chunk6 +
  quotient0Coefficient7Chunk7 +
  quotient0Coefficient7Chunk8 +
  quotient0Coefficient7Chunk9

/-- Internal datum. -/ def quotient0Coefficient7 : Coefficient :=
  quotient0Coefficient7Block0

/-- Internal datum. -/ def quotient0Coefficient8Chunk0 : Coefficient :=
  coefficientTerm 73
    (-((852 : ℚ))) +
  coefficientTerm 72
    (-((1456076741 : ℚ))) +
  coefficientTerm 71
    (-((14215515923968 : ℚ))) +
  coefficientTerm 70
    (-((9154862876488493 : ℚ))) +
  coefficientTerm 69
    (2983998133091183339 : ℚ) +
  coefficientTerm 68
    (2443913544292795500558 : ℚ) +
  coefficientTerm 67
    (450247074497377570454744 : ℚ) +
  coefficientTerm 66
    (30294800302565346054839590 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient8Chunk1 : Coefficient :=
  coefficientTerm 65
    (728361831618794492200511603 : ℚ) +
  coefficientTerm 64
    (2656947994568280023095902279 : ℚ) +
  coefficientTerm 63
    (-((68904976090964084995595916763 : ℚ))) +
  coefficientTerm 62
    (-((73277180330165060546335725565 : ℚ))) +
  coefficientTerm 61
    (3550417598552182656406176639904 : ℚ) +
  coefficientTerm 60
    (-((12544991124878113887371800623164 : ℚ))) +
  coefficientTerm 59
    (-((32603291213758113694662047813190 : ℚ))) +
  coefficientTerm 58
    (382764825272279994431815280573605 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient8Chunk2 : Coefficient :=
  coefficientTerm 57
    (-((1199791635297922843311864669380425 : ℚ))) +
  coefficientTerm 56
    (740652125228914512615993809902402 : ℚ) +
  coefficientTerm 55
    (7343756818923106396862944024186433 : ℚ) +
  coefficientTerm 54
    (-((30931176379075825698631052993376321 : ℚ))) +
  coefficientTerm 53
    (62350639691553486378201388049288618 : ℚ) +
  coefficientTerm 52
    (-((57925102729972523420808451752961020 : ℚ))) +
  coefficientTerm 51
    (-((47093939913313116096331280972502563 : ℚ))) +
  coefficientTerm 50
    (266186985321203410557079171577321922 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient8Chunk3 : Coefficient :=
  coefficientTerm 49
    (-((492581451950127320797754982604813709 : ℚ))) +
  coefficientTerm 48
    (543635068375634151718512707558404412 : ℚ) +
  coefficientTerm 47
    (-((325408215888467279405598294784172469 : ℚ))) +
  coefficientTerm 46
    (-((46979638020936122298306202183170119 : ℚ))) +
  coefficientTerm 45
    (331521012691430453543615304827759946 : ℚ) +
  coefficientTerm 44
    (-((374626812901928499840828142453886368 : ℚ))) +
  coefficientTerm 43
    (227005486750351077464003857072138591 : ℚ) +
  coefficientTerm 42
    (-((52800782639252176430879433718023564 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient8Chunk4 : Coefficient :=
  coefficientTerm 41
    (-((35431065459366661946094630854757297 : ℚ))) +
  coefficientTerm 40
    (38696339043621448520381093055270607 : ℚ) +
  coefficientTerm 39
    (-((13279140588047895377143845589312845 : ℚ))) +
  coefficientTerm 38
    (-((2188801180114013289909400140456196 : ℚ))) +
  coefficientTerm 37
    (3789363497958706630003598915350293 : ℚ) +
  coefficientTerm 36
    (-((1113234536729341072101660492055248 : ℚ))) +
  coefficientTerm 35
    (-((257889387386946984788514574596920 : ℚ))) +
  coefficientTerm 34
    (256821087510000707377830956529832 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient8Chunk5 : Coefficient :=
  coefficientTerm 33
    (-((34321226694834443375596922175576 : ℚ))) +
  coefficientTerm 32
    (-((25313424194509509055839864675155 : ℚ))) +
  coefficientTerm 31
    (9482355707698208365175762262562 : ℚ) +
  coefficientTerm 30
    (1023478996812386435381860316798 : ℚ) +
  coefficientTerm 29
    (-((1104968537468628990294817836258 : ℚ))) +
  coefficientTerm 28
    (52961212811231501660679441871 : ℚ) +
  coefficientTerm 27
    (86367119524926021224771191375 : ℚ) +
  coefficientTerm 26
    (-((12260400059314508821828899772 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient8Chunk6 : Coefficient :=
  coefficientTerm 25
    (-((4781357090083847127616771247 : ℚ))) +
  coefficientTerm 24
    (900784383870160316032848783 : ℚ) +
  coefficientTerm 23
    (287833131266233980013239315 : ℚ) +
  coefficientTerm 22
    (-((75842065815002704781161002 : ℚ))) +
  coefficientTerm 21
    (-((3423684351740304829253723 : ℚ))) +
  coefficientTerm 20
    (163928394001347601615251 : ℚ) +
  coefficientTerm 19
    (1006607881616192047962827 : ℚ) +
  coefficientTerm 18
    (-((225492025207686686720108 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient8Chunk7 : Coefficient :=
  coefficientTerm 17
    (22024953494934696563767 : ℚ) +
  coefficientTerm 16
    (-((5121424946994373740027 : ℚ))) +
  coefficientTerm 15
    (1338194080108908410287 : ℚ) +
  coefficientTerm 14
    (-((148367502202490698770 : ℚ))) +
  coefficientTerm 13
    (6824511727894220562 : ℚ) +
  coefficientTerm 12
    (-((381890508652799633 : ℚ))) +
  coefficientTerm 11
    (1586490181640664 : ℚ) +
  coefficientTerm 10
    (10077784604731897 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient8Chunk8 : Coefficient :=
  coefficientTerm 9
    (-((1091736602958074 : ℚ))) +
  coefficientTerm 8
    (36285904778558 : ℚ) +
  coefficientTerm 7
    (-((147205013140 : ℚ))) +
  coefficientTerm 6
    (-((7012552011 : ℚ))) +
  coefficientTerm 5
    (26266288 : ℚ) +
  coefficientTerm 4
    (38812 : ℚ) +
  coefficientTerm 3
    (1 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient8Block0 : Coefficient :=
  quotient0Coefficient8Chunk0 +
  quotient0Coefficient8Chunk1 +
  quotient0Coefficient8Chunk2 +
  quotient0Coefficient8Chunk3 +
  quotient0Coefficient8Chunk4 +
  quotient0Coefficient8Chunk5 +
  quotient0Coefficient8Chunk6 +
  quotient0Coefficient8Chunk7 +
  quotient0Coefficient8Chunk8

/-- Internal datum. -/ def quotient0Coefficient8 : Coefficient :=
  quotient0Coefficient8Block0

/-- Internal datum. -/ def quotient0Coefficient9Chunk0 : Coefficient :=
  coefficientTerm 69
    (-((10301 : ℚ))) +
  coefficientTerm 68
    (-((4086554106 : ℚ))) +
  coefficientTerm 67
    (-((17781154148144 : ℚ))) +
  coefficientTerm 66
    (-((4157003441354283 : ℚ))) +
  coefficientTerm 65
    (4107472736005449912 : ℚ) +
  coefficientTerm 64
    (1697410837865813806807 : ℚ) +
  coefficientTerm 63
    (206978601281310653341892 : ℚ) +
  coefficientTerm 62
    (8988557453323120297335401 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient9Chunk1 : Coefficient :=
  coefficientTerm 61
    (114136116226209934315437346 : ℚ) +
  coefficientTerm 60
    (-((529642133051990507775384028 : ℚ))) +
  coefficientTerm 59
    (-((8933145695393242429024567624 : ℚ))) +
  coefficientTerm 58
    (54687925759588761139427871830 : ℚ) +
  coefficientTerm 57
    (113484213528424956541685828521 : ℚ) +
  coefficientTerm 56
    (-((1979043818499616750801264014209 : ℚ))) +
  coefficientTerm 55
    (6685662310909528986112295504313 : ℚ) +
  coefficientTerm 54
    (-((43265463788500026363855093423 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient9Chunk2 : Coefficient :=
  coefficientTerm 53
    (-((74151556052975730968199312651026 : ℚ))) +
  coefficientTerm 52
    (283996570987881736181748338047403 : ℚ) +
  coefficientTerm 51
    (-((513948320446880668723931984132351 : ℚ))) +
  coefficientTerm 50
    (208643390350080204731190594684507 : ℚ) +
  coefficientTerm 49
    (1431202826829384695660494196617852 : ℚ) +
  coefficientTerm 48
    (-((4436951511990983528070180557477920 : ℚ))) +
  coefficientTerm 47
    (7081451998354474419574542631804489 : ℚ) +
  coefficientTerm 46
    (-((6625083768176088999373564739682741 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient9Chunk3 : Coefficient :=
  coefficientTerm 45
    (1974341241833030964144251161264113 : ℚ) +
  coefficientTerm 44
    (4462491430494388896154837665963308 : ℚ) +
  coefficientTerm 43
    (-((8435802244197689467709372561063263 : ℚ))) +
  coefficientTerm 42
    (7719126488876290007490486423690888 : ℚ) +
  coefficientTerm 41
    (-((3907936666875792591803601011830769 : ℚ))) +
  coefficientTerm 40
    (337862016650285943867916348688656 : ℚ) +
  coefficientTerm 39
    (1100171583168553342421808189363983 : ℚ) +
  coefficientTerm 38
    (-((841818618028512884793990517583394 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient9Chunk4 : Coefficient :=
  coefficientTerm 37
    (200713309499726259783647933461027 : ℚ) +
  coefficientTerm 36
    (97577070905644996026153492773846 : ℚ) +
  coefficientTerm 35
    (-((87803539034108738839094065390862 : ℚ))) +
  coefficientTerm 34
    (16499245731176850395566015976995 : ℚ) +
  coefficientTerm 33
    (9514390074980293426617686316895 : ℚ) +
  coefficientTerm 32
    (-((5572531182366432816856457710955 : ℚ))) +
  coefficientTerm 31
    (144926804755518986506230180733 : ℚ) +
  coefficientTerm 30
    (693396939967700311118140910731 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient9Chunk5 : Coefficient :=
  coefficientTerm 29
    (-((158045238662527392259774895818 : ℚ))) +
  coefficientTerm 28
    (-((47440374714732268428852012843 : ℚ))) +
  coefficientTerm 27
    (22531121599409999294086477199 : ℚ) +
  coefficientTerm 26
    (1409999528032684073791973638 : ℚ) +
  coefficientTerm 25
    (-((1916664648991409222828366256 : ℚ))) +
  coefficientTerm 24
    (23877467101396059956145422 : ℚ) +
  coefficientTerm 23
    (137429462609950389607736242 : ℚ) +
  coefficientTerm 22
    (-((12936970655015005892742359 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient9Chunk6 : Coefficient :=
  coefficientTerm 21
    (-((4673299109620291527237733 : ℚ))) +
  coefficientTerm 20
    (-((188227517583038791980083 : ℚ))) +
  coefficientTerm 19
    (489752044787577500131601 : ℚ) +
  coefficientTerm 18
    (-((70536101856997181969020 : ℚ))) +
  coefficientTerm 17
    (1870937715883645022783 : ℚ) +
  coefficientTerm 16
    (-((1783478480001474290769 : ℚ))) +
  coefficientTerm 15
    (521214181310732201326 : ℚ) +
  coefficientTerm 14
    (-((5688032574213871920 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient9Chunk7 : Coefficient :=
  coefficientTerm 13
    (-((11736491938324185188 : ℚ))) +
  coefficientTerm 12
    (1851132239420395605 : ℚ) +
  coefficientTerm 11
    (-((257890172443693818 : ℚ))) +
  coefficientTerm 10
    (34990652583250472 : ℚ) +
  coefficientTerm 9
    (-((2567229086288468 : ℚ))) +
  coefficientTerm 8
    (67125405023138 : ℚ) +
  coefficientTerm 7
    (627900343839 : ℚ) +
  coefficientTerm 6
    (-((38099958375 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient9Chunk8 : Coefficient :=
  coefficientTerm 5
    (126565857 : ℚ) +
  coefficientTerm 4
    (553417 : ℚ) +
  coefficientTerm 3
    (62 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient9Block0 : Coefficient :=
  quotient0Coefficient9Chunk0 +
  quotient0Coefficient9Chunk1 +
  quotient0Coefficient9Chunk2 +
  quotient0Coefficient9Chunk3 +
  quotient0Coefficient9Chunk4 +
  quotient0Coefficient9Chunk5 +
  quotient0Coefficient9Chunk6 +
  quotient0Coefficient9Chunk7 +
  quotient0Coefficient9Chunk8

/-- Internal datum. -/ def quotient0Coefficient9 : Coefficient :=
  quotient0Coefficient9Block0

/-- Internal datum. -/ def quotient0Coefficient10Chunk0 : Coefficient :=
  coefficientTerm 65
    (-((84795 : ℚ))) +
  coefficientTerm 64
    (-((9249791357 : ℚ))) +
  coefficientTerm 63
    (-((17764301785637 : ℚ))) +
  coefficientTerm 62
    (776213213900766 : ℚ) +
  coefficientTerm 61
    (4037297054161828142 : ℚ) +
  coefficientTerm 60
    (1004429494391053719601 : ℚ) +
  coefficientTerm 59
    (79580713251232334586924 : ℚ) +
  coefficientTerm 58
    (2071460432327377445916385 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient10Chunk1 : Coefficient :=
  coefficientTerm 57
    (7792924832715496911205179 : ℚ) +
  coefficientTerm 56
    (-((186003897681485984918127297 : ℚ))) +
  coefficientTerm 55
    (-((69742675695314315285232871 : ℚ))) +
  coefficientTerm 54
    (8004733231804259736724782048 : ℚ) +
  coefficientTerm 53
    (-((33108869393634454942475653908 : ℚ))) +
  coefficientTerm 52
    (-((17708037596890999345383083688 : ℚ))) +
  coefficientTerm 51
    (581689920063838594482030996429 : ℚ) +
  coefficientTerm 50
    (-((2196118772006503543983081679520 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient10Chunk2 : Coefficient :=
  coefficientTerm 49
    (3430858265552132386489949626593 : ℚ) +
  coefficientTerm 48
    (2205842478685754649899198499563 : ℚ) +
  coefficientTerm 47
    (-((23993997552628312472156482314438 : ℚ))) +
  coefficientTerm 46
    (60477688619674247714573245208261 : ℚ) +
  coefficientTerm 45
    (-((85398379220417501073074069304283 : ℚ))) +
  coefficientTerm 44
    (59242630643719234652037291354957 : ℚ) +
  coefficientTerm 43
    (28925035648794235898816729963355 : ℚ) +
  coefficientTerm 42
    (-((132862117486622853909863967272945 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient10Chunk3 : Coefficient :=
  coefficientTerm 41
    (180439592547701337189809680331009 : ℚ) +
  coefficientTerm 40
    (-((141750973199686172586763680333535 : ℚ))) +
  coefficientTerm 39
    (56531754433438804142282080539111 : ℚ) +
  coefficientTerm 38
    (10428338205852998025375198120902 : ℚ) +
  coefficientTerm 37
    (-((29538931435552719324784820772228 : ℚ))) +
  coefficientTerm 36
    (17197451502312262492911239041775 : ℚ) +
  coefficientTerm 35
    (-((2137920407938866711630599247632 : ℚ))) +
  coefficientTerm 34
    (-((3116641904907914921780192778750 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient10Chunk4 : Coefficient :=
  coefficientTerm 33
    (1907346498956432283565885337033 : ℚ) +
  coefficientTerm 32
    (-((156997346791560039116974498050 : ℚ))) +
  coefficientTerm 31
    (-((280952177367410597481707163202 : ℚ))) +
  coefficientTerm 30
    (110637022859592513367366963935 : ℚ) +
  coefficientTerm 29
    (11065676246206088287813137766 : ℚ) +
  coefficientTerm 28
    (-((16823032640914348932772049342 : ℚ))) +
  coefficientTerm 27
    (1939581635192245753654157097 : ℚ) +
  coefficientTerm 26
    (1469357234716721234973888442 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient10Chunk5 : Coefficient :=
  coefficientTerm 25
    (-((382015301682906618321088862 : ℚ))) +
  coefficientTerm 24
    (-((86444626530095748188149253 : ℚ))) +
  coefficientTerm 23
    (37424802258461604466893693 : ℚ) +
  coefficientTerm 22
    (3719117765314567027776013 : ℚ) +
  coefficientTerm 21
    (-((2581598458589569356419158 : ℚ))) +
  coefficientTerm 20
    (-((118429899787348278957952 : ℚ))) +
  coefficientTerm 19
    (118085308205166841495617 : ℚ) +
  coefficientTerm 18
    (16047247793994515121458 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient10Chunk6 : Coefficient :=
  coefficientTerm 17
    (-((9998516435698062310921 : ℚ))) +
  coefficientTerm 16
    (1294634071212289664079 : ℚ) +
  coefficientTerm 15
    (-((311784689653804144618 : ℚ))) +
  coefficientTerm 14
    (138476878543042106366 : ℚ) +
  coefficientTerm 13
    (-((31375386223411656567 : ℚ))) +
  coefficientTerm 12
    (4463281425242257161 : ℚ) +
  coefficientTerm 11
    (-((567997221649766418 : ℚ))) +
  coefficientTerm 10
    (61606937238503783 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient10Chunk7 : Coefficient :=
  coefficientTerm 9
    (-((3688324040838516 : ℚ))) +
  coefficientTerm 8
    (39646449800931 : ℚ) +
  coefficientTerm 7
    (4996930698843 : ℚ) +
  coefficientTerm 6
    (-((147430657763 : ℚ))) +
  coefficientTerm 5
    (272460463 : ℚ) +
  coefficientTerm 4
    (5278078 : ℚ) +
  coefficientTerm 3
    (1748 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient10Block0 : Coefficient :=
  quotient0Coefficient10Chunk0 +
  quotient0Coefficient10Chunk1 +
  quotient0Coefficient10Chunk2 +
  quotient0Coefficient10Chunk3 +
  quotient0Coefficient10Chunk4 +
  quotient0Coefficient10Chunk5 +
  quotient0Coefficient10Chunk6 +
  quotient0Coefficient10Chunk7

/-- Internal datum. -/ def quotient0Coefficient10 : Coefficient :=
  quotient0Coefficient10Block0

/-- Internal datum. -/ def quotient0Coefficient11Chunk0 : Coefficient :=
  coefficientTerm 61
    (-((501818 : ℚ))) +
  coefficientTerm 60
    (-((16740055869 : ℚ))) +
  coefficientTerm 59
    (-((13315292426088 : ℚ))) +
  coefficientTerm 58
    (4243882750942817 : ℚ) +
  coefficientTerm 57
    (3214495505835905087 : ℚ) +
  coefficientTerm 56
    (501690485853735664236 : ℚ) +
  coefficientTerm 55
    (24773952029183853923053 : ℚ) +
  coefficientTerm 54
    (329889455686482806942765 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient11Chunk1 : Coefficient :=
  coefficientTerm 53
    (-((1476162313969364619948234 : ℚ))) +
  coefficientTerm 52
    (-((22114829662490677320905604 : ℚ))) +
  coefficientTerm 51
    (144281431396516244912370606 : ℚ) +
  coefficientTerm 50
    (85686349294762751923827716 : ℚ) +
  coefficientTerm 49
    (-((3581623366995158787063395832 : ℚ))) +
  coefficientTerm 48
    (14325354834507198555167823465 : ℚ) +
  coefficientTerm 47
    (-((17758196857007342973729812705 : ℚ))) +
  coefficientTerm 46
    (-((54554327489096876110646225957 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient11Chunk2 : Coefficient :=
  coefficientTerm 45
    (302437983490671753385184821371 : ℚ) +
  coefficientTerm 44
    (-((685895459307604576882206051009 : ℚ))) +
  coefficientTerm 43
    (828161925289330459245142155155 : ℚ) +
  coefficientTerm 42
    (-((179571310825570289595548849861 : ℚ))) +
  coefficientTerm 41
    (-((1342443172019594485003284216166 : ℚ))) +
  coefficientTerm 40
    (2908736967472700947779473939527 : ℚ) +
  coefficientTerm 39
    (-((3332981233258937393786420437087 : ℚ))) +
  coefficientTerm 38
    (2251960069131348400398878321759 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient11Chunk3 : Coefficient :=
  coefficientTerm 37
    (-((541558378114969116741493083647 : ℚ))) +
  coefficientTerm 36
    (-((590861925184437658911344674666 : ℚ))) +
  coefficientTerm 35
    (727329422538864912700874332399 : ℚ) +
  coefficientTerm 34
    (-((330038391212224468570747561909 : ℚ))) +
  coefficientTerm 33
    (-((4708880174679046676623779901 : ℚ))) +
  coefficientTerm 32
    (85839734954987045830875172074 : ℚ) +
  coefficientTerm 31
    (-((38818236895982735360473585843 : ℚ))) +
  coefficientTerm 30
    (-((1381055724409934993490254708 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient11Chunk4 : Coefficient :=
  coefficientTerm 29
    (7317346199079732225666281749 : ℚ) +
  coefficientTerm 28
    (-((1949280998940293461981377093 : ℚ))) +
  coefficientTerm 27
    (-((547237018430418985182219033 : ℚ))) +
  coefficientTerm 26
    (366856498987548248591179105 : ℚ) +
  coefficientTerm 25
    (-((3149916729750831115767378 : ℚ))) +
  coefficientTerm 24
    (-((36937416157731067222856412 : ℚ))) +
  coefficientTerm 23
    (4066611184661095168002500 : ℚ) +
  coefficientTerm 22
    (3128738468077742080096935 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient11Chunk5 : Coefficient :=
  coefficientTerm 21
    (-((734321797444887057492544 : ℚ))) +
  coefficientTerm 20
    (-((73159034137894467399843 : ℚ))) +
  coefficientTerm 19
    (-((4152214194238429284492 : ℚ))) +
  coefficientTerm 18
    (27130131491916217762846 : ℚ) +
  coefficientTerm 17
    (-((8795332420449141896867 : ℚ))) +
  coefficientTerm 16
    (1758590106700448121568 : ℚ) +
  coefficientTerm 15
    (-((531503099991703980016 : ℚ))) +
  coefficientTerm 14
    (164697430602016305351 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient11Chunk6 : Coefficient :=
  coefficientTerm 13
    (-((33158678525841141640 : ℚ))) +
  coefficientTerm 12
    (4771570933929000553 : ℚ) +
  coefficientTerm 11
    (-((601209174566723050 : ℚ))) +
  coefficientTerm 10
    (57568281936077638 : ℚ) +
  coefficientTerm 9
    (-((2029518621765831 : ℚ))) +
  coefficientTerm 8
    (-((175796573304906 : ℚ))) +
  coefficientTerm 7
    (17432245435891 : ℚ) +
  coefficientTerm 6
    (-((389846614917 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient11Chunk7 : Coefficient :=
  coefficientTerm 5
    (-((952024095 : ℚ))) +
  coefficientTerm 4
    (35179671 : ℚ) +
  coefficientTerm 3
    (29184 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient11Block0 : Coefficient :=
  quotient0Coefficient11Chunk0 +
  quotient0Coefficient11Chunk1 +
  quotient0Coefficient11Chunk2 +
  quotient0Coefficient11Chunk3 +
  quotient0Coefficient11Chunk4 +
  quotient0Coefficient11Chunk5 +
  quotient0Coefficient11Chunk6 +
  quotient0Coefficient11Chunk7

/-- Internal datum. -/ def quotient0Coefficient11 : Coefficient :=
  quotient0Coefficient11Block0

/-- Internal datum. -/ def quotient0Coefficient12Chunk0 : Coefficient :=
  coefficientTerm 57
    (-((2195661 : ℚ))) +
  coefficientTerm 56
    (-((23819032995 : ℚ))) +
  coefficientTerm 55
    (-((5982336402061 : ℚ))) +
  coefficientTerm 54
    (5723818038264075 : ℚ) +
  coefficientTerm 53
    (2136079834133602541 : ℚ) +
  coefficientTerm 52
    (207100901832871596313 : ℚ) +
  coefficientTerm 51
    (5903915689867743921040 : ℚ) +
  coefficientTerm 50
    (22393953155770363663429 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient12Chunk1 : Coefficient :=
  coefficientTerm 49
    (-((498912581478782964653898 : ℚ))) +
  coefficientTerm 48
    (193949366146945374799120 : ℚ) +
  coefficientTerm 47
    (16722508815383030705983257 : ℚ) +
  coefficientTerm 46
    (-((78977313955832298855715628 : ℚ))) +
  coefficientTerm 45
    (69035198298659723375503458 : ℚ) +
  coefficientTerm 44
    (647335030164768448891309804 : ℚ) +
  coefficientTerm 43
    (-((3048814767086342626257946563 : ℚ))) +
  coefficientTerm 42
    (6431794761693208604977956171 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient12Chunk2 : Coefficient :=
  coefficientTerm 41
    (-((5708350900633672912445104511 : ℚ))) +
  coefficientTerm 40
    (-((6510523920890101324449766392 : ℚ))) +
  coefficientTerm 39
    (30446707512907443182716789972 : ℚ) +
  coefficientTerm 38
    (-((52144861915263337064608844228 : ℚ))) +
  coefficientTerm 37
    (52710584899024607717916105756 : ℚ) +
  coefficientTerm 36
    (-((28411650638467871399243987454 : ℚ))) +
  coefficientTerm 35
    (-((2922173406349606449509352892 : ℚ))) +
  coefficientTerm 34
    (19632027477976652056129835279 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient12Chunk3 : Coefficient :=
  coefficientTerm 33
    (-((16805880525115481474131613661 : ℚ))) +
  coefficientTerm 32
    (5918105862144161760725689210 : ℚ) +
  coefficientTerm 31
    (1173694557055770596902500192 : ℚ) +
  coefficientTerm 30
    (-((2144888019852345729465571418 : ℚ))) +
  coefficientTerm 29
    (729982818161151758397027320 : ℚ) +
  coefficientTerm 28
    (135182681049642116496660342 : ℚ) +
  coefficientTerm 27
    (-((173202672694677965743090129 : ℚ))) +
  coefficientTerm 26
    (27853378694708192345507643 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient12Chunk4 : Coefficient :=
  coefficientTerm 25
    (17615978420859251959727711 : ℚ) +
  coefficientTerm 24
    (-((6838496459328204680276644 : ℚ))) +
  coefficientTerm 23
    (-((1026164040505858361139391 : ℚ))) +
  coefficientTerm 22
    (913279725754464392309502 : ℚ) +
  coefficientTerm 21
    (-((45930594736129827946168 : ℚ))) +
  coefficientTerm 20
    (-((42339624174831762771856 : ℚ))) +
  coefficientTerm 19
    (-((11747048898166696798807 : ℚ))) +
  coefficientTerm 18
    (11936273872571427223595 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient12Chunk5 : Coefficient :=
  coefficientTerm 17
    (-((3182350477080941759504 : ℚ))) +
  coefficientTerm 16
    (723038324939802329945 : ℚ) +
  coefficientTerm 15
    (-((280265574469013623348 : ℚ))) +
  coefficientTerm 14
    (88148301202540786604 : ℚ) +
  coefficientTerm 13
    (-((16780801773197532553 : ℚ))) +
  coefficientTerm 12
    (2207859591198407728 : ℚ) +
  coefficientTerm 11
    (-((234606351515453054 : ℚ))) +
  coefficientTerm 10
    (8152253468501147 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient12Chunk6 : Coefficient :=
  coefficientTerm 9
    (3453307670997838 : ℚ) +
  coefficientTerm 8
    (-((612337394727900 : ℚ))) +
  coefficientTerm 7
    (37008544581738 : ℚ) +
  coefficientTerm 6
    (-((601163583791 : ℚ))) +
  coefficientTerm 5
    (-((10888372082 : ℚ))) +
  coefficientTerm 4
    (165360207 : ℚ) +
  coefficientTerm 3
    (321644 : ℚ) +
  coefficientTerm 2
    (8 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient12Block0 : Coefficient :=
  quotient0Coefficient12Chunk0 +
  quotient0Coefficient12Chunk1 +
  quotient0Coefficient12Chunk2 +
  quotient0Coefficient12Chunk3 +
  quotient0Coefficient12Chunk4 +
  quotient0Coefficient12Chunk5 +
  quotient0Coefficient12Chunk6

/-- Internal datum. -/ def quotient0Coefficient12 : Coefficient :=
  quotient0Coefficient12Block0

/-- Internal datum. -/ def quotient0Coefficient13Chunk0 : Coefficient :=
  coefficientTerm 54
    (-((1 : ℚ))) +
  coefficientTerm 53
    (-((7183616 : ℚ))) +
  coefficientTerm 52
    (-((25816174882 : ℚ))) +
  coefficientTerm 51
    (1266319898877 : ℚ) +
  coefficientTerm 50
    (5496041714943423 : ℚ) +
  coefficientTerm 49
    (1181246870316346355 : ℚ) +
  coefficientTerm 48
    (68226041612259065923 : ℚ) +
  coefficientTerm 47
    (953082616966753097393 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient13Chunk1 : Coefficient :=
  coefficientTerm 46
    (-((4197182608729005384075 : ℚ))) +
  coefficientTerm 45
    (-((52454501614462912548260 : ℚ))) +
  coefficientTerm 44
    (365253777519690492553794 : ℚ) +
  coefficientTerm 43
    (-((247020501088064396536160 : ℚ))) +
  coefficientTerm 42
    (-((5296226300798979023010995 : ℚ))) +
  coefficientTerm 41
    (24907826940587632113840748 : ℚ) +
  coefficientTerm 40
    (-((48941835025219456959169808 : ℚ))) +
  coefficientTerm 39
    (13626789182461782237274215 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient13Chunk2 : Coefficient :=
  coefficientTerm 38
    (176514448340067182606276648 : ℚ) +
  coefficientTerm 37
    (-((514689141995584885481386140 : ℚ))) +
  coefficientTerm 36
    (780207727724272723341062202 : ℚ) +
  coefficientTerm 35
    (-((682391227051677495040732330 : ℚ))) +
  coefficientTerm 34
    (196465676514597526372074952 : ℚ) +
  coefficientTerm 33
    (334308980647855400910737058 : ℚ) +
  coefficientTerm 32
    (-((533493695216215506772012963 : ℚ))) +
  coefficientTerm 31
    (366362708947199340960316368 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient13Chunk3 : Coefficient :=
  coefficientTerm 30
    (-((97284823240084124980570954 : ℚ))) +
  coefficientTerm 29
    (-((45667996955833237923328941 : ℚ))) +
  coefficientTerm 28
    (49342623283675745136672438 : ℚ) +
  coefficientTerm 27
    (-((12146738828257896475502423 : ℚ))) +
  coefficientTerm 26
    (-((5075730990866577599717193 : ℚ))) +
  coefficientTerm 25
    (3720466432241635370476910 : ℚ) +
  coefficientTerm 24
    (-((176223564818083624258509 : ℚ))) +
  coefficientTerm 23
    (-((490416828071177553105860 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient13Chunk4 : Coefficient :=
  coefficientTerm 22
    (111730526731491397938215 : ℚ) +
  coefficientTerm 21
    (37836801815091152845966 : ℚ) +
  coefficientTerm 20
    (-((13253066017775639194114 : ℚ))) +
  coefficientTerm 19
    (-((4270924420707923676588 : ℚ))) +
  coefficientTerm 18
    (2418003762281191897995 : ℚ) +
  coefficientTerm 17
    (-((251696496946316354350 : ℚ))) +
  coefficientTerm 16
    (26805732057319386232 : ℚ) +
  coefficientTerm 15
    (-((46812441580534401884 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient13Chunk5 : Coefficient :=
  coefficientTerm 14
    (15534931781885497098 : ℚ) +
  coefficientTerm 13
    (-((919928727395120924 : ℚ))) +
  coefficientTerm 12
    (-((500804978105795623 : ℚ))) +
  coefficientTerm 11
    (183138787469464270 : ℚ) +
  coefficientTerm 10
    (-((47152534267370078 : ℚ))) +
  coefficientTerm 9
    (8932264185394535 : ℚ) +
  coefficientTerm 8
    (-((969252259108482 : ℚ))) +
  coefficientTerm 7
    (46142861827888 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient13Chunk6 : Coefficient :=
  coefficientTerm 6
    (-((60666968444 : ℚ))) +
  coefficientTerm 5
    (-((48224409005 : ℚ))) +
  coefficientTerm 4
    (531658416 : ℚ) +
  coefficientTerm 3
    (2474394 : ℚ) +
  coefficientTerm 2
    (289 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient13Block0 : Coefficient :=
  quotient0Coefficient13Chunk0 +
  quotient0Coefficient13Chunk1 +
  quotient0Coefficient13Chunk2 +
  quotient0Coefficient13Chunk3 +
  quotient0Coefficient13Chunk4 +
  quotient0Coefficient13Chunk5 +
  quotient0Coefficient13Chunk6

/-- Internal datum. -/ def quotient0Coefficient13 : Coefficient :=
  quotient0Coefficient13Block0

/-- Internal datum. -/ def quotient0Coefficient14Chunk0 : Coefficient :=
  coefficientTerm 50
    (-((29 : ℚ))) +
  coefficientTerm 49
    (-((17529450 : ℚ))) +
  coefficientTerm 48
    (-((19875370624 : ℚ))) +
  coefficientTerm 47
    (6122084765995 : ℚ) +
  coefficientTerm 46
    (4234742657757298 : ℚ) +
  coefficientTerm 45
    (532041318636900224 : ℚ) +
  coefficientTerm 44
    (16884690418375817282 : ℚ) +
  coefficientTerm 43
    (62729149179243979184 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient14Chunk1 : Coefficient :=
  coefficientTerm 42
    (-((1322685005900862757313 : ℚ))) +
  coefficientTerm 41
    (1585966290632919452147 : ℚ) +
  coefficientTerm 40
    (30807300592378950620746 : ℚ) +
  coefficientTerm 39
    (-((164406189964871924261990 : ℚ))) +
  coefficientTerm 38
    (296472124753248426794689 : ℚ) +
  coefficientTerm 37
    (293895668509813193762172 : ℚ) +
  coefficientTerm 36
    (-((2770555586796077302922225 : ℚ))) +
  coefficientTerm 35
    (6957101651011232791890480 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient14Chunk2 : Coefficient :=
  coefficientTerm 34
    (-((9567500485915753035919861 : ℚ))) +
  coefficientTerm 33
    (6280338981865943351153466 : ℚ) +
  coefficientTerm 32
    (2761290501880773656985353 : ℚ) +
  coefficientTerm 31
    (-((11212791299747064053589077 : ℚ))) +
  coefficientTerm 30
    (12660403349744729256811263 : ℚ) +
  coefficientTerm 29
    (-((7457444928651243872488568 : ℚ))) +
  coefficientTerm 28
    (1370405424760092974995973 : ℚ) +
  coefficientTerm 27
    (1327166964249170885684188 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient14Chunk3 : Coefficient :=
  coefficientTerm 26
    (-((1041808488457915567765942 : ℚ))) +
  coefficientTerm 25
    (153382623225307471110414 : ℚ) +
  coefficientTerm 24
    (151732290004797225150807 : ℚ) +
  coefficientTerm 23
    (-((71264527774678586806690 : ℚ))) +
  coefficientTerm 22
    (-((7760864379530747735771 : ℚ))) +
  coefficientTerm 21
    (12237884818122207878949 : ℚ) +
  coefficientTerm 20
    (-((1115274072453579470188 : ℚ))) +
  coefficientTerm 19
    (-((1184198311556213921062 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient14Chunk4 : Coefficient :=
  coefficientTerm 18
    (131569642072347395502 : ℚ) +
  coefficientTerm 17
    (181362931931618724659 : ℚ) +
  coefficientTerm 16
    (-((68061925206991313698 : ℚ))) +
  coefficientTerm 15
    (12329809035838432487 : ℚ) +
  coefficientTerm 14
    (-((6104169313251203042 : ℚ))) +
  coefficientTerm 13
    (3484266626175980637 : ℚ) +
  coefficientTerm 12
    (-((1162625980602131684 : ℚ))) +
  coefficientTerm 11
    (277652635773537723 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient14Chunk5 : Coefficient :=
  coefficientTerm 10
    (-((56360337997859376 : ℚ))) +
  coefficientTerm 9
    (8800031055668797 : ℚ) +
  coefficientTerm 8
    (-((793732905312639 : ℚ))) +
  coefficientTerm 7
    (19268611394496 : ℚ) +
  coefficientTerm 6
    (2140455126179 : ℚ) +
  coefficientTerm 5
    (-((129839533685 : ℚ))) +
  coefficientTerm 4
    (1026464286 : ℚ) +
  coefficientTerm 3
    (13652670 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient14Chunk6 : Coefficient :=
  coefficientTerm 2
    (4848 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient14Block0 : Coefficient :=
  quotient0Coefficient14Chunk0 +
  quotient0Coefficient14Chunk1 +
  quotient0Coefficient14Chunk2 +
  quotient0Coefficient14Chunk3 +
  quotient0Coefficient14Chunk4 +
  quotient0Coefficient14Chunk5 +
  quotient0Coefficient14Chunk6

/-- Internal datum. -/ def quotient0Coefficient14 : Coefficient :=
  quotient0Coefficient14Block0

/-- Internal datum. -/ def quotient0Coefficient15Chunk0 : Coefficient :=
  coefficientTerm 46
    (-((369 : ℚ))) +
  coefficientTerm 45
    (-((31326696 : ℚ))) +
  coefficientTerm 44
    (-((8472236792 : ℚ))) +
  coefficientTerm 43
    (8005902127425 : ℚ) +
  coefficientTerm 42
    (2664185234670550 : ℚ) +
  coefficientTerm 41
    (187758090658059056 : ℚ) +
  coefficientTerm 40
    (2753285292850099361 : ℚ) +
  coefficientTerm 39
    (-((12193476717412802535 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient15Chunk1 : Coefficient :=
  coefficientTerm 38
    (-((115987666876457304197 : ℚ))) +
  coefficientTerm 37
    (864516622258124753633 : ℚ) +
  coefficientTerm 36
    (-((1461346469622457476706 : ℚ))) +
  coefficientTerm 35
    (-((5118947288385956777219 : ℚ))) +
  coefficientTerm 34
    (31835969115928352402324 : ℚ) +
  coefficientTerm 33
    (-((75741198010308980412817 : ℚ))) +
  coefficientTerm 32
    (90562228100350035459061 : ℚ) +
  coefficientTerm 31
    (-((13679841171756579591568 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient15Chunk2 : Coefficient :=
  coefficientTerm 30
    (-((145822389272030724322735 : ℚ))) +
  coefficientTerm 29
    (274864713349869545706338 : ℚ) +
  coefficientTerm 28
    (-((264837706908010120761999 : ℚ))) +
  coefficientTerm 27
    (137243126284292689864613 : ℚ) +
  coefficientTerm 26
    (-((11714583939587293177099 : ℚ))) +
  coefficientTerm 25
    (-((33765218917768905130434 : ℚ))) +
  coefficientTerm 24
    (19822168730071581464460 : ℚ) +
  coefficientTerm 23
    (-((146551671411373026540 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient15Chunk3 : Coefficient :=
  coefficientTerm 22
    (-((4162937276300030813851 : ℚ))) +
  coefficientTerm 21
    (1211854314230683584247 : ℚ) +
  coefficientTerm 20
    (412760068606584745462 : ℚ) +
  coefficientTerm 19
    (-((236248737509971165337 : ℚ))) +
  coefficientTerm 18
    (-((51955682846694971352 : ℚ))) +
  coefficientTerm 17
    (61422074616111225887 : ℚ) +
  coefficientTerm 16
    (-((17250675116298171694 : ℚ))) +
  coefficientTerm 15
    (4670206276739316303 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient15Chunk4 : Coefficient :=
  coefficientTerm 14
    (-((3279408256597215555 : ℚ))) +
  coefficientTerm 13
    (1699288762948131765 : ℚ) +
  coefficientTerm 12
    (-((542627980242857813 : ℚ))) +
  coefficientTerm 11
    (130018294631351879 : ℚ) +
  coefficientTerm 10
    (-((26110196413296705 : ℚ))) +
  coefficientTerm 9
    (3595466932190777 : ℚ) +
  coefficientTerm 8
    (-((142213261631048 : ℚ))) +
  coefficientTerm 7
    (-((36824439833440 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient15Chunk5 : Coefficient :=
  coefficientTerm 6
    (5347371624212 : ℚ) +
  coefficientTerm 5
    (-((218713454238 : ℚ))) +
  coefficientTerm 4
    (396554331 : ℚ) +
  coefficientTerm 3
    (54377547 : ℚ) +
  coefficientTerm 2
    (49508 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient15Block0 : Coefficient :=
  quotient0Coefficient15Chunk0 +
  quotient0Coefficient15Chunk1 +
  quotient0Coefficient15Chunk2 +
  quotient0Coefficient15Chunk3 +
  quotient0Coefficient15Chunk4 +
  quotient0Coefficient15Chunk5

/-- Internal datum. -/ def quotient0Coefficient15 : Coefficient :=
  quotient0Coefficient15Block0

/-- Internal datum. -/ def quotient0Coefficient16Chunk0 : Coefficient :=
  coefficientTerm 42
    (-((2692 : ℚ))) +
  coefficientTerm 41
    (-((39278988 : ℚ))) +
  coefficientTerm 40
    (2404710232 : ℚ) +
  coefficientTerm 39
    (7520841619003 : ℚ) +
  coefficientTerm 38
    (1340971173832645 : ℚ) +
  coefficientTerm 37
    (48548012663106837 : ℚ) +
  coefficientTerm 36
    (169407898919176831 : ℚ) +
  coefficientTerm 35
    (-((3431399731603605027 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient16Chunk1 : Coefficient :=
  coefficientTerm 34
    (6874443080525448522 : ℚ) +
  coefficientTerm 33
    (44680313807145130899 : ℚ) +
  coefficientTerm 32
    (-((278061791726346144035 : ℚ))) +
  coefficientTerm 31
    (653244458060703634864 : ℚ) +
  coefficientTerm 30
    (-((555530397257446175164 : ℚ))) +
  coefficientTerm 29
    (-((910778688611520751165 : ℚ))) +
  coefficientTerm 28
    (3557879390885953743390 : ℚ) +
  coefficientTerm 27
    (-((5461853209957969805167 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient16Chunk2 : Coefficient :=
  coefficientTerm 26
    (4787027289994418917741 : ℚ) +
  coefficientTerm 25
    (-((2108978052213973796972 : ℚ))) +
  coefficientTerm 24
    (-((213343664718030679929 : ℚ))) +
  coefficientTerm 23
    (811616231716081417813 : ℚ) +
  coefficientTerm 22
    (-((330975152511776654243 : ℚ))) +
  coefficientTerm 21
    (-((81581402651158301707 : ℚ))) +
  coefficientTerm 20
    (107335671817775343086 : ℚ) +
  coefficientTerm 19
    (-((13213170061102186971 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient16Chunk3 : Coefficient :=
  coefficientTerm 18
    (-((18447315457914187695 : ℚ))) +
  coefficientTerm 17
    (7598637519126752932 : ℚ) +
  coefficientTerm 16
    (132301046394753919 : ℚ) +
  coefficientTerm 15
    (-((200073608218166492 : ℚ))) +
  coefficientTerm 14
    (-((421485462501412192 : ℚ))) +
  coefficientTerm 13
    (270700497017903959 : ℚ) +
  coefficientTerm 12
    (-((74304343031232550 : ℚ))) +
  coefficientTerm 11
    (12781126177031031 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient16Chunk4 : Coefficient :=
  coefficientTerm 10
    (-((1060954593347493 : ℚ))) +
  coefficientTerm 9
    (-((632456229765455 : ℚ))) +
  coefficientTerm 8
    (341906053991402 : ℚ) +
  coefficientTerm 7
    (-((70455092474928 : ℚ))) +
  coefficientTerm 6
    (6514289472683 : ℚ) +
  coefficientTerm 5
    (-((195189060384 : ℚ))) +
  coefficientTerm 4
    (-((4083349076 : ℚ))) +
  coefficientTerm 3
    (154051674 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient16Chunk5 : Coefficient :=
  coefficientTerm 2
    (338857 : ℚ) +
  coefficientTerm 1
    (5 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient16Block0 : Coefficient :=
  quotient0Coefficient16Chunk0 +
  quotient0Coefficient16Chunk1 +
  quotient0Coefficient16Chunk2 +
  quotient0Coefficient16Chunk3 +
  quotient0Coefficient16Chunk4 +
  quotient0Coefficient16Chunk5

/-- Internal datum. -/ def quotient0Coefficient16 : Coefficient :=
  quotient0Coefficient16Block0

/-- Internal datum. -/ def quotient0Coefficient17Chunk0 : Coefficient :=
  coefficientTerm 38
    (-((12310 : ℚ))) +
  coefficientTerm 37
    (-((31264329 : ℚ))) +
  coefficientTerm 36
    (8865036292 : ℚ) +
  coefficientTerm 35
    (5607598469329 : ℚ) +
  coefficientTerm 34
    (516379910379024 : ℚ) +
  coefficientTerm 33
    (7953793729359004 : ℚ) +
  coefficientTerm 32
    (-((36138656636678554 : ℚ))) +
  coefficientTerm 31
    (-((225513213789617737 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient17Chunk1 : Coefficient :=
  coefficientTerm 30
    (1824761305246903941 : ℚ) +
  coefficientTerm 29
    (-((4372663816136499476 : ℚ))) +
  coefficientTerm 28
    (392072848245272984 : ℚ) +
  coefficientTerm 27
    (22680290200486100227 : ℚ) +
  coefficientTerm 26
    (-((62593199044284473794 : ℚ))) +
  coefficientTerm 25
    (88746704450309202441 : ℚ) +
  coefficientTerm 24
    (-((70637050212978992123 : ℚ))) +
  coefficientTerm 23
    (20521717079671044262 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient17Chunk2 : Coefficient :=
  coefficientTerm 22
    (17119513875229255863 : ℚ) +
  coefficientTerm 21
    (-((19647359409425721107 : ℚ))) +
  coefficientTerm 20
    (4709903453166896873 : ℚ) +
  coefficientTerm 19
    (3874928448449139941 : ℚ) +
  coefficientTerm 18
    (-((2783215273643003581 : ℚ))) +
  coefficientTerm 17
    (31887419613840808 : ℚ) +
  coefficientTerm 16
    (567666479386638645 : ℚ) +
  coefficientTerm 15
    (-((183233617458378572 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient17Chunk3 : Coefficient :=
  coefficientTerm 14
    (-((6079915546131253 : ℚ))) +
  coefficientTerm 13
    (-((1631749094246472 : ℚ))) +
  coefficientTerm 12
    (14488456297797784 : ℚ) +
  coefficientTerm 11
    (-((8889647249145223 : ℚ))) +
  coefficientTerm 10
    (3491820891816609 : ℚ) +
  coefficientTerm 9
    (-((1196156295080997 : ℚ))) +
  coefficientTerm 8
    (316107509831471 : ℚ) +
  coefficientTerm 7
    (-((50735319849219 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient17Chunk4 : Coefficient :=
  coefficientTerm 6
    (3713918130463 : ℚ) +
  coefficientTerm 5
    (12309533905 : ℚ) +
  coefficientTerm 4
    (-((13242386622 : ℚ))) +
  coefficientTerm 3
    (295213445 : ℚ) +
  coefficientTerm 2
    (1617921 : ℚ) +
  coefficientTerm 1
    (137 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient17Block0 : Coefficient :=
  quotient0Coefficient17Chunk0 +
  quotient0Coefficient17Chunk1 +
  quotient0Coefficient17Chunk2 +
  quotient0Coefficient17Chunk3 +
  quotient0Coefficient17Chunk4

/-- Internal datum. -/ def quotient0Coefficient17 : Coefficient :=
  quotient0Coefficient17Block0

/-- Internal datum. -/ def quotient0Coefficient18Chunk0 : Coefficient :=
  coefficientTerm 34
    (-((35975 : ℚ))) +
  coefficientTerm 33
    (-((10894675 : ℚ))) +
  coefficientTerm 32
    (11093619068 : ℚ) +
  coefficientTerm 31
    (3276544082389 : ℚ) +
  coefficientTerm 30
    (140769663319819 : ℚ) +
  coefficientTerm 29
    (430385450367064 : ℚ) +
  coefficientTerm 28
    (-((8538267635462022 : ℚ))) +
  coefficientTerm 27
    (23149085084243428 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient18Chunk1 : Coefficient :=
  coefficientTerm 26
    (32823577603344808 : ℚ) +
  coefficientTerm 25
    (-((323533225580555436 : ℚ))) +
  coefficientTerm 24
    (840611011714563246 : ℚ) +
  coefficientTerm 23
    (-((1136457686245987456 : ℚ))) +
  coefficientTerm 22
    (723361770095726600 : ℚ) +
  coefficientTerm 21
    (157097663952741256 : ℚ) +
  coefficientTerm 20
    (-((682358115190365379 : ℚ))) +
  coefficientTerm 19
    (497025196539271613 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient18Chunk2 : Coefficient :=
  coefficientTerm 18
    (-((58250729807311673 : ℚ))) +
  coefficientTerm 17
    (-((132886504655562603 : ℚ))) +
  coefficientTerm 16
    (79296350292662771 : ℚ) +
  coefficientTerm 15
    (-((5693283596119050 : ℚ))) +
  coefficientTerm 14
    (-((6655656700049085 : ℚ))) +
  coefficientTerm 13
    (-((2405627301517344 : ℚ))) +
  coefficientTerm 12
    (4701839614739282 : ℚ) +
  coefficientTerm 11
    (-((2641217914971899 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient18Chunk3 : Coefficient :=
  coefficientTerm 10
    (1078410176930895 : ℚ) +
  coefficientTerm 9
    (-((385469807864841 : ℚ))) +
  coefficientTerm 8
    (99118998741475 : ℚ) +
  coefficientTerm 7
    (-((12683901637704 : ℚ))) +
  coefficientTerm 6
    (-((220477854863 : ℚ))) +
  coefficientTerm 5
    (242203483626 : ℚ) +
  coefficientTerm 4
    (-((20534079655 : ℚ))) +
  coefficientTerm 3
    (326977378 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient18Chunk4 : Coefficient :=
  coefficientTerm 2
    (5453316 : ℚ) +
  coefficientTerm 1
    (1626 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient18Block0 : Coefficient :=
  quotient0Coefficient18Chunk0 +
  quotient0Coefficient18Chunk1 +
  quotient0Coefficient18Chunk2 +
  quotient0Coefficient18Chunk3 +
  quotient0Coefficient18Chunk4

/-- Internal datum. -/ def quotient0Coefficient18 : Coefficient :=
  quotient0Coefficient18Block0

/-- Internal datum. -/ def quotient0Coefficient19Chunk0 : Coefficient :=
  coefficientTerm 30
    (-((64421 : ℚ))) +
  coefficientTerm 29
    (5752957 : ℚ) +
  coefficientTerm 28
    (10404001505 : ℚ) +
  coefficientTerm 27
    (1418578547115 : ℚ) +
  coefficientTerm 26
    (22961688914080 : ℚ) +
  coefficientTerm 25
    (-((108404179124269 : ℚ))) +
  coefficientTerm 24
    (-((326582177215712 : ℚ))) +
  coefficientTerm 23
    (3105863898373986 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient19Chunk1 : Coefficient :=
  coefficientTerm 22
    (-((8484101667678119 : ℚ))) +
  coefficientTerm 21
    (10391810976466491 : ℚ) +
  coefficientTerm 20
    (-((1236616416849823 : ℚ))) +
  coefficientTerm 19
    (-((14429931249128136 : ℚ))) +
  coefficientTerm 18
    (21145816085642283 : ℚ) +
  coefficientTerm 17
    (-((13027854697744441 : ℚ))) +
  coefficientTerm 16
    (1206312964593841 : ℚ) +
  coefficientTerm 15
    (3318562917322478 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient19Chunk2 : Coefficient :=
  coefficientTerm 14
    (-((1736661492509241 : ℚ))) +
  coefficientTerm 13
    (-((106852538089476 : ℚ))) +
  coefficientTerm 12
    (390703096708610 : ℚ) +
  coefficientTerm 11
    (-((163806132869799 : ℚ))) +
  coefficientTerm 10
    (54071978841562 : ℚ) +
  coefficientTerm 9
    (-((19727865628424 : ℚ))) +
  coefficientTerm 8
    (731194860249 : ℚ) +
  coefficientTerm 7
    (3559636132488 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient19Chunk3 : Coefficient :=
  coefficientTerm 6
    (-((1525594366595 : ℚ))) +
  coefficientTerm 5
    (256923753128 : ℚ) +
  coefficientTerm 4
    (-((16402506995 : ℚ))) +
  coefficientTerm 3
    (51028168 : ℚ) +
  coefficientTerm 2
    (12825394 : ℚ) +
  coefficientTerm 1
    (11116 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient19Block0 : Coefficient :=
  quotient0Coefficient19Chunk0 +
  quotient0Coefficient19Chunk1 +
  quotient0Coefficient19Chunk2 +
  quotient0Coefficient19Chunk3

/-- Internal datum. -/ def quotient0Coefficient19 : Coefficient :=
  quotient0Coefficient19Block0

/-- Internal datum. -/ def quotient0Coefficient20Chunk0 : Coefficient :=
  coefficientTerm 27
    (-((1 : ℚ))) +
  coefficientTerm 26
    (-((59461 : ℚ))) +
  coefficientTerm 25
    (12324255 : ℚ) +
  coefficientTerm 24
    (7567949262 : ℚ) +
  coefficientTerm 23
    (413727350705 : ℚ) +
  coefficientTerm 22
    (962883719324 : ℚ) +
  coefficientTerm 21
    (-((19482816501492 : ℚ))) +
  coefficientTerm 20
    (61774352853746 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient20Chunk1 : Coefficient :=
  coefficientTerm 19
    (-((50329163617114 : ℚ))) +
  coefficientTerm 18
    (-((137374724091247 : ℚ))) +
  coefficientTerm 17
    (430703302378126 : ℚ) +
  coefficientTerm 16
    (-((535570955482756 : ℚ))) +
  coefficientTerm 15
    (328036535322921 : ℚ) +
  coefficientTerm 14
    (-((48177565481359 : ℚ))) +
  coefficientTerm 13
    (-((59954282019238 : ℚ))) +
  coefficientTerm 12
    (29129781550225 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient20Chunk2 : Coefficient :=
  coefficientTerm 11
    (6713175810924 : ℚ) +
  coefficientTerm 10
    (-((11122916321228 : ℚ))) +
  coefficientTerm 9
    (7254726298252 : ℚ) +
  coefficientTerm 8
    (-((4824800994325 : ℚ))) +
  coefficientTerm 7
    (2474094821655 : ℚ) +
  coefficientTerm 6
    (-((732900400191 : ℚ))) +
  coefficientTerm 5
    (104052243523 : ℚ) +
  coefficientTerm 4
    (-((3693477677 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient20Chunk3 : Coefficient :=
  coefficientTerm 3
    (-((414312942 : ℚ))) +
  coefficientTerm 2
    (20087309 : ℚ) +
  coefficientTerm 1
    (48806 : ℚ) +
  coefficientTerm 0
    (-((1 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient20Block0 : Coefficient :=
  quotient0Coefficient20Chunk0 +
  quotient0Coefficient20Chunk1 +
  quotient0Coefficient20Chunk2 +
  quotient0Coefficient20Chunk3

/-- Internal datum. -/ def quotient0Coefficient20 : Coefficient :=
  quotient0Coefficient20Block0

/-- Internal datum. -/ def quotient0Coefficient21Chunk0 : Coefficient :=
  coefficientTerm 23
    (-((15 : ℚ))) +
  coefficientTerm 22
    (-((8092 : ℚ))) +
  coefficientTerm 21
    (15797934 : ℚ) +
  coefficientTerm 20
    (3926971132 : ℚ) +
  coefficientTerm 19
    (66063854900 : ℚ) +
  coefficientTerm 18
    (-((322974843589 : ℚ))) +
  coefficientTerm 17
    (-((83076725911 : ℚ))) +
  coefficientTerm 16
    (3190137344449 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient21Chunk1 : Coefficient :=
  coefficientTerm 15
    (-((8479457071746 : ℚ))) +
  coefficientTerm 14
    (10760671653296 : ℚ) +
  coefficientTerm 13
    (-((6953384268387 : ℚ))) +
  coefficientTerm 12
    (1362201681311 : ℚ) +
  coefficientTerm 11
    (1016907368302 : ℚ) +
  coefficientTerm 10
    (-((826595071238 : ℚ))) +
  coefficientTerm 9
    (565301719652 : ℚ) +
  coefficientTerm 8
    (-((548482783406 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient21Chunk2 : Coefficient :=
  coefficientTerm 7
    (335294671523 : ℚ) +
  coefficientTerm 6
    (-((91983170987 : ℚ))) +
  coefficientTerm 5
    (2278554341 : ℚ) +
  coefficientTerm 4
    (3713544789 : ℚ) +
  coefficientTerm 3
    (-((577725900 : ℚ))) +
  coefficientTerm 2
    (18364436 : ℚ) +
  coefficientTerm 1
    (143236 : ℚ) +
  coefficientTerm 0
    (-((15 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient21Block0 : Coefficient :=
  quotient0Coefficient21Chunk0 +
  quotient0Coefficient21Chunk1 +
  quotient0Coefficient21Chunk2

/-- Internal datum. -/ def quotient0Coefficient21 : Coefficient :=
  quotient0Coefficient21Block0

/-- Internal datum. -/ def quotient0Coefficient22Chunk0 : Coefficient :=
  coefficientTerm 19
    (-((82 : ℚ))) +
  coefficientTerm 18
    (13361 : ℚ) +
  coefficientTerm 17
    (16021238 : ℚ) +
  coefficientTerm 16
    (1261724832 : ℚ) +
  coefficientTerm 15
    (1475077136 : ℚ) +
  coefficientTerm 14
    (-((36407863262 : ℚ))) +
  coefficientTerm 13
    (112498435337 : ℚ) +
  coefficientTerm 12
    (-((155199725195 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient22Chunk1 : Coefficient :=
  coefficientTerm 11
    (100151151507 : ℚ) +
  coefficientTerm 10
    (-((17782585682 : ℚ))) +
  coefficientTerm 9
    (-((3689752379 : ℚ))) +
  coefficientTerm 8
    (-((7310974827 : ℚ))) +
  coefficientTerm 7
    (1016865576 : ℚ) +
  coefficientTerm 6
    (9900732767 : ℚ) +
  coefficientTerm 5
    (-((8189798136 : ℚ))) +
  coefficientTerm 4
    (2549608631 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient22Chunk2 : Coefficient :=
  coefficientTerm 3
    (-((294506047 : ℚ))) +
  coefficientTerm 2
    (5298778 : ℚ) +
  coefficientTerm 1
    (276611 : ℚ) +
  coefficientTerm 0
    (-((82 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient22Block0 : Coefficient :=
  quotient0Coefficient22Chunk0 +
  quotient0Coefficient22Chunk1 +
  quotient0Coefficient22Chunk2

/-- Internal datum. -/ def quotient0Coefficient22 : Coefficient :=
  quotient0Coefficient22Block0

/-- Internal datum. -/ def quotient0Coefficient23Chunk0 : Coefficient :=
  coefficientTerm 15
    (-((174 : ℚ))) +
  coefficientTerm 14
    (-((32381 : ℚ))) +
  coefficientTerm 13
    (9713996 : ℚ) +
  coefficientTerm 12
    (187613781 : ℚ) +
  coefficientTerm 11
    (-((879728127 : ℚ))) +
  coefficientTerm 10
    (1243219873 : ℚ) +
  coefficientTerm 9
    (-((314121207 : ℚ))) +
  coefficientTerm 8
    (-((454855379 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient23Chunk1 : Coefficient :=
  coefficientTerm 7
    (-((481845806 : ℚ))) +
  coefficientTerm 6
    (1585480914 : ℚ) +
  coefficientTerm 5
    (-((1259449216 : ℚ))) +
  coefficientTerm 4
    (393587100 : ℚ) +
  coefficientTerm 3
    (-((24344810 : ℚ))) +
  coefficientTerm 2
    (-((5558926 : ℚ))) +
  coefficientTerm 1
    (320710 : ℚ) +
  coefficientTerm 0
    (-((174 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient23Block0 : Coefficient :=
  quotient0Coefficient23Chunk0 +
  quotient0Coefficient23Chunk1

/-- Internal datum. -/ def quotient0Coefficient23 : Coefficient :=
  quotient0Coefficient23Block0

/-- Internal datum. -/ def quotient0Coefficient24Chunk0 : Coefficient :=
  coefficientTerm 11
    (21 : ℚ) +
  coefficientTerm 10
    (-((25578 : ℚ))) +
  coefficientTerm 9
    (3307990 : ℚ) +
  coefficientTerm 8
    (-((1833545 : ℚ))) +
  coefficientTerm 7
    (-((24370997 : ℚ))) +
  coefficientTerm 6
    (49000504 : ℚ) +
  coefficientTerm 5
    (-((24941700 : ℚ))) +
  coefficientTerm 4
    (-((14379666 : ℚ)))

/-- Internal datum. -/ def quotient0Coefficient24Chunk1 : Coefficient :=
  coefficientTerm 3
    (17501554 : ℚ) +
  coefficientTerm 2
    (-((4426317 : ℚ))) +
  coefficientTerm 1
    (167692 : ℚ) +
  coefficientTerm 0
    (21 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient24Block0 : Coefficient :=
  quotient0Coefficient24Chunk0 +
  quotient0Coefficient24Chunk1

/-- Internal datum. -/ def quotient0Coefficient24 : Coefficient :=
  quotient0Coefficient24Block0

/-- Internal datum. -/ def quotient0Coefficient25Chunk0 : Coefficient :=
  coefficientTerm 7
    (581 : ℚ) +
  coefficientTerm 6
    (38374 : ℚ) +
  coefficientTerm 5
    (508963 : ℚ) +
  coefficientTerm 4
    (-((1764658 : ℚ))) +
  coefficientTerm 3
    (1859389 : ℚ) +
  coefficientTerm 2
    (-((629839 : ℚ))) +
  coefficientTerm 1
    (-((13972 : ℚ))) +
  coefficientTerm 0
    (581 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient25Block0 : Coefficient :=
  quotient0Coefficient25Chunk0

/-- Internal datum. -/ def quotient0Coefficient25 : Coefficient :=
  quotient0Coefficient25Block0

/-- Internal datum. -/ def quotient0Coefficient26Chunk0 : Coefficient :=
  coefficientTerm 3
    (581 : ℚ) +
  coefficientTerm 2
    (25592 : ℚ) +
  coefficientTerm 1
    (-((27335 : ℚ))) +
  coefficientTerm 0
    (581 : ℚ)

/-- Internal datum. -/ def quotient0Coefficient26Block0 : Coefficient :=
  quotient0Coefficient26Chunk0

/-- Internal datum. -/ def quotient0Coefficient26 : Coefficient :=
  quotient0Coefficient26Block0

/-- Internal datum. -/ def quotient0 : Bivariate :=
  outerTerm 0 quotient0Coefficient0 +
  outerTerm 1 quotient0Coefficient1 +
  outerTerm 2 quotient0Coefficient2 +
  outerTerm 3 quotient0Coefficient3 +
  outerTerm 4 quotient0Coefficient4 +
  outerTerm 5 quotient0Coefficient5 +
  outerTerm 6 quotient0Coefficient6 +
  outerTerm 7 quotient0Coefficient7 +
  outerTerm 8 quotient0Coefficient8 +
  outerTerm 9 quotient0Coefficient9 +
  outerTerm 10 quotient0Coefficient10 +
  outerTerm 11 quotient0Coefficient11 +
  outerTerm 12 quotient0Coefficient12 +
  outerTerm 13 quotient0Coefficient13 +
  outerTerm 14 quotient0Coefficient14 +
  outerTerm 15 quotient0Coefficient15 +
  outerTerm 16 quotient0Coefficient16 +
  outerTerm 17 quotient0Coefficient17 +
  outerTerm 18 quotient0Coefficient18 +
  outerTerm 19 quotient0Coefficient19 +
  outerTerm 20 quotient0Coefficient20 +
  outerTerm 21 quotient0Coefficient21 +
  outerTerm 22 quotient0Coefficient22 +
  outerTerm 23 quotient0Coefficient23 +
  outerTerm 24 quotient0Coefficient24 +
  outerTerm 25 quotient0Coefficient25 +
  outerTerm 26 quotient0Coefficient26

/-- Internal datum. -/ def exceptionalUnit0 : Coefficient :=
  C
    (1 : ℚ)

/-- Internal datum. -/ def exceptional0 : Coefficient :=
  exceptionalUnit0 *
  (parameter - 1) ^ 6 *
  (parameter) ^ 7

/-- Internal datum. -/ def recurrence0 : Prop :=
  C ((remainder1.coeff 7) ^ 27) * remainder0 =
    remainder1 * quotient0 + C exceptional0 * remainder2

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end
end

end


