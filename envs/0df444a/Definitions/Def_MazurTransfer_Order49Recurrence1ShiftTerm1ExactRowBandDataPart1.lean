-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm1ExactRowBandDataPart1
-- name    : MazurTransfer_Order49Recurrence1ShiftTerm1ExactRowBandDataPart1
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:38:24.909011+00:00
-- url     : https://prove2.me/theorems/0067d814-9019-421f-8bde-a4192ac18299
-- title:
--   Exact first-recurrence ShiftTerm1 data: part 1
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



































/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-122739733042983787952) * X ^ 2 +
    (-2696048136976233952811844) * X ^ 3 +
    (-61270717707304490134604796) * X ^ 4 +
    (815676262451320632196967121856) * X ^ 5 +
    (-135039205563966226445224180736242) * X ^ 6 +
    (1659178981694951653198741379060559) * X ^ 7 +
    (638175052510476295303198253384711477) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-15098197779856900946873492240864266860) +
    (-1120940882642761558960142150007846902740) * X ^ 1 +
    (14985109838430735998435045050623760635849) * X ^ 2 +
    (1221485274402652169868514294714763213998274) * X ^ 3 +
    (57304094532887089822026342312254539918681) * X ^ 4 +
    (-687367409617728725045087314937397373406684108) * X ^ 5 +
    (-6918005717054536600333811489722439230895112396) * X ^ 6 +
    (185515274713167854525104188150938615528271547810) * X ^ 7 +
    (3715545010341273866204916329764781945673545701355) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-16937581513195251187825394410781196935299729829958) +
    (-937116437673910492245122069063652935965900135653637) * X ^ 1 +
    (-3190380420660714553345497517679803968332215621979192) * X ^ 2 +
    (134476378377744412090096084024445787966109006865865061) * X ^ 3 +
    (1227884166663735100808699911433133547279508088289582795) * X ^ 4 +
    (-10929794062332905536915072953771481177766661804755393401) * X ^ 5 +
    (-189639857235308505681047581738419783133845846684680902731) * X ^ 6 +
    (333238810589168534724018060577287324424432160689599907351) * X ^ 7 +
    (18253090097377802964278838549354637202394905511143201276500) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (29131779420475524565556435292402259815313898688304206009591) +
    (-1238841461780376972460417678718321965085056102399082401730307) * X ^ 1 +
    (-4705450204999605453198843767130146895884590088952547056702639) * X ^ 2 +
    (65754925906664456040205999455309387046266637759626773079858298) * X ^ 3 +
    (334107027458267487023123653536053799954366066618404516635306884) * X ^ 4 +
    (-2761902930907302609214497754441813971221279286013419126204071388) * X ^ 5 +
    (-17461978680999366236496996088360680869643888153733440480374022889) * X ^ 6 +
    (107614888550553836847280574155896455699674961452896399388660112259) * X ^ 7 +
    (655634137583869478783865989391309931920381015856713711942801687732) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-3664322588757274951308102302628864985298010516729891976251533835805) +
    (-20100745389878765202891406213424246338694979008019470560086783351264) * X ^ 1 +
    (119173373213435123766607361122997491697047985352320618536959920075401) * X ^ 2 +
    (460625822784060412949327840253158866182006463539435482166698412876514) * X ^ 3 +
    (-3411353529306638473829065318467007249313605818339665652712536228544114) * X ^ 4 +
    (-7372230356816554356769624258609007686358268007702209897436849000923338) * X ^ 5 +
    (84157667126397311524285435964895896513907887011661909411615422896311693) * X ^ 6 +
    (39056022935338355394581489571463729346534621858943451633423663979292781) * X ^ 7 +
    (-1680034602211375271329891801562833155343285035720954114409349515755676350) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (1961995007344982235413890194491603323124863110532742052887950264454379407) +
    (25171032096995190551898907980041864270430930097934841703667956731787610589) * X ^ 1 +
    (-76710599713100210397728229883715988777227043478543825802528230460937741204) * X ^ 2 +
    (-231275259994633800254997445475595143004345196059255145004716754849035205913) * X ^ 3 +
    (1541424419528103502164588022793116318186826211624942189681923582548182700976) * X ^ 4 +
    (-126025536574374483084826106958846664339729129566022126240086971195761959926) * X ^ 5 +
    (-18985766757292895059241648324919997054205337852625066215017912356658062543100) * X ^ 6 +
    (43610575977354604257716216147346204413489196944629576028730917108681077502355) * X ^ 7 +
    ((1 * 10 ^ 77 +
      10846339984873299427624312056697854312321480112871707840698303305510707085382)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    -((7 * 10 ^ 77 +
      15174208788998422893645212384981544211645895800636568831811266975011394306755)) +
    ((6 * 10 ^ 77 +
      25532341294715481023375615388397526543841764394374800368330984274465349053387)) * X ^ 1 +
    ((50 * 10 ^ 77 +
      90065844467957021732517359859994048778097000756513911674594658863301006498067)) * X ^ 2 +
    -((181 * 10 ^ 77 +
      52660791592624703828999997783867014216615534437492130508358820346187924155403)) * X ^ 3 +
    ((43 * 10 ^ 77 +
      38680002741874584122398494540699423703123685184875276843895944253016741549429)) * X ^ 4 +
    ((1286 * 10 ^ 77 +
      23651995185480343576687635149703901192987735171031348231331873133180702381057)) * X ^ 5 +
    -((3667 * 10 ^ 77 +
      34747299929318461442161403768479300930542322240747135067302892120995590657616)) * X ^ 6 +
    ((951 * 10 ^ 77 +
      41145323357454686726624901850036241202251932682811021116382358951547060840510)) * X ^ 7 +
    ((20726 * 10 ^ 77 +
      66049128727630531874770110615054930225879405694230514195279279023769848484625)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    -((61167 * 10 ^ 77 +
      74062376722055173226125599709305556605543522036135418788087244221952030570042)) +
    ((50337 * 10 ^ 77 +
      67154715791792250977558923692384743607781852362978328178938485552402477520071)) * X ^ 1 +
    ((177673 * 10 ^ 77 +
      63383148852825015991302550422073376818260098089231961137606090633322176876140)) * X ^ 2 +
    -((719113 * 10 ^ 77 +
      83991361948466037466962864878527865189885719189172273426972962434034603517749)) * X ^ 3 +
    ((1161841 * 10 ^ 77 +
      64077040918789785085702488041017786099717821231446352224469628481060458763889)) * X ^ 4 +
    -((232917 * 10 ^ 77 +
      80864544305412150907154583389659390171369480474667892492550179683477453395254)) * X ^ 5 +
    -((3615073 * 10 ^ 77 +
      45838994528288169689666939150203219568053170619878590324461550455106886776135)) * X ^ 6 +
    ((10199568 * 10 ^ 77 +
      91379539809880261991965690511101927236696357580717924365550149365567948011242)) * X ^ 7 +
    -((15442803 * 10 ^ 77 +
      51138568639877589831272399696944364838619567183901760571284403549079267340458)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    ((11991357 * 10 ^ 77 +
      42830199176561028993444613331229476532444188404048191912167616041009386508875)) +
    ((5606453 * 10 ^ 77 +
      88148346449995660695494016602389956316017436896097608006875059561432418388209)) * X ^ 1 +
    -((34088032 * 10 ^ 77 +
      99511803538004851749554189869036471187552425624483751386754077646359885463450)) * X ^ 2 +
    ((59886427 * 10 ^ 77 +
      09309242203608198664823283332640893636305379041246011657222979394409710055361)) * X ^ 3 +
    -((66920088 * 10 ^ 77 +
      34675261111395365640166730426776007377555572570023102316529617521023026294496)) * X ^ 4 +
    ((48975977 * 10 ^ 77 +
      25790285386207425322094456846625942458511227179580454329623682943097990847403)) * X ^ 5 +
    -((15636626 * 10 ^ 77 +
      37870478616845717547623765303349088540321205542905577371756598211178817754979)) * X ^ 6 +
    -((14617241 * 10 ^ 77 +
      45901268848259011035779403359770129343234681843317854230589590368488728271338)) * X ^ 7 +
    ((28330495 * 10 ^ 77 +
      57901054649582044960592242141624040653263547226763881287178480341908796305038)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((25469681 * 10 ^ 77 +
      23119308312252444390028120841231735139136189033169668404258769277229783114639)) +
    ((15830199 * 10 ^ 77 +
      35969150207954845297287487987771724825218973929102572382084598905138792656588)) * X ^ 1 +
    -((8863653 * 10 ^ 77 +
      17491340261198324676738072633380422227634296527012504448630658640737813263494)) * X ^ 2 +
    ((7107795 * 10 ^ 77 +
      04740042608295022174477573490437374483736113611021433921854235806782285717812)) * X ^ 3 +
    -((7515304 * 10 ^ 77 +
      17870792360957630150291618769870517439728508372409070326243204701448682573889)) * X ^ 4 +
    ((6686445 * 10 ^ 77 +
      16882957931182714861934964911060575317404368375746742682652724144724194067799)) * X ^ 5 +
    -((4034656 * 10 ^ 77 +
      08842965556534407199899543146505418898588263056188177693375024965597857279301)) * X ^ 6 +
    ((1093329 * 10 ^ 77 +
      20054665334354354370908369554547131605448584124551578877762883554510021544280)) * X ^ 7 +
    ((693194 * 10 ^ 77 +
      36060447178969810476482741606932412284799672838745726728515587005868840124230)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((1101419 * 10 ^ 77 +
      19124806924688104427415251452544411788287543928103940494987334608621916313912)) +
    ((756997 * 10 ^ 77 +
      58205951282326169480012347681827397936817420571188090782203891914850967812996)) * X ^ 1 +
    -((314932 * 10 ^ 77 +
      51409830003082068492624543633646555540325091976282888327770370228229797612877)) * X ^ 2 +
    ((59651 * 10 ^ 77 +
      85476516538331080119089764654514031904525437056603803160809532733547622034344)) * X ^ 3 +
    ((20257 * 10 ^ 77 +
      96693858123453515994233718593366791059335213874569200173815489535356206157578)) * X ^ 4 +
    -((21613 * 10 ^ 77 +
      06549923570671607904616091102058700938601657129448387287653338910325102340353)) * X ^ 5 +
    ((8855 * 10 ^ 77 +
      98494356449819236677704985844315190871405347362977551198703105228551504361177)) * X ^ 6 +
    -((1787 * 10 ^ 77 +
      09190853989937801763895466929840344881863876058926249751475908963584600193730)) * X ^ 7 +
    -((90 * 10 ^ 77 +
      12366126423771209781874492227451248414243065786414599217503821753324582707227)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((180 * 10 ^ 77 +
      20469593150263817169522415380304910767940984947396936219279606749976375673536)) +
    -((53 * 10 ^ 77 +
      90171176625245853294007066060392465830514813975344875811518520682772204537823)) * X ^ 1 +
    ((5 * 10 ^ 77 +
      22160165494367255485908079677103465679028893008914130083965326857703593708794)) * X ^ 2 +
    ((1 * 10 ^ 77 +
      27134595289113630751322786657489229669956476866454519746925593256621427023777)) * X ^ 3 +
    (-44833943086736393181542359355103721924572281446021339319139060151423891524785) * X ^ 4 +
    (2508947863936725196418513851592909442454864953541111019717642125571428353787) * X ^ 5 +
    (996625082013637809175026878142641625717815773765574670594186819635294587443) * X ^ 6 +
    (-121713772417936979268162822049168411975620538987471484087806955632239375293) * X ^ 7 +
    (-25275313568276554320124771389842456292971636601786417349610344539335698437) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    (4372766062843287722897618740670723826418373177472945976738156017897483023) +
    (554007121229986889894824236359982003462037567956327901648301419056849301) * X ^ 1 +
    (-115189374898588389972733627003325796071017695556795795786215755499456826) * X ^ 2 +
    (-8291394142473072937320012103445650009393713743202126851462713329130108) * X ^ 3 +
    (1610226561369377231397062365562955954328878664572483927341681310383967) * X ^ 4 +
    (121842406621587026375803390049984960951335848614891056363363458149094) * X ^ 5 +
    (-8854407354673559549743053580091825125434805272068810145079226255278) * X ^ 6 +
    (-1268305642022475131476444942955854091913314719863437419799906210928) * X ^ 7 +
    (-55394508139900592018152955933573724704428024824627937491737291215) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    (-1159054106411711679947885772240580916602531815291891094486504574) +
    (-12303391953115413568055417897841008224130410584320226677800854) * X ^ 1 +
    (-62938003361883971213061178030041056688787885634934534936153) * X ^ 2 +
    (-117700812902494846268132849293585919340657693208544969041) * X ^ 3 +
    (112374058939279337873965338289070010910022446982274745) * X ^ 4 +
    (558622395743406769219860089836057675001358873768642) * X ^ 5 +
    (378452657911766289554817352742751629734765443465) * X ^ 6 +
    (41643446675124801602717070349364948325971389) * X ^ 7 +
    (286602794783659856508304450791329304392) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    (4253066079461239157593236895614)
  )

/-- Internal datum. -/ def recurrence1ShiftTerm1Row1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band1 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band2 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band3 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band4 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band5 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band6 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band7 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band8 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band9 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band10 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band11 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band12 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band13 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band14 +
  MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band15





































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band1
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band10
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band11
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band12
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band13
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band14
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band15
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band2
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band4
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band5
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band6
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band7
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band8
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band9


