-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm1ExactRowBandDataPart3
-- name    : MazurTransfer_Order49Recurrence1QuotientTerm1ExactRowBandDataPart3
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:40:04.703979+00:00
-- url     : https://prove2.me/theorems/88316b08-f12f-4312-b181-e0394eccda75
-- title:
--   Exact first-recurrence QuotientTerm1 data: part 3
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for QuotientTerm1 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 1 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0

namespace MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (-535055915795269029619938798283045286409) * X ^ 2 +
    (23066263110449441095230462957262322461703515) * X ^ 3 +
    (713940647672886588265431567120979851390052852) * X ^ 4 +
    (-4237638266421604253916617676735522430192321505168) * X ^ 5 +
    (311224460885416614166788225108888853048739025419719) * X ^ 6 +
    (17860312716633342641496536195379583110116460395168220) * X ^ 7 +
    (-656708194635833564375935487532738480503588233813708100) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-33470755228269476103288984361086004518399787803317567078) +
    (112030199886422966629827559375988834357973185269537954555) * X ^ 1 +
    (25537939312776379836944408661017836294236603297061475485136) * X ^ 2 +
    (254101689897271581571518519571093245111437055781377412112309) * X ^ 3 +
    (-7245949447570074405312565459843354514040710736255216639233357) * X ^ 4 +
    (-153198207467518622643960124748500849874493706392420286229423875) * X ^ 5 +
    (764759999769956816986085462624255522431921967928293126614098070) * X ^ 6 +
    (34880465759864986659187374665260158414546503239077464661346469818) * X ^ 7 +
    (86405767958801341810879015114772127363097964784864721633170245243) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-5170360503727648312616556482016726142172671617128169216761596842085) +
    (-23584378562776180812898086467118121873780400381327565866249942646013) * X ^ 1 +
    (420353817223936667953807262089793737177624936742347100150509895925005) * X ^ 2 +
    (3811260702095361515832241987036031861789887111617654618477784748798486) * X ^ 3 +
    (-31724152196024092453964768943320725491368082784373893159417505032393914) * X ^ 4 +
    (-298325949776023656382113317194485289879436030734733572853917479103648542) * X ^ 5 +
    (1547993818361065197030270370351575377424143017072610313786660101421259704) * X ^ 6 +
    (20014917201478631747868038200457993663247863027109657778657736964115150826) * X ^ 7 +
    (-76144940763308392480054725395364310922522930113225502931497694461134635690) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-987090567057467336064601152340332277683430588681640755332567714469553495005) +
    (3219592075964262850306182338535517054810681305684128299355456967213483433914) * X ^ 1 +
    (40779716003802839995298368083509533936757907928560020473802239132447632541367) * X ^ 2 +
    -((1 * 10 ^ 77 +
      33091301156334674139614588083759502189066014024591921848334481713846582422352)) * X ^ 3 +
    -((13 * 10 ^ 77 +
      82975888003198589660545908080318309608485584042663660232826596652607041515774)) * X ^ 4 +
    ((50 * 10 ^ 77 +
      72052773154416875601370066129761662793296260645990476771344522001787352373939)) * X ^ 5 +
    ((386 * 10 ^ 77 +
      83077415451466288635263968041931678906275690016015970156049057814143445472441)) * X ^ 6 +
    -((1721 * 10 ^ 77 +
      65808690582109008014977614057571620680153505313114626172431166712966186415030)) * X ^ 7 +
    -((8734 * 10 ^ 77 +
      65193352881531500535739399900726888765158093816469656310669682284314975975943)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    ((50588 * 10 ^ 77 +
      53736318708479711999825191470513634793934431629816715762550683674289419097049)) +
    ((148649 * 10 ^ 77 +
      87708100912320975145069252948121525870405415679995365516322937010382299293648)) * X ^ 1 +
    -((1251192 * 10 ^ 77 +
      48659643315396041910276866648630053234147721533151469918501201635514703388191)) * X ^ 2 +
    -((1519571 * 10 ^ 77 +
      80058296246975730554089947869134316491488064174936762403951399715760393831197)) * X ^ 3 +
    ((25538842 * 10 ^ 77 +
      51284057521137217370644176507462839958488893696057910254301852586550873892399)) * X ^ 4 +
    -((6787627 * 10 ^ 77 +
      47783817146755566646466334695841848516820608046756721498604138216536181824382)) * X ^ 5 +
    -((416269036 * 10 ^ 77 +
      06156359857226054171899981694109731534353032179933068068186544194377616039775)) * X ^ 6 +
    ((711102461 * 10 ^ 77 +
      82766613283254632049056194344586456893727509623066805284871037102552224281766)) * X ^ 7 +
    ((5071830642 * 10 ^ 77 +
      99213972487784180208669804716704893552518720523035072793446702962694159643279)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    -((17914852394 * 10 ^ 77 +
      26205739736233560176150086288685331521674486092302533501755861980324683359314)) +
    -((37268194286 * 10 ^ 77 +
      74978619169616338814385383358766352605365058928554442842326409981648545070136)) * X ^ 1 +
    ((285802085582 * 10 ^ 77 +
      83810169951584844501905429872139445978851283342157707830220695106765384173803)) * X ^ 2 +
    -((66589671660 * 10 ^ 77 +
      80352203795882995896460112043421124696930416427030487149505431937173469276925)) * X ^ 3 +
    -((3047308961087 * 10 ^ 77 +
      64267669978950272699165079703205475053171388753063955857388654002205676671204)) * X ^ 4 +
    ((6429495123344 * 10 ^ 77 +
      26575517913168454895090539347549412385309220983733552026469205477078960317126)) * X ^ 5 +
    ((17739705642565 * 10 ^ 77 +
      41869661261274755741994714577542241193281296454073296283395046651466402565301)) * X ^ 6 +
    -((95636525350599 * 10 ^ 77 +
      58995017943709464396656498284009915867279496330782837355094445157190193435051)) * X ^ 7 +
    ((38967586551943 * 10 ^ 77 +
      53353425972735933239969769577919420492052182226229373174754693278672261238389)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    ((717745263263490 * 10 ^ 77 +
      86107434717859494613107364854851942796733337770951471241645643634268470055547)) +
    -((1852522678517609 * 10 ^ 77 +
      03822480789663638412592372425498578903625754267583419545597575412414818669235)) * X ^ 1 +
    -((1261615034118241 * 10 ^ 77 +
      71071127761644627193341001266383582857725200904078304027772634537187599256520)) * X ^ 2 +
    ((15794761370237138 * 10 ^ 77 +
      76306362681597240578612554932926666526932874039184953485298998339766837037882)) * X ^ 3 +
    -((27761435225606986 * 10 ^ 77 +
      36479126469588624774510408807144488884471036590560309989931856423025701905344)) * X ^ 4 +
    -((33071780273105329 * 10 ^ 77 +
      62442105831939466220130161821706747332903366045538006530930226733879427461275)) * X ^ 5 +
    ((237882050421782729 * 10 ^ 77 +
      14203531335310938596584489529596974057844274726157967477114708242561124507004)) * X ^ 6 +
    -((385988008633154446 * 10 ^ 77 +
      35188384821717345935817020592581073888977940098087119357305400217848660532157)) * X ^ 7 +
    -((270674905776132262 * 10 ^ 77 +
      11474437705119689563995741785264140038288395499097652660578365228540703125653)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((2444872674630369083 * 10 ^ 77 +
      51296939737929016429151195370501371785713667780649469322960142693164160779653)) +
    -((4709716000622992176 * 10 ^ 77 +
      37221355116406906394725493770727113273623100592032408902270080789568198658911)) * X ^ 1 +
    ((1623215958526878646 * 10 ^ 77 +
      90199957747952121838444794897886508752981916126480929540966707689051259886526)) * X ^ 2 +
    ((13141942684602551561 * 10 ^ 77 +
      05749876443366789930857239006184681699521051388645423127139608789569467643734)) * X ^ 3 +
    -((36146440547615478062 * 10 ^ 77 +
      83280117712512743358804443777836629962920039811054309548689463501332285072145)) * X ^ 4 +
    ((44370031063415153833 * 10 ^ 77 +
      15778728638480697915944279085554944501766665231246436652692174944162305231843)) * X ^ 5 +
    -((4158623783360779779 * 10 ^ 77 +
      23050415449336712410988895830833827210743394130159620239926900446184396419486)) * X ^ 6 +
    -((94008408264515221181 * 10 ^ 77 +
      34024152470910933871360304341033415371645637139700165994645494116762398533209)) * X ^ 7 +
    ((200805916153261140732 * 10 ^ 77 +
      83714951745103278549448408385826362090466410693736772599019549858221811345929)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((219826857692919841359 * 10 ^ 77 +
      47047016559467165613272814725180673547670076403608063731606926386261195120058)) +
    ((80518914096113080244 * 10 ^ 77 +
      61582373023322914911860357239339655091999610474330987402221948586458061236931)) * X ^ 1 +
    ((181896599021112582713 * 10 ^ 77 +
      23532633295812192775212703534864670615700605380969539656389875626120096790640)) * X ^ 2 +
    -((423743300855418450486 * 10 ^ 77 +
      33237490547064981834128619080091301823372320841719547266882512529548667559754)) * X ^ 3 +
    ((490474174940727590424 * 10 ^ 77 +
      15283880589444358429675940373440308637835470588673058439255753461553385750278)) * X ^ 4 +
    -((336436924609010426293 * 10 ^ 77 +
      61969645875268108175568782159086440825578825185069212070033620361764782114075)) * X ^ 5 +
    ((58771357213972392468 * 10 ^ 77 +
      74044281709020385496914955042700679461670489107436553470140081946311564908970)) * X ^ 6 +
    ((182442165777511058678 * 10 ^ 77 +
      24684267576947581596628392353322952477583061396592570698206689990697263195502)) * X ^ 7 +
    -((280543522258675064273 * 10 ^ 77 +
      16501152916966488157291104158173539277436962718395875517340850266811067911075)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((236839692434384469692 * 10 ^ 77 +
      01025608829104441922565774794843485186942981991710490699514059229571079377841)) +
    -((126691280195162583155 * 10 ^ 77 +
      11677594194126420393719716519533329342395573481881643838302119168079131154949)) * X ^ 1 +
    ((28371873925975210548 * 10 ^ 77 +
      12214579054888386334368900969038833975636731367527900887214594418435330870170)) * X ^ 2 +
    ((22171890249015887173 * 10 ^ 77 +
      39879917112515420835650965183842969564675095362080654161984753713531588979452)) * X ^ 3 +
    -((30742289596984427224 * 10 ^ 77 +
      92619065774457843815669369141016683927192836469354148951763809199126877508385)) * X ^ 4 +
    ((19897024220300591267 * 10 ^ 77 +
      83214623339259644975281404794934670066978206863815758269313571544936636809245)) * X ^ 5 +
    -((7628348665604810845 * 10 ^ 77 +
      61055451734194945312287879281123374309207013735868049739625049443235846158909)) * X ^ 6 +
    ((825527404231989779 * 10 ^ 77 +
      11095879743361866542238571995876241584149705131521634686988727909934963856286)) * X ^ 7 +
    ((1120095138984977916 * 10 ^ 77 +
      56845918406056148857619082480027555326587437372548140556960623113407193767617)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    -((893054768327845198 * 10 ^ 77 +
      73610348480783238330102552501386632138233501926685843546794534432764228417957)) +
    ((333205934493839086 * 10 ^ 77 +
      74814876977440980098331186447062183795280527884217437932136706570857003440449)) * X ^ 1 +
    -((38484866961440227 * 10 ^ 77 +
      85209093807231401116317734814350751376981061325075393782569465558947778854401)) * X ^ 2 +
    -((29279144516353486 * 10 ^ 77 +
      09245148825437806947084596594626045212838449431375219515626322185530452463479)) * X ^ 3 +
    ((18501733691661793 * 10 ^ 77 +
      61614471871714150252783760935171966719764437419954048508246013071599113975688)) * X ^ 4 +
    -((4279559407433237 * 10 ^ 77 +
      74929702981948559965305280561427956275327984059541859208024448497729916891481)) * X ^ 5 +
    -((321468435247907 * 10 ^ 77 +
      18965971680630083799753507922322531693725269995147819516897373193951217942250)) * X ^ 6 +
    ((503350664122199 * 10 ^ 77 +
      46664446281776788315894536006747889217499046317372979603307532773876426080623)) * X ^ 7 +
    -((124332632778523 * 10 ^ 77 +
      28350524961044459035938252757363434615364945305934478779866081436050092826518)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    -((3183743036911 * 10 ^ 77 +
      38316919895111606878349597127486923119431946601169768713886759953619147031879)) +
    ((8488901669144 * 10 ^ 77 +
      83856601796262737424015335056653255695333647544048315718273938889682907354553)) * X ^ 1 +
    -((1519859981889 * 10 ^ 77 +
      92299847654961987779336301312715268235976238334163558570619150892581348667522)) * X ^ 2 +
    -((134972269658 * 10 ^ 77 +
      99557688689274918802354890703613791711730948520732446685078969600762544302855)) * X ^ 3 +
    ((78269514606 * 10 ^ 77 +
      81537496833927720391770123980829926108836804383628498006178619089746651495320)) * X ^ 4 +
    -((4288153859 * 10 ^ 77 +
      88299801566844316414044843274869281573203165074062651704325621763929684240283)) * X ^ 5 +
    -((1775102951 * 10 ^ 77 +
      32982688064020042494685478419131064891194973038417394755737946854835609705452)) * X ^ 6 +
    ((201258082 * 10 ^ 77 +
      45386097645415007775369013313058174101499232141149142079698508842476523400668)) * X ^ 7 +
    ((25438990 * 10 ^ 77 +
      16785402365339801259530104391458536726645771589324705522148906627497733691383)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    -((3261297 * 10 ^ 77 +
      36686580856030558736624738702113719004745503003062257190878811047266729684075)) +
    -((326759 * 10 ^ 77 +
      63063992901146487268512521711388855205367463864174024373019504843558876243503)) * X ^ 1 +
    ((19068 * 10 ^ 77 +
      23286511122734513759772992284833099206240009070485068424919032504322728880591)) * X ^ 2 +
    ((3243 * 10 ^ 77 +
      46629616486268767225143684167956004207483631823941204222925892820661989666068)) * X ^ 3 +
    ((149 * 10 ^ 77 +
      84555345724516311483482132473877160629111570962031854796702124245549107826890)) * X ^ 4 +
    ((3 * 10 ^ 77 +
      24361311008563972315040089835523339093708149075464204496904165082462349326779)) * X ^ 5 +
    (3528291332398363184837506332995215284072466561693909714707691072743450167611) * X ^ 6 +
    (18444861780064636611771014407236457347978266631214008151437489867499288090) * X ^ 7 +
    (35650759893155832405722984980381965028664880441890255546432119840652434) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    (-30763171501336989443450315279745575622372147632484627898402836125906) +
    (-166532218989470746534533323412166737986794817214725010698567750487) * X ^ 1 +
    (-117288657743483677814365436061726303843267826357615127888148673) * X ^ 2 +
    (-13743967025035177823868978070032635972135446602301843045628) * X ^ 3 +
    (-109776191049371519449287963109025260672117427630525451) * X ^ 4 +
    (-3488754043779585229690856105140628626705806626) * X ^ 5
  )

/-- Internal datum. -/ def recurrence1QuotientTerm1Row3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band3 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band4 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band5 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band6 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band7 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band8 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band9 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band10 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band11 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band12 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band13 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band14 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band15 +
  MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band16



































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band10
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band11
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band12
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band13
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band14
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band15
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band16
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band3
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band4
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band5
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band6
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band7
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band8
#print axioms MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row3Band9


