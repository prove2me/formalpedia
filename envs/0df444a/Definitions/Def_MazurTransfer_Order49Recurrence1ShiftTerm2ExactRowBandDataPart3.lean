-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart3
-- name    : MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart3
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:47:12.365972+00:00
-- url     : https://prove2.me/theorems/4b589f94-15aa-4a8f-b79d-a224c1339444
-- title:
--   Exact first-recurrence ShiftTerm2 data: part 3
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for ShiftTerm2 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 2 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart2
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

































































































 def recurrence1ShiftTerm2Row3Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (131480365199665614987694827671896628003) * X ^ 2 +
    (-5669026796177636458725244113076479083116494) * X ^ 3 +
    (-136313176831360230214290739391697040287111508) * X ^ 4 +
    (1042643763407465691917280344499580271732789554843) * X ^ 5 +
    (-83662137127857316942584030680363037291821680932851) * X ^ 6 +
    (-3880986105354119667549466428554947261024462944676986) * X ^ 7 +
    (193032473618530961015840980001374432451959955303875613) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (7203340064196207455199624817337438537506489124060997891) +
    (-86900746344644648362297178442221259364732629870512993642) * X ^ 1 +
    (-6259344033813402913636467707822189799208394557557803232802) * X ^ 2 +
    (-19566928777639767633188618247251050989027345644718573591114) * X ^ 3 +
    (2331120783430297739338702949849712825250372261877506106049522) * X ^ 4 +
    (27246394524309903612137773685715024927078407213699746925232048) * X ^ 5 +
    (-472023297292676838449804298859270538920659731722947142664673255) * X ^ 6 +
    (-8152656969684236262284921102489874281300131944988994326943656201) * X ^ 7 +
    (36636860792836828925778721019230673228935947909280303960534594692) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (1581028239023584624961864902863092666811130305643641242035479112014) +
    (-1593799828167956596356104373100250398128726135033538050861839780018) * X ^ 1 +
    (-160956895488911660781422114323784035167678546364536466180253496949431) * X ^ 2 +
    (-450309015330947696772615023898179021928963072003053189416804764524328) * X ^ 3 +
    (15033832249841085919344712548301236835972943124815990200431759963422443) * X ^ 4 +
    (44278557321071889345486270859375166472564834073334238286255010560716253) * X ^ 5 +
    (-894698422261522457334141502525091651235105681547326474596649526848402108) * X ^ 6 +
    (-3976357314991016996697552010134155458921368859645647136651090986545222114) * X ^ 7 +
    (49612861859610748277500488929550160712656236636905676839263961154362572778) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (206978749283989061454008328681746528484353909430458527170766377584109596805) +
    (-2210697202634409957738007003544249063960859400119573460906840228309413221535) * X ^ 1 +
    (-8646880063057217828987548356578574861191406553278832730773557991167424851195) * X ^ 2 +
    (88075707257693337954275707514892622213827569471577745770805024010309514562775) * X ^ 3 +
    ((2 * 10 ^ 77 +
      68113835340304008843696100691253666474168755941648519907568165651379907045004)) * X ^ 4 +
    -((30 * 10 ^ 77 +
      53147245358593690643250209056632964056203008270666964443698263501717177292383)) * X ^ 5 +
    -((59 * 10 ^ 77 +
      68384689676435501991860011881405361582052441373003195378273909024369956318168)) * X ^ 6 +
    ((915 * 10 ^ 77 +
      35358928033876595777888577799355241854802867258598699296438751993221628048404)) * X ^ 7 +
    ((703 * 10 ^ 77 +
      59334486974575944814742482639169872676522591611160500062235720171883655496395)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    -((23324 * 10 ^ 77 +
      05972721227057094781569729115568278564080650881177761694633409133688475087644)) +
    ((10871 * 10 ^ 77 +
      19212884479018208314852172896413418505107664017833706190774333146346545531638)) * X ^ 1 +
    ((488964 * 10 ^ 77 +
      84864730491142820725760093429111046686618449930110854252823098342531782326553)) * X ^ 2 +
    -((867633 * 10 ^ 77 +
      18512518595480765678732385988940989239850564110864794461994713071958369564648)) * X ^ 3 +
    -((8060008 * 10 ^ 77 +
      65156885264001019241965543248896714514379636795950202171646651240311570968310)) * X ^ 4 +
    ((27380619 * 10 ^ 77 +
      51208055332816346796149434934239828173222885975240781136556564164820834313499)) * X ^ 5 +
    ((92849689 * 10 ^ 77 +
      05306053330109059700119498975544802037673856679468897895998639716074245663275)) * X ^ 6 +
    -((582161397 * 10 ^ 77 +
      03090428776830695770161484217130428896216180820889089010732879008572067524881)) * X ^ 7 +
    -((408908235 * 10 ^ 77 +
      72610343443037435216907471417920251945959085866110545927691061652288948993542)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    ((8896921118 * 10 ^ 77 +
      71215016743365815241866652065735527880614510273099938332312466065605182397642)) +
    -((10526272936 * 10 ^ 77 +
      22444210259344546908882538881683828078458919013136150693844837157865235632988)) * X ^ 1 +
    -((92294022065 * 10 ^ 77 +
      05698761034392861447052869069081400143626954101754389945396159220947207753681)) * X ^ 2 +
    ((301218760190 * 10 ^ 77 +
      44957136008634313308829501094672139708693412641997273819820829460906893023709)) * X ^ 3 +
    ((447622376764 * 10 ^ 77 +
      70021862872551966499297287261183068021469989409720097975806254904914527396955)) * X ^ 4 +
    -((4115590999170 * 10 ^ 77 +
      57986791055118409695885970685730772206470354937499854023079896504564130038851)) * X ^ 5 +
    ((4005069271402 * 10 ^ 77 +
      66441970634694972921386949712265881946958004431560233166772498200016450988208)) * X ^ 6 +
    ((30900726856891 * 10 ^ 77 +
      76819854307669762600501443048908307362857988880316400643511039554749365955802)) * X ^ 7 +
    -((103655875906763 * 10 ^ 77 +
      00696931763811088590200539752391590673217778689010635195494769721073251244671)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((34537446086351 * 10 ^ 77 +
      28331857815621597615476882823056835082309854376402045063457687016305342045386)) +
    ((922544294290837 * 10 ^ 77 +
      60338915219994336585304903490783258342514445584738856070501831081502493902700)) * X ^ 1 +
    -((1881911739005342 * 10 ^ 77 +
      67817188910567363798056643836168387971720807898652887973866057881635384300590)) * X ^ 2 +
    -((2247601735474703 * 10 ^ 77 +
      91726676660938656747052521861934274651874745852804260416468150086915694488622)) * X ^ 3 +
    ((18367891300279714 * 10 ^ 77 +
      24311429965110839722959479736461713258055107107980848768740273892484053626734)) * X ^ 4 +
    -((30591808012948054 * 10 ^ 77 +
      13668613203899889088323828834281426701727362106401710408294692544357919720903)) * X ^ 5 +
    -((35643391957567478 * 10 ^ 77 +
      23098228187512315567142933308277662061392413272866748661939674559305423783796)) * X ^ 6 +
    ((265174552613711205 * 10 ^ 77 +
      46854979734728671790834651741397673446116772637670043677439775623238863248128)) * X ^ 7 +
    -((486285565398377656 * 10 ^ 77 +
      88430673910569843522328909515535498626717982970890193944650385432590153692580)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((75172869476143527 * 10 ^ 77 +
      06314114260721265629728721611716637209703099818049019328320237233555231580840)) +
    ((2462110895820231255 * 10 ^ 77 +
      69785015823838710996424600320684687800222335804188693647349359094065600350606)) * X ^ 1 +
    -((6077278447133637954 * 10 ^ 77 +
      73378748200318432200265939987954802053567675595769681865755724286509290187915)) * X ^ 2 +
    ((5979885719941795128 * 10 ^ 77 +
      23298095215331074647666424318775689448881241466276951162029591856668213626580)) * X ^ 3 +
    ((6750318879325126225 * 10 ^ 77 +
      53008025255491928274324760576129882022827123781454641330647186815183977759310)) * X ^ 4 +
    -((37251813567267385734 * 10 ^ 77 +
      69912730788282044624468077662677248343997495676017190447210775385270737989548)) * X ^ 5 +
    ((73972271059476567834 * 10 ^ 77 +
      05021509530835756042903556006843963866177491161346015886671727073162262948852)) * X ^ 6 +
    -((83372949769024174870 * 10 ^ 77 +
      45226395261224146788928887732991094161621804905925547815262027331134133469604)) * X ^ 7 +
    ((26475284660428890976 * 10 ^ 77 +
      20452097258423091127543307937244930583449613551786115884444897733108118299388)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((105911023777699077974 * 10 ^ 77 +
      05573902241335779379440110296180751337966909720322486512579065090794194646832)) +
    -((267333478086346601980 * 10 ^ 77 +
      67342534772292855768670287976974664126622860573368967018161308235719870499993)) * X ^ 1 +
    ((370853666641037262338 * 10 ^ 77 +
      36500660374293132258855992962861905435107228346648442709219017858669054144819)) * X ^ 2 +
    -((344992002242672283825 * 10 ^ 77 +
      41944528862740308078552797346593051780103367829440582018698250695954732844953)) * X ^ 3 +
    ((188722889520179445085 * 10 ^ 77 +
      85722822711870609838085143541761209718649544502270522110239300309608462103152)) * X ^ 4 +
    ((22685048885889745697 * 10 ^ 77 +
      87746437750177905376915935112920264447710015414619518456917477339225178005547)) * X ^ 5 +
    -((188271992482239664652 * 10 ^ 77 +
      48049814216660847805776970009300210326414989318925892595314557193684226108651)) * X ^ 6 +
    ((246468762605634803629 * 10 ^ 77 +
      31535835971533318765591197834545897248273601919426378316311570488993107534350)) * X ^ 7 +
    -((203917249147351651036 * 10 ^ 77 +
      66569900358176263272736937449497813196067974260492886447703766815170242522986)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    ((113928779918402122765 * 10 ^ 77 +
      04176261097873068246129515503950458607728808457337812860565848046083562447990)) +
    -((32213326160374621719 * 10 ^ 77 +
      56555140010192587748276552219656242764748564277308777789337936993067823378902)) * X ^ 1 +
    -((13410739381110840228 * 10 ^ 77 +
      09358590086838312844343177196537607848665006061683775738291279392488464020814)) * X ^ 2 +
    ((24930183851082405582 * 10 ^ 77 +
      20730782976274824609246471306567633551310247927807070250912141462704106399656)) * X ^ 3 +
    -((18419131047419551868 * 10 ^ 77 +
      64125073021138472933582463322258163264163683516296301655046673778445697801584)) * X ^ 4 +
    ((8483841741674026068 * 10 ^ 77 +
      43006900116923200942818943909213318754716482688353360895762703734006980418624)) * X ^ 5 +
    -((1976759688148152825 * 10 ^ 77 +
      03125651174590725422856864988271205065917148225856734938014400147798814531927)) * X ^ 6 +
    -((503797115229887371 * 10 ^ 77 +
      42500469828080292515125125381337790192422748240924799503260347060346280757639)) * X ^ 7 +
    ((756130741646901884 * 10 ^ 77 +
      23971212994877965852049018935645021641570902827731736789806469473830947526295)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    -((385185574833793054 * 10 ^ 77 +
      08837324184354572381261810607464702812493916835036437536821262867565142598823)) +
    ((97719535895572080 * 10 ^ 77 +
      91052997994258273504573192414270466645157503702530924874136074396532930748332)) * X ^ 1 +
    ((6145330960693197 * 10 ^ 77 +
      38211236895936449097589866830746471617376647849664936267324719721345730364900)) * X ^ 2 +
    -((16518902873445112 * 10 ^ 77 +
      54349484569050860157686271646776901113866155346946785649311923762326047120211)) * X ^ 3 +
    ((6717923610993442 * 10 ^ 77 +
      65450052033145335824852615192441855291419415641548821587304411542146954602421)) * X ^ 4 +
    -((931497322010222 * 10 ^ 77 +
      75757950667051508877166493984790597305777817231931089210585240588818702329698)) * X ^ 5 +
    -((318675207674654 * 10 ^ 77 +
      40089911554821346835794497296130133500815642006312728077985026322680079865563)) * X ^ 6 +
    ((188519145061313 * 10 ^ 77 +
      35631338718408883441283084263335282782992702226865744107715927917970118828867)) * X ^ 7 +
    -((31477277117419 * 10 ^ 77 +
      44987666330168986503472482450679509428543671952684704167802169171995396244284)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    -((4580242488309 * 10 ^ 77 +
      19148690426417275389840045355388148904602040797790595773116109103124796731527)) +
    ((2947397329487 * 10 ^ 77 +
      67631516365838793287200651579118361975487273756662345559590775050672989953692)) * X ^ 1 +
    -((356799109087 * 10 ^ 77 +
      67756332858577974757878382942624923927544605080694432103152477992230036999784)) * X ^ 2 +
    -((69537864241 * 10 ^ 77 +
      84940987089179561616397475987469649439183056601188724939879570974011978133192)) * X ^ 3 +
    ((23349633743 * 10 ^ 77 +
      53074579741535093743846585119647680340057031614582551716433667979481287993833)) * X ^ 4 +
    -((475727284 * 10 ^ 77 +
      81904695573689439345293321932545671609443351741462566297592438332924292565048)) * X ^ 5 +
    -((574223332 * 10 ^ 77 +
      14000209808632249949787326221542664462744337756338034495816178260856264036427)) * X ^ 6 +
    ((46341925 * 10 ^ 77 +
      41230069154213322568103506039889423651618899507938909333035319736597080920099)) * X ^ 7 +
    ((8390985 * 10 ^ 77 +
      71364292618146165113904551736786245203696891169208370257525842091538554222850)) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    -((792857 * 10 ^ 77 +
      90666419310374801634666588051594855676212951588226771693226008392544488124990)) +
    -((99218 * 10 ^ 77 +
      90706401094410191517803232564165290591427997005290088433404441338873270873926)) * X ^ 1 +
    ((4182 * 10 ^ 77 +
      95858770825192856775361680305946411584791254894596678014070057967323215971136)) * X ^ 2 +
    ((862 * 10 ^ 77 +
      07953821152230297847256527514331437767467584079121890175278928480387769722260)) * X ^ 3 +
    ((41 * 10 ^ 77 +
      22917362314652930590520974631937551759674184116718022071150114426219972012078)) * X ^ 4 +
    (90590529053261832512934861471665023974335668275328446148766616666769279938877) * X ^ 5 +
    (993129052605987397203044975392564730999940135078882559843421471790101061119) * X ^ 6 +
    (5215385036233081105037606360083997515455489495319580915615371382373045511) * X ^ 7 +
    (10119218645900209576481771495556584262032335137198692883801233436803488) * X ^ 8
  )

 def recurrence1ShiftTerm2Row3Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    (-8656816591153980856685654201280985171018625165633059654099027869647) +
    (-47167614841909829428733068403641445229019739847340136697565672288) * X ^ 1 +
    (-33246960901718974328246269851338639425563473262878349869762645) * X ^ 2 +
    (-3896486385913489348201720326751317675701763857065359444042) * X ^ 3 +
    (-31122463099690895323739612049055804003287199427414960) * X ^ 4 +
    (-989090828273191249048029195560974419171412153) * X ^ 5
  )

 def recurrence1ShiftTerm2Row3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band3 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band4 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band5 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band6 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band7 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band8 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band9 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band10 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band11 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band12 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band13 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band14 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band15 +
  MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band16









































































































































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band10
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band11
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band12
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band13
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band14
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band15
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band16
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band3
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band4
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band5
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band6
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band7
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band8
#print axioms MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Row3Band9


