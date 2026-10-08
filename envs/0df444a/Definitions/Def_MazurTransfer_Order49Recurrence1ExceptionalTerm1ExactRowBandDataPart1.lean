-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm1ExactRowBandDataPart1
-- name    : MazurTransfer_Order49Recurrence1ExceptionalTerm1ExactRowBandDataPart1
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:38:32.91959+00:00
-- url     : https://prove2.me/theorems/645859cb-c968-4c3b-88d0-7e4f2e8893d9
-- title:
--   Exact first-recurrence ExceptionalTerm1 data: part 1
-- statement:
--   This part contains original polynomial data for one row, or the final aggregation of rows and bands, in the original arithmetic product identity of the first order-49 pseudo-division recurrence. Its values and public names are unchanged from the independently audited full data package. It supplies the original row and band equality proofs for ExceptionalTerm1 and asserts no polynomial identity itself.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The package is selected by the kernel dependency closure of one original row definition; the final part assembles the remaining original data. Complete original AST declarations and resolved-reference ranges preserve every mathematical command. Private visibility changes only at exact private-token ranges. All original values are independently kernel-compared with the pinned originals, and the combined part bodies receive a fresh audit before publication. No theorem proof or assumed equality is included. Apache-2.0 attribution retained. Named downstream consumers: original row and band product row and band identities, normalized coefficient 1 and full every-curve order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0

namespace MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section









































/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (-13272447653500) * X ^ 2 +
    (-228620881323516780) * X ^ 3 +
    (48551422220846408192) * X ^ 4 +
    (-372411987560353021905596) * X ^ 5 +
    (154006249916739342913895706) * X ^ 6 +
    (-57933810674304010040826333944) * X ^ 7 +
    (11245663048386821053610997104691) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (-1513629073615447190779359469849278) +
    (131631365852497708163730664231104648) * X ^ 1 +
    (-7843799053910196645455812318728093120) * X ^ 2 +
    (310659509825907349145500626480587006293) * X ^ 3 +
    (-8386980451263210440670731139733866694681) * X ^ 4 +
    (180482962812429140648413633949865460781210) * X ^ 5 +
    (-5607555858816762962698217910780768492090508) * X ^ 6 +
    (229431263360770758954446666931334945084631712) * X ^ 7 +
    (-6746367813813946646850792969357961461416866471) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (100550126865891700089088629440830895401205155823) +
    (479624008138781379730659473718879273090637305744) * X ^ 1 +
    (-62479869650420776041131448413775479586454958957949) * X ^ 2 +
    (1758210665320165780205612706917507504906360455011377) * X ^ 3 +
    (-36642716782111159429035747240483889361428178153839570) * X ^ 4 +
    (761441542811737679742995640079391672585219930572399272) * X ^ 5 +
    (-16317575092422556949240028689006170209177734581216818917) * X ^ 6 +
    (313739269731836214614727849519058615165378716994518742301) * X ^ 7 +
    (-4817638967433349342058548121550619317816749956080968393311) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (53160623626133834359455700544858653802009214956001787596081) +
    (-287489583485876456172011259201602774619489074992677510867393) * X ^ 1 +
    (-3463614646119252335687271464217952992636251814131773217124915) * X ^ 2 +
    (127809051911270169567794580840562334256047860565049414305496135) * X ^ 3 +
    (-2232679958157813242975068570226357269639609753886042181021543292) * X ^ 4 +
    (28885665934988015108578594043584308953634647000789366761759593707) * X ^ 5 +
    (-305241869169389788742137017368483875065075911324541372990811737388) * X ^ 6 +
    (2744105435636414595139324751964346580067026094590316618845382387236) * X ^ 7 +
    (-21462944223496406125470845949635224623181859564988105794785629424829) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (148164227745483176674307399637022272542450858335525713445727418899054) +
    (-911870132090687304809715255952639530091351865967748165586300489727795) * X ^ 1 +
    (5044139177085209026345154032099121346364162742484488708608878307563248) * X ^ 2 +
    (-25309681453766403381527518024450581891614033574709105249199766065104053) * X ^ 3 +
    (116950366987291362845802424348450749581482924943894024026091889159790114) * X ^ 4 +
    (-511949431009339902438489753526117283341117509257570325662803860800222938) * X ^ 5 +
    (2225004997182139305258214253422845532832543101236301826823766241533647195) * X ^ 6 +
    (-10142593654624069390883873844812145404626696005311221881666061281952892360) * X ^ 7 +
    (49834526371622579862090197081613551708207593103847327452475371929144594613) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (-257515813380440216503114396910828578451040373157444164344760214689734810465) +
    (1327187997634637796525444285433783403006244474703224730393882743181723383801) * X ^ 1 +
    (-6507258750142162711584057147348326024702503958594767284046624197251520656418) * X ^ 2 +
    (29432672546965845965833409429293154294518538873114121561769750200084935723117) * X ^ 3 +
    -((1 * 10 ^ 77 +
      20563313932515483130330455918561492457893631420163528292573119759750931387644)) * X ^ 4 +
    ((4 * 10 ^ 77 +
      41559642135480509579883660773378835112336438413822167094902953119499591403103)) * X ^ 5 +
    -((14 * 10 ^ 77 +
      24670182627775107159299526273772653735878990763583862113342054083643937871129)) * X ^ 6 +
    ((39 * 10 ^ 77 +
      29270232338596138000080847553709948367489773182885238319575557665908093175425)) * X ^ 7 +
    -((85 * 10 ^ 77 +
      25287615476901170235839092436095043893263330295891789492623403644471226184616)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    ((100 * 10 ^ 77 +
      63297457149802106699202363357568641865059336477654441399180481159928844499353)) +
    ((240 * 10 ^ 77 +
      92852235576611303304642880857556700282954532145799559108375266344056586836577)) * X ^ 1 +
    -((2179 * 10 ^ 77 +
      59380524150250925825772323490516432346782476633965248891034506896693780575916)) * X ^ 2 +
    ((9471 * 10 ^ 77 +
      86946875907484469662907433496063439685324057624663539537627936389257676947643)) * X ^ 3 +
    -((32782 * 10 ^ 77 +
      81815950939196571402410897844567769300036284953969513327228530371182569853782)) * X ^ 4 +
    ((102961 * 10 ^ 77 +
      56680450622544111922450569063653058606884288964458455674881984332997620830080)) * X ^ 5 +
    -((295935 * 10 ^ 77 +
      51962345889876756293385886215692642394634033527497660102315250778707379372439)) * X ^ 6 +
    ((681294 * 10 ^ 77 +
      38584635308306969183090055410962377312441635566735883329562426621196080149443)) * X ^ 7 +
    -((802879 * 10 ^ 77 +
      56791168598144627141914684885872656243020185215542500148641279898625810982659)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    -((1443543 * 10 ^ 77 +
      21506313655201348123690139846034202753352173663224268444703686009824542543159)) +
    ((6160866 * 10 ^ 77 +
      89429602629654017379642679044481900899551877023901558882316322873252864173494)) * X ^ 1 +
    ((19551941 * 10 ^ 77 +
      17162308642707047143466478826158418542143623705986063152906721821089226693870)) * X ^ 2 +
    -((212941665 * 10 ^ 77 +
      33640368383181097516131628696869271335007693854819481658001680308678933110926)) * X ^ 3 +
    ((680099069 * 10 ^ 77 +
      54500898578856030458496906344683944634271344818842038170489628492028953554912)) * X ^ 4 +
    -((25200017 * 10 ^ 77 +
      31509776935620178246479785775190469670933759348362875178223181201911737459877)) * X ^ 5 +
    -((8926039819 * 10 ^ 77 +
      57965868339717048605538390984105471674003232833089223517208096049846821142493)) * X ^ 6 +
    ((39183824945 * 10 ^ 77 +
      27324430297210773068258825360726257888668823227415348790968220120349069509762)) * X ^ 7 +
    -((62072300614 * 10 ^ 77 +
      99758783270091802400281003380389198649737124630048293670983162993505790852161)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((185607968508 * 10 ^ 77 +
      77695900164051900723974428003569672542716809687502560963078708317633153511924)) +
    ((1498765188931 * 10 ^ 77 +
      40750185073090030823865476164370882975643176898237518126347894336087888080476)) * X ^ 1 +
    -((4534914804270 * 10 ^ 77 +
      89810543232967994176425853237256826789633737155094776334800871164887698810144)) * X ^ 2 +
    ((4345334107726 * 10 ^ 77 +
      51798799419540422965478236182131053469845612834360105992135438169136889113782)) * X ^ 3 +
    ((25886872820317 * 10 ^ 77 +
      58489939869566878618933477964542761168392227446456375281654660630716308843027)) * X ^ 4 +
    -((154639909630252 * 10 ^ 77 +
      15384980589990954487982836432973971066546537252695294299134438940863417216845)) * X ^ 5 +
    ((441318117966176 * 10 ^ 77 +
      09477706116013715397611524861316419237863185140480522329951112893843135448180)) * X ^ 6 +
    -((577949917607731 * 10 ^ 77 +
      60970585268660188491294632743237999387391571506731920515418756754571085566465)) * X ^ 7 +
    -((1195361150462115 * 10 ^ 77 +
      44054528340434238146487053224717271254991194856942820373805812524525852635243)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    ((10001583029766808 * 10 ^ 77 +
      84307506231836314319391118714210018456822609560758036307487821709898340752699)) +
    -((34915580380998079 * 10 ^ 77 +
      99257906924432806422522207232466551462263137415366776540939693281435406741357)) * X ^ 1 +
    ((79385085585732965 * 10 ^ 77 +
      53092875891957199489713501218255805520558100290836975514633123661704879253618)) * X ^ 2 +
    -((99006631646556034 * 10 ^ 77 +
      80681874849278577802289067359382465202103850469744233308880087517983683777388)) * X ^ 3 +
    -((115416591062711255 * 10 ^ 77 +
      24032949081335213458690211395695725937093356521559586301095553544255535440174)) * X ^ 4 +
    ((1187430380632776955 * 10 ^ 77 +
      80527085995370779134248782694785357679931312219999688309986426913231763088567)) * X ^ 5 +
    -((4585094284423391102 * 10 ^ 77 +
      53627381469990240921758953598854110216750362631847228974428249422493089100957)) * X ^ 6 +
    ((13215369430744008123 * 10 ^ 77 +
      48761434079559567468814917597978137139022394437226289261411879701744381078427)) * X ^ 7 +
    -((32031808655980942432 * 10 ^ 77 +
      67610451348976426890757706233927527092518416595963218822762052931312165672625)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((68327501510427700147 * 10 ^ 77 +
      94952408811264993969945086849636487613506330515323395774827708885606858635855)) +
    -((131256456301748323775 * 10 ^ 77 +
      65304191520529358067600582832658898677258783131769164810824326147336044021071)) * X ^ 1 +
    ((230181129569052534531 * 10 ^ 77 +
      91520979168135036823053537286723720925525948511581355979484128611888475445599)) * X ^ 2 +
    -((371786156451756425869 * 10 ^ 77 +
      40817170051766130675125871035064169998847674140847218824511356656057284814303)) * X ^ 3 +
    ((556499040800859155015 * 10 ^ 77 +
      20563426259573805490779923962268604564188855877813053862482504627327701432121)) * X ^ 4 +
    -((775392600742715695401 * 10 ^ 77 +
      18019489810314587527574791607257837724256718501631255857046941740903623383970)) * X ^ 5 +
    ((1009047502415959206888 * 10 ^ 77 +
      09663961488672461501866911442668363102871294442485409402288876330452700293109)) * X ^ 6 +
    -((1229512717725748502099 * 10 ^ 77 +
      17726725827923053110138037676330357768451116583677806945699850296841473369683)) * X ^ 7 +
    ((1405484338863189814725 * 10 ^ 77 +
      17871087381895527260531147008856999034501470127857800196976393698791160673002)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    -((1509488280594824160968 * 10 ^ 77 +
      14320383701906721694560889878820873497116787277869247344334352037288688935335)) +
    ((1524826564686531235635 * 10 ^ 77 +
      65006116702000791425239244214114195940852110286905973370654451487561641345325)) * X ^ 1 +
    -((1449894397770444847113 * 10 ^ 77 +
      55620753313137264686995904410665834035058743720155902187009016830719473886596)) * X ^ 2 +
    ((1298355493908366066509 * 10 ^ 77 +
      23713955705657314333440187905031918063674269844596473580194866376581921968129)) * X ^ 3 +
    -((1095203927123756577368 * 10 ^ 77 +
      58600959169767094654572496439945933685067137927030523396324801934360457108108)) * X ^ 4 +
    ((870227736692782823659 * 10 ^ 77 +
      01043039809766471482653206001272437978280136356323590429737247569983578820421)) * X ^ 5 +
    -((651158683071666362904 * 10 ^ 77 +
      49490171035214886104120304381392010307583958585916136583625873573344017468202)) * X ^ 6 +
    ((458579391122073229365 * 10 ^ 77 +
      45061206021629761608949643568413362701565543981728501922716578217871588303213)) * X ^ 7 +
    -((303694061453068674613 * 10 ^ 77 +
      55537560747008455612626934470635747996067130096015543807778047910056816487071)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    ((188890157998026800004 * 10 ^ 77 +
      75512264966239589471756808668156914946198778036065622783533541301904665002169)) +
    -((110150892850635334833 * 10 ^ 77 +
      73307534607776838849033345296076861280162613353994644192620969537665953018390)) * X ^ 1 +
    ((60084466641008050802 * 10 ^ 77 +
      44042148336944349896933006356833515394597560469941573318768498035066593122020)) * X ^ 2 +
    -((30560369796332594214 * 10 ^ 77 +
      86784062410658554547407178724633915267291016152260974521980579643557524727676)) * X ^ 3 +
    ((14430339571663122312 * 10 ^ 77 +
      13475599293996445332640852313073848029760816594072849456714802726961801322158)) * X ^ 4 +
    -((6286331016492800178 * 10 ^ 77 +
      35689847291319912793456482196393299872846974874195826534289657557311095845119)) * X ^ 5 +
    ((2502795173622565776 * 10 ^ 77 +
      16011684821404047518373891143183146761182215591554644650173972017840909749243)) * X ^ 6 +
    -((896791179218729666 * 10 ^ 77 +
      49994805736241856903165989281295115116653695956176240158549206244762365290096)) * X ^ 7 +
    ((281156191462181824 * 10 ^ 77 +
      21484305192862388451519837907651062372863304404820525784641805771287154129254)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    -((72398416784688764 * 10 ^ 77 +
      31863491883953618227887602825842870684481300898294325515152077087031936982514)) +
    ((12378078308032391 * 10 ^ 77 +
      34285063113428816848163175478920286352268632535442705407257833994769376593031)) * X ^ 1 +
    ((670829362593856 * 10 ^ 77 +
      03117135240940766683684627334583517486555062448878817529863962024036699617751)) * X ^ 2 +
    -((1768310074890086 * 10 ^ 77 +
      23695733262963894093745951775226139067329453270856917037863663892192834490158)) * X ^ 3 +
    ((966038110791417 * 10 ^ 77 +
      10987927115188306266903425720670459947950172845434540600999708791054516456412)) * X ^ 4 +
    -((374477195306377 * 10 ^ 77 +
      25462366524450286766163493227406115861174802788385218876895545036791896197275)) * X ^ 5 +
    ((116690994895171 * 10 ^ 77 +
      54532706898374240756972154721892690718595328713590166701010854164814808033603)) * X ^ 6 +
    -((29829578591638 * 10 ^ 77 +
      72174392703915401274209817959495170193378544222300680747565795571241341999269)) * X ^ 7 +
    ((6041841456276 * 10 ^ 77 +
      52883699196929101778698627093969048155843824209653599157735335401956933710731)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    -((826593428559 * 10 ^ 77 +
      78814214176223494431256915793397386946736299215793006863868292935865809238872)) +
    ((2296710618 * 10 ^ 77 +
      78770923512227768335256282048666489191057304902375045621195747743504464347985)) * X ^ 1 +
    ((43383674060 * 10 ^ 77 +
      00905925001124566270236710225285579232883372522372585335367724473946611837471)) * X ^ 2 +
    -((17123862549 * 10 ^ 77 +
      29522917755356615704559846315667418851613019292344801182462703468767570425016)) * X ^ 3 +
    ((4478088431 * 10 ^ 77 +
      57883725247897900289355221725476843773324790556338273800742404389792584033070)) * X ^ 4 +
    -((911239981 * 10 ^ 77 +
      06478492158022719288914074960523013640417050325799147050820168831832806486253)) * X ^ 5 +
    ((149353698 * 10 ^ 77 +
      64908154729816341451825582951176093445913885190697039884260569985079313237113)) * X ^ 6 +
    -((19510596 * 10 ^ 77 +
      84764971878024051744039260899904321720820104735787445409431085855152437289529)) * X ^ 7 +
    ((1906958 * 10 ^ 77 +
      19152950945687364690309579647427537504955743599134525688726613157576868234880)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    -((107548 * 10 ^ 77 +
      51389085101728924486414796256744449512626688582990509029963699137023539162237)) +
    -((4345 * 10 ^ 77 +
      17483709565926498179511736507979749484438662304703279397800574868852737203445)) * X ^ 1 +
    ((2026 * 10 ^ 77 +
      86773351486928741890579875152774392111207281791536378580490931229376315964126)) * X ^ 2 +
    -((294 * 10 ^ 77 +
      84262847002818562557137051803837554972843462851726235995481623026211262110498)) * X ^ 3 +
    ((28 * 10 ^ 77 +
      41756929843368697922863668455300493809472528881657813681101166085658518938392)) * X ^ 4 +
    -((1 * 10 ^ 77 +
      99572016013499565405096126297100872941270301885049542989120625576429498548024)) * X ^ 5 +
    (10319976281914274350871427050261325126072587396339775018227238631691996126765) * X ^ 6 +
    (-383955431579848790747623783559537519111583865591853361806805161496787629892) * X ^ 7 +
    (9775285667040061100592003794144919362495366248152515835422989209275771595) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band17 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 153 * (
    (-155719345914182968281151491869622935239930310631876162768851989402661961) +
    (1276293991820647516580179621405115470102636517471306749898068432590731) * X ^ 1 +
    (-1490593400462300631071882005886789137905887983908445482181292909226) * X ^ 2 +
    (-46710863530949472988392665822455589364684861396164715647996487742) * X ^ 3 +
    (228691893204381612593690751490707399644615326405776036512007443) * X ^ 4 +
    (86852157597435239456913970915246911571418883420463471665946) * X ^ 5 +
    (-2446988806704803913961355775533209187912374279692138040384) * X ^ 6 +
    (5213632541961808283858850576117449115892169169206093279) * X ^ 7 +
    (-4106857415564544043244095302823237120556461452460852) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1Band18 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 162 * (
    (1172412798048549384894403511826132628468800751888) +
    (-99401509074732351564793249524400197994746428) * X ^ 1 +
    (1811691565030576167575676399539668624434) * X ^ 2 +
    (-4178478126571984624465525171455299) * X ^ 3 +
    (361905845058540118588798539) * X ^ 4 +
    (-183108611955514623) * X ^ 5
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band1 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band2 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band3 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band4 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band5 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band6 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band7 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band8 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band9 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band10 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band11 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band12 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band13 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band14 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band15 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band16 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band17 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band18



end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band1
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band10
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band11
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band12
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band13
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band14
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band15
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band16
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band17
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band18
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band2
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band3
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band4
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band5
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band6
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band7
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band8
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row1Band9


