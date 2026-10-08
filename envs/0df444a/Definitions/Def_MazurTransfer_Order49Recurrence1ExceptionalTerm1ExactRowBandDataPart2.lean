-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm1ExactRowBandDataPart2
-- name    : MazurTransfer_Order49Recurrence1ExceptionalTerm1ExactRowBandDataPart2
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T09:39:28.162102+00:00
-- url     : https://prove2.me/theorems/1c3162d6-58bc-432d-a214-367f13a7478b
-- title:
--   Exact first-recurrence ExceptionalTerm1 data: part 2
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

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (11287910767619677660) * X ^ 2 +
    (194211384301313782030446) * X ^ 3 +
    (-45171173713251976601937908) * X ^ 4 +
    (317609899407482130767666580022) * X ^ 5 +
    (-137316431521623528225484861776075) * X ^ 6 +
    (51980836819042850355594486585550312) * X ^ 7 +
    (-10588148321835856129300479988943226861) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (1493435052072819614731157020001968903080) +
    (-140696090808280877129470735350347513701731) * X ^ 1 +
    (9329498110315369137406011158084029043158063) * X ^ 2 +
    (-436385883487197121340057181763429279280260726) * X ^ 3 +
    (14919561806792477528339355456852138829371533069) * X ^ 4 +
    (-408638255919974419946286967985245268999518975728) * X ^ 5 +
    (11492683314185268963572350862425616694665008731242) * X ^ 6 +
    (-385972616446087304143041635849389702590878462053532) * X ^ 7 +
    (12356861717297716026412909933006391561819437046934815) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (-295210618166593083266779081977317667026381433657063578) +
    (4303659276424175021064191090794834475479083529212326899) * X ^ 1 +
    (-5227996873302264482453172619186654737110321683862764451) * X ^ 2 +
    (-1766147284230575675029143216765349037975818680996556803997) * X ^ 3 +
    (65955853167791224433637000394055499787345042712288057718847) * X ^ 4 +
    (-1780833136795870207256854521036669727031942983394192887683530) * X ^ 5 +
    (43044524244521237571798016984925990329252988049592394769327574) * X ^ 6 +
    (-958213886832267483665066471762661068023176074205620959996899092) * X ^ 7 +
    (19212483083475020179782855773127004345412479525133338377273838300) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (-340180053353344846848257949087411905299872802558931285551944925067) +
    (5281632918578371042792524151507891586310193786244882239364345587527) * X ^ 1 +
    (-71969090760918925174239202282590644722412451389657211499157793137406) * X ^ 2 +
    (864224514431992953018089210480920345658410576769192934723382548742230) * X ^ 3 +
    (-9190975590139769937687326233936356967334603437377862203940879740391450) * X ^ 4 +
    (86991202662481487019790568277684298633359343479098705491937181198564722) * X ^ 5 +
    (-736089055978083677247832367786569972700239424900249357181296013753331114) * X ^ 6 +
    (5590617324929518433877242232013263403624756237793453546125203760877211734) * X ^ 7 +
    (-38237757011233766605165284288264895383722208238424710235287024614636495630) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (236081195460823327004639972723885274687132765828960528799787893720494024533) +
    (-1317381152873394779396858793124930081862822631089839645136794220168345797908) * X ^ 1 +
    (6643812417027606489618571475130852568459231370935499084114911347723693115587) * X ^ 2 +
    (-30233531118607058366519284199080320362711827710792151248744675518228587313202) * X ^ 3 +
    ((1 * 10 ^ 77 +
      23695227608141580228915015643704461733605218789838618681418107492728231806090)) * X ^ 4 +
    -((4 * 10 ^ 77 +
      51784196077348998532111827830843577684219889132802796385897533722053121456518)) * X ^ 5 +
    ((14 * 10 ^ 77 +
      51793732754342082197547813386075628178174656552961410963572982599510682992475)) * X ^ 6 +
    -((39 * 10 ^ 77 +
      69281841305939955439861459312416580476759355722126229089928533529386843729374)) * X ^ 7 +
    ((83 * 10 ^ 77 +
      98864517717478987329298897197785149179405533174512366500878926917856694530240)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    -((85 * 10 ^ 77 +
      19763782903779537932871514961301181764099656768513455511723761280893907163835)) +
    -((338 * 10 ^ 77 +
      46865579831218343160333188938255756210074238900887386194385928389953620226177)) * X ^ 1 +
    ((2681 * 10 ^ 77 +
      76624356494823935984102691957419811929107369709540032788576829625311165145738)) * X ^ 2 +
    -((11690 * 10 ^ 77 +
      15263387266101652540779396881069584521818069261511850277391668287961748339818)) * X ^ 3 +
    ((41315 * 10 ^ 77 +
      41476738490059619190797063804557332179120260283026846657394476294434691559762)) * X ^ 4 +
    -((133064 * 10 ^ 77 +
      87803024792863251471772030036644969420855517950324287752584527773333480208268)) * X ^ 5 +
    ((399772 * 10 ^ 77 +
      41971818329338378960288348912520070060015520382866874821318583242680524485887)) * X ^ 6 +
    -((1017637 * 10 ^ 77 +
      54425500834132685891059708481205343378320309053648751771476221012803039244290)) * X ^ 7 +
    ((1617443 * 10 ^ 77 +
      70619645886803922045602376164677236982369957149084361586060458957565329878671)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    ((990658 * 10 ^ 77 +
      85533712386168476031419419698477210805752459725521924674910453966650879257543)) +
    -((13061196 * 10 ^ 77 +
      80780657978181432180427914622341956443169378978480379553455169447972660296218)) * X ^ 1 +
    ((15367103 * 10 ^ 77 +
      18906765726295043182337322769400285949946148072250444790808558280340178735398)) * X ^ 2 +
    ((130612760 * 10 ^ 77 +
      13405212984804032952506144573031838303938209670115430102685489345807145125040)) * X ^ 3 +
    -((583350868 * 10 ^ 77 +
      99087790054566944570136779914881015585543828429345478160136482630369425669523)) * X ^ 4 +
    -((246807247 * 10 ^ 77 +
      94943442268120433874573353363550517989447962791426581744463700179468685279263)) * X ^ 5 +
    ((11348831675 * 10 ^ 77 +
      24160809181234618760159096901488231199043285696491551540290132911931553798652)) * X ^ 6 +
    -((49144551235 * 10 ^ 77 +
      71189962813130977509331992285059062484864965612365431517410846921575449857854)) * X ^ 7 +
    ((72424628795 * 10 ^ 77 +
      64330098433435485434211795767322405852455851645444887976876284314262867189075)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    ((260680092643 * 10 ^ 77 +
      19378138528471512070793315518814124006022859941024325396944727918234132051057)) +
    -((1822337709333 * 10 ^ 77 +
      14901231805453521038791083559417657585042934619008301393104673460656184495039)) * X ^ 1 +
    ((4522589854213 * 10 ^ 77 +
      19548655862037090824692753296775752843567093633129477553012788828389960302557)) * X ^ 2 +
    ((39235163644 * 10 ^ 77 +
      05328650858977017703545857278067091297934180799697364604977364105707724106834)) * X ^ 3 +
    -((41762045182374 * 10 ^ 77 +
      71514925441071486271589595196304174353310982661813036800248019162796232742045)) * X ^ 4 +
    ((160933167542520 * 10 ^ 77 +
      46584525298798613211718436632570348824056229157409929421718687112564170447150)) * X ^ 5 +
    -((283279257178989 * 10 ^ 77 +
      09345377428014394376114440788244114801668287890163253985902428418772928924490)) * X ^ 6 +
    -((86503862866637 * 10 ^ 77 +
      65895622168109792344265995211182609552952270923146053148122985009292847343864)) * X ^ 7 +
    ((2050583628616914 * 10 ^ 77 +
      07484862230491143817117471528300956856053923476288143307190884770859292211155)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((6514081890685775 * 10 ^ 77 +
      94530381711318285851704686384113867349979101093153607633642155091832901777966)) +
    ((13049176535580267 * 10 ^ 77 +
      87007932324306425126537921790193373405700242267425357032032927280869199887405)) * X ^ 1 +
    -((27418688570265405 * 10 ^ 77 +
      79484947422709817083526229651714336558640544608292009143206109137711592550835)) * X ^ 2 +
    ((96510771966361207 * 10 ^ 77 +
      34587891375744780337607708377543723907615939814054876319238312301926611161776)) * X ^ 3 +
    -((342310180827608224 * 10 ^ 77 +
      77004019125890290952514465422024863860384187294645120442171984132373505986994)) * X ^ 4 +
    ((692802101598577719 * 10 ^ 77 +
      73378486944041975391634466912258120470350234606514335641878555328016015608952)) * X ^ 5 +
    ((708703199171316273 * 10 ^ 77 +
      72728869628000400614966414955290813059012288856646661632057087340813313545765)) * X ^ 6 +
    -((12334237205014272026 * 10 ^ 77 +
      79610888354905956762096101031838059545251923946382405066731488367956559948002)) * X ^ 7 +
    ((58312365465144410582 * 10 ^ 77 +
      57294217074483002050252971659212618183210134304924584081626033885281511300511)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    -((184453699694771718975 * 10 ^ 77 +
      59579461741275933803081485862878677194143112826778396374794763157723861770733)) +
    ((430280277671215400251 * 10 ^ 77 +
      80087620572243690090452191098075913093341419229774373773791869480445363572010)) * X ^ 1 +
    -((692217324160907831602 * 10 ^ 77 +
      56614075850406368213769521577286537769420901151304673643493380131993199819439)) * X ^ 2 +
    ((353526431257493680855 * 10 ^ 77 +
      68749874418049069486178152783440600602898639724286048701016996155210755143429)) * X ^ 3 +
    ((2448605874144644424105 * 10 ^ 77 +
      01065340304019137523817771249051858462956833024888411189180473953347003095217)) * X ^ 4 +
    -((11925997644062491831322 * 10 ^ 77 +
      12025380521474420856713182406277587463689485724499267120262328645862277900578)) * X ^ 5 +
    ((35802095623463167866162 * 10 ^ 77 +
      96810372417354970510870966622383526994587817763263570456122007243466889777061)) * X ^ 6 +
    -((85756460178405177676964 * 10 ^ 77 +
      11061235505513946224495841843936312451382021331434818154304499260997146736266)) * X ^ 7 +
    ((176002792507626375197133 * 10 ^ 77 +
      93712070286636229423297779875645178238921235814937302633417064908324332383644)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    -((318999664988466806955604 * 10 ^ 77 +
      24294833291236713882183749107536529668699528183223751953858625941709666017684)) +
    ((518320784579026931269822 * 10 ^ 77 +
      35362571207332872485421766999082499539874600999904144890788123491299932851649)) * X ^ 1 +
    -((760544074701096701350471 * 10 ^ 77 +
      60249853010771073985768901310419720771491719932389058759753253951449293883636)) * X ^ 2 +
    ((1009877976296723826429128 * 10 ^ 77 +
      02441761647675194170097699725263325871690931431096687696249540335082018196901)) * X ^ 3 +
    -((1209830282235045314621202 * 10 ^ 77 +
      17197056326584902221013936112978127474694769346833087406309302276212295351449)) * X ^ 4 +
    ((1294458721628251274095676 * 10 ^ 77 +
      95556643979399115635878164467669589738366699925978448422387540091179924819473)) * X ^ 5 +
    -((1207702298614733890191934 * 10 ^ 77 +
      26540189363646855468782180462673998257709831595634548468203580202727362293474)) * X ^ 6 +
    ((924649634517125452936152 * 10 ^ 77 +
      86658811645980032727905644844230783139333991737545039150935432327314570207102)) * X ^ 7 +
    -((465983359662756926665934 * 10 ^ 77 +
      67760675280417011242645290021826744551826643968087449133835053409323190301836)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    -((101717054941104595337687 * 10 ^ 77 +
      14877882397096089545264264972281360216958286950164542214985798772486069311981)) +
    ((681690823080934430895573 * 10 ^ 77 +
      96662452361416783648833089719320265854016563012566159187555054576948951455304)) * X ^ 1 +
    -((1173644837061846907330082 * 10 ^ 77 +
      00950287529093404489608463568998240035957293288316956692588319330732432634746)) * X ^ 2 +
    ((1501367563262472178290388 * 10 ^ 77 +
      96585807562804604594730758420153415084303418944104169789971928337038396800560)) * X ^ 3 +
    -((1631109895997594020293786 * 10 ^ 77 +
      88096535274687643273463583993539047309161113408686864657963183949238139860284)) * X ^ 4 +
    ((1574956105084678442459266 * 10 ^ 77 +
      99555188489279730265086097671618237187641399091568369515732447402594000082762)) * X ^ 5 +
    -((1379981261269460060640035 * 10 ^ 77 +
      89776730509106587932830926687757527697787864745498234055197311449751471311140)) * X ^ 6 +
    ((1109334322128547679289645 * 10 ^ 77 +
      50240828908599344289430119744008211286164418478372081556579927437420578269574)) * X ^ 7 +
    -((823209331930523327031754 * 10 ^ 77 +
      60724094769983181882638031148422402415994977201790226703339020176660173577686)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    ((565837563434039047406440 * 10 ^ 77 +
      95971922288281117677880341859452205307812337161655894199053600217447979727310)) +
    -((360817494154511508204882 * 10 ^ 77 +
      69948216047364714566711608989794994046564197477637605540126042164334049856843)) * X ^ 1 +
    ((213483693276422469945351 * 10 ^ 77 +
      38846991225458136832412375100984687659512215427671878152159954481940226605998)) * X ^ 2 +
    -((117065578139410053700149 * 10 ^ 77 +
      30685890299774142491638401487060452130622675551231065770941798242254799904879)) * X ^ 3 +
    ((59344135597250472472033 * 10 ^ 77 +
      05547017157597898420532810875252760541407383597277288720865025306049368416946)) * X ^ 4 +
    -((27690404339844970308610 * 10 ^ 77 +
      85755824474946568868939917703124511466517548345911142539338777928402683708919)) * X ^ 5 +
    ((11810158892606220497626 * 10 ^ 77 +
      57676340040925165061782831629635672129299884202600384529431362008493498131838)) * X ^ 6 +
    -((4551901767519099793253 * 10 ^ 77 +
      04752412678980936135626409640504931368051602807994713813585858809940793731806)) * X ^ 7 +
    ((1553764123970573693126 * 10 ^ 77 +
      16540295328983494468504968120337678005025399490339189367098663715290374245688)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    -((450880775287402943073 * 10 ^ 77 +
      93680708347024291328459968085428121731404124282624698161126672491402315171049)) +
    ((99783324633309891216 * 10 ^ 77 +
      11065592179614002572745648243826051580881132534344817996275873189608286224224)) * X ^ 1 +
    -((9303730464236519943 * 10 ^ 77 +
      83483649148843371955335186200488302821821245627865270748719151021559795212457)) * X ^ 2 +
    -((5601386788508636479 * 10 ^ 77 +
      81356702410482430310413199109653561570746531143096468384629360104333563697726)) * X ^ 3 +
    ((4312992642018352743 * 10 ^ 77 +
      48840328140870678415783273675657384019156990607332380315857479031034077419690)) * X ^ 4 +
    -((1906096618653644817 * 10 ^ 77 +
      64018205595159952195790507786401419955438591628628460260880083648102430752877)) * X ^ 5 +
    ((648152984933087036 * 10 ^ 77 +
      41490092601117321415363118088647028993471424172693373857937526022371712703377)) * X ^ 6 +
    -((178942205127679381 * 10 ^ 77 +
      77460531483683895075315387612839565804216856894899640705493680456149784106943)) * X ^ 7 +
    ((39594704315382691 * 10 ^ 77 +
      93643879778396288930989366691101455689892226468619958958306356925624208538803)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    -((6356116478525631 * 10 ^ 77 +
      76881551137248117899314695496888653920991596247507659986703238735177482889042)) +
    ((385725006085165 * 10 ^ 77 +
      09371846046670991991421429394036814485344993014680538350213688310845802246242)) * X ^ 1 +
    ((189512037804260 * 10 ^ 77 +
      11399288471204366091367326306691001148576359597430504873818913235318173000636)) * X ^ 2 +
    -((94214361441427 * 10 ^ 77 +
      73764810890970597575745713639103993306319935302794078914304804159982576776638)) * X ^ 3 +
    ((26865127401305 * 10 ^ 77 +
      08621858844458341421914185145322200970776228532952564942627200861605875505370)) * X ^ 4 +
    -((5778655553375 * 10 ^ 77 +
      47443659670552012214694557280008007281852703526076899873278169860569641978283)) * X ^ 5 +
    ((990491353319 * 10 ^ 77 +
      29433841425112659743801580339365299540246486522988205734965662460737225681839)) * X ^ 6 +
    -((135041603119 * 10 ^ 77 +
      24317465072152532285238387676876195151411853769830852224108203767644834349294)) * X ^ 7 +
    ((13898148539 * 10 ^ 77 +
      39220090582383676135312955069006111693884678097290331653268900964149537942264)) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band17 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 153 * (
    -((876546131 * 10 ^ 77 +
      35288339137115320351235730092309018371633590475372259620943092508172921202671)) +
    -((15796357 * 10 ^ 77 +
      77286059710343679942189757969489292850426617681035337333837105434060751263690)) * X ^ 1 +
    ((13168083 * 10 ^ 77 +
      56095184455754537078435830520355859574400525839660344393965860857691231076356)) * X ^ 2 +
    -((2045132 * 10 ^ 77 +
      04642806959358706079833591928714983681081949613970790627011557382338407611058)) * X ^ 3 +
    ((203814 * 10 ^ 77 +
      42171826699333517867299886454218144538445287337795642567192004566029983509778)) * X ^ 4 +
    -((14648 * 10 ^ 77 +
      96093793831441153635732475328270674551163438052338529083734702726432773222816)) * X ^ 5 +
    ((771 * 10 ^ 77 +
      17450989637607439116430331842145879964061151849679826161827752132392524636964)) * X ^ 6 +
    -((29 * 10 ^ 77 +
      10556370983492944451902909918962947807943829994220680547007749206699348585590)) * X ^ 7 +
    (74959870904881670597670762538947674843391337569381807970347804704631855721548) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band18 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 162 * (
    (-1205242628497108802864064525014824176399001505839029544710173232589439061082) +
    (9961468930569408574740570635531713543892023202187076791112278390925338138) * X ^ 1 +
    (-12083598414839599416830088970662377997550811811561633806101288505261410) * X ^ 2 +
    (-362964805503171028542393384609258770617339621051622996892197837353828) * X ^ 3 +
    (1788239872961011529305052796171350259575998143510237305434695233773) * X ^ 4 +
    (656119085724879228136026111913898194618127631259197458119849806) * X ^ 5 +
    (-19077080042415235925519795198095506917769217858021565324726708) * X ^ 6 +
    (40711235716587791857793576710939189654008250364753612802624) * X ^ 7 +
    (-32088009746753131552437821488127388121865169260215050171) * X ^ 8
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2Band19 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 171 * (
    (9162569507286653740558497499459943505524090087972859) +
    (-776898091419996271438559972464680749389159610460) * X ^ 1 +
    (14160009789146050977018883577974265299493961) * X ^ 2 +
    (-32658675661887769636616831822822243208) * X ^ 3 +
    (2828629578771939578368486081986) * X ^ 4 +
    (-1431163500917805567360) * X ^ 5
  )

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Row2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band2 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band3 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band4 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band5 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band6 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band7 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band8 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band9 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band10 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band11 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band12 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band13 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band14 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band15 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band16 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band17 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band18 +
  MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band19











































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData

#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band10
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band11
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band12
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band13
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band14
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band15
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band16
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band17
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band18
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band19
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band2
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band3
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band4
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band5
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band6
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band7
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band8
#print axioms MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row2Band9


