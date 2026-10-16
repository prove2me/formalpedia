-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01HeightBracketTree
-- name    : TaoFivePrimes_RHBatch01HeightBracketTree
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T16:14:30.295293+00:00
-- url     : https://prove2.me/theorems/99dab7dd-c81d-44d6-871e-549f1667d1ae
-- title:
--   TaoFivePrimes_RHBatch01HeightBracketTree
-- statement:
--   An ordered tree of 409 proposed sign brackets from a 1/32-spaced high-height grid. Each leaf carries ordinary proofs of coordinate bounds, interval ordering and opposite strict signs of its proposed dyadic boxes. Each join carries a proof that its subtrees are ordered. These certificates assert no containment of normalized zeta values.
-- source:
--   Finite structural sign and order certificates, generated from the native FLINT 3.6.0 Platt FFT/interpolation proposal on [3289999744,3289999872]. Numeric tests are necessary constructor proof fields and use ordinary decide +kernel. No value containment, total zero count or RH conclusion is asserted. Platt method: DOI 10.1090/mcom/3198. The surrounding project preserves attribution to sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham.

/- Structural certificates for proposed high-height sign brackets.
Every finite sign/order test is a necessary proof field checked in ordinary Lean.
Containment of mathematical zeta values is NOT asserted by these records.
Numerical proposals: Platt/FLINT. Surrounding xi/theta work: sometik179 and
Gabewhigham. -/
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace RHBatch01HeightBracketData
structure Bracket where
  l : Nat
  r : Nat
  llo : Int
  lhi : Int
  rlo : Int
  rhi : Int
  bound : l<r ∧ r≤4096
  boxOrder : llo≤lhi ∧ rlo≤rhi
  signs : (lhi<0 ∧ 0<rlo) ∨ (rhi<0 ∧ 0<llo)
inductive Tree : Nat → Nat → Nat → Type
  | leaf (b : Bracket) : Tree b.l b.r 1
  | join {l₁ r₁ n₁ l₂ r₂ n₂ : Nat}
      (u : Tree l₁ r₁ n₁) (v : Tree l₂ r₂ n₂) (ordered : r₁≤l₂) :
      Tree l₁ r₂ (n₁+n₂)
noncomputable def leaf0 : Bracket :=
  ⟨9, 10, (Int.negSucc 45605284259280030), (Int.negSucc 45605284259280014), (Int.ofNat 6285147167817532), (Int.ofNat 6285147167817538),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf1 : Bracket :=
  ⟨12, 13, (Int.ofNat 2229364972133513), (Int.ofNat 2229364972133517), (Int.negSucc 52204693434074592), (Int.negSucc 52204693434074584),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf2 : Bracket :=
  ⟨27, 28, (Int.negSucc 91501179921910422), (Int.negSucc 91501179921910412), (Int.ofNat 5051848880664895), (Int.ofNat 5051848880664898),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf3 : Bracket :=
  ⟨34, 35, (Int.ofNat 47757601357552803), (Int.ofNat 47757601357552818), (Int.negSucc 18364617643700677), (Int.negSucc 18364617643700670),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf4 : Bracket :=
  ⟨44, 45, (Int.negSucc 57595214066261645), (Int.negSucc 57595214066261641), (Int.ofNat 18535615044702366), (Int.ofNat 18535615044702379),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf5 : Bracket :=
  ⟨55, 56, (Int.ofNat 6441278387129353), (Int.ofNat 6441278387129360), (Int.negSucc 50587530528338565), (Int.negSucc 50587530528338561),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf6 : Bracket :=
  ⟨62, 63, (Int.negSucc 21580307822266235), (Int.negSucc 21580307822266222), (Int.ofNat 41086013039538518), (Int.ofNat 41086013039538528),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf7 : Bracket :=
  ⟨72, 73, (Int.ofNat 1274349288620073), (Int.ofNat 1274349288620086), (Int.negSucc 98878185274487474), (Int.negSucc 98878185274487463),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf8 : Bracket :=
  ⟨82, 83, (Int.negSucc 42263976124516109), (Int.negSucc 42263976124516093), (Int.ofNat 118285198335601168), (Int.ofNat 118285198335601183),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf9 : Bracket :=
  ⟨98, 99, (Int.ofNat 37431769159591217), (Int.ofNat 37431769159591225), (Int.negSucc 63621451889437647), (Int.negSucc 63621451889437626),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf10 : Bracket :=
  ⟨106, 107, (Int.negSucc 26859582678883218), (Int.negSucc 26859582678883197), (Int.ofNat 33446073488512726), (Int.ofNat 33446073488512745),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf11 : Bracket :=
  ⟨117, 118, (Int.ofNat 12308375849965597), (Int.ofNat 12308375849965613), (Int.negSucc 12784442492538369), (Int.negSucc 12784442492538348),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf12 : Bracket :=
  ⟨123, 124, (Int.negSucc 5323201576916697), (Int.negSucc 5323201576916680), (Int.ofNat 8771099138343280), (Int.ofNat 8771099138343286),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf13 : Bracket :=
  ⟨127, 128, (Int.ofNat 12670123788988674), (Int.ofNat 12670123788988682), (Int.negSucc 6277745422304472), (Int.negSucc 6277745422304462),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf14 : Bracket :=
  ⟨137, 138, (Int.negSucc 63669584089505142), (Int.negSucc 63669584089505125), (Int.ofNat 34726283704953513), (Int.ofNat 34726283704953522),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf15 : Bracket :=
  ⟨155, 156, (Int.ofNat 20133135630545500), (Int.ofNat 20133135630545509), (Int.negSucc 165696727466581626), (Int.negSucc 165696727466581621),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf16 : Bracket :=
  ⟨167, 168, (Int.negSucc 22892659009107140), (Int.negSucc 22892659009107126), (Int.ofNat 55835246671307908), (Int.ofNat 55835246671307918),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf17 : Bracket :=
  ⟨175, 176, (Int.ofNat 22282619614062996), (Int.ofNat 22282619614063009), (Int.negSucc 17656624506350959), (Int.negSucc 17656624506350943),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf18 : Bracket :=
  ⟨181, 182, (Int.negSucc 9073964940152991), (Int.negSucc 9073964940152982), (Int.ofNat 34973843145449741), (Int.ofNat 34973843145449761),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf19 : Bracket :=
  ⟨190, 191, (Int.ofNat 45584820613954839), (Int.ofNat 45584820613954858), (Int.negSucc 44952977812152682), (Int.negSucc 44952977812152663),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf20 : Bracket :=
  ⟨205, 206, (Int.negSucc 48009280141941574), (Int.negSucc 48009280141941561), (Int.ofNat 38697071827158397), (Int.ofNat 38697071827158416),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf21 : Bracket :=
  ⟨212, 213, (Int.ofNat 31272151843793549), (Int.ofNat 31272151843793553), (Int.negSucc 42780960467533377), (Int.negSucc 42780960467533363),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf22 : Bracket :=
  ⟨224, 225, (Int.negSucc 17357234209269264), (Int.negSucc 17357234209269257), (Int.ofNat 55599652536384302), (Int.ofNat 55599652536384322),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf23 : Bracket :=
  ⟨234, 235, (Int.ofNat 8202445961412925), (Int.ofNat 8202445961412934), (Int.negSucc 27133773598087764), (Int.negSucc 27133773598087754),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf24 : Bracket :=
  ⟨239, 240, (Int.negSucc 1077218327518887), (Int.negSucc 1077218327518869), (Int.ofNat 48435462080533518), (Int.ofNat 48435462080533531),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf25 : Bracket :=
  ⟨252, 253, (Int.ofNat 21542879783734873), (Int.ofNat 21542879783734878), (Int.negSucc 28111387086677404), (Int.negSucc 28111387086677397),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf26 : Bracket :=
  ⟨256, 257, (Int.negSucc 5520821065860912), (Int.negSucc 5520821065860909), (Int.ofNat 74527562818694505), (Int.ofNat 74527562818694517),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf27 : Bracket :=
  ⟨272, 273, (Int.ofNat 234582276059385517), (Int.ofNat 234582276059385533), (Int.negSucc 5491810528716640), (Int.negSucc 5491810528716630),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf28 : Bracket :=
  ⟨283, 284, (Int.negSucc 98086893976237258), (Int.negSucc 98086893976237248), (Int.ofNat 39801090175689916), (Int.ofNat 39801090175689928),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf29 : Bracket :=
  ⟨289, 290, (Int.ofNat 40153180271471529), (Int.ofNat 40153180271471545), (Int.negSucc 127692705876839676), (Int.negSucc 127692705876839656),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf30 : Bracket :=
  ⟨302, 303, (Int.negSucc 342116639349393243), (Int.negSucc 342116639349393231), (Int.ofNat 12169671966207577), (Int.ofNat 12169671966207589),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf31 : Bracket :=
  ⟨315, 316, (Int.ofNat 216860916585473249), (Int.ofNat 216860916585473262), (Int.negSucc 42165264922317650), (Int.negSucc 42165264922317636),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf32 : Bracket :=
  ⟨322, 323, (Int.negSucc 84692564452255762), (Int.negSucc 84692564452255743), (Int.ofNat 191925048627723782), (Int.ofNat 191925048627723793),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf33 : Bracket :=
  ⟨338, 339, (Int.ofNat 95143299118679353), (Int.ofNat 95143299118679375), (Int.negSucc 226860428131880739), (Int.negSucc 226860428131880720),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf34 : Bracket :=
  ⟨349, 350, (Int.negSucc 110697259904799087), (Int.negSucc 110697259904799073), (Int.ofNat 50515870769231178), (Int.ofNat 50515870769231198),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf35 : Bracket :=
  ⟨359, 360, (Int.ofNat 25695208818739369), (Int.ofNat 25695208818739381), (Int.negSucc 38814972831045192), (Int.negSucc 38814972831045176),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf36 : Bracket :=
  ⟨364, 365, (Int.negSucc 43999262875262797), (Int.negSucc 43999262875262791), (Int.ofNat 20627024850722619), (Int.ofNat 20627024850722637),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf37 : Bracket :=
  ⟨380, 381, (Int.ofNat 25137470752958191), (Int.ofNat 25137470752958201), (Int.negSucc 27585283976391627), (Int.negSucc 27585283976391608),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf38 : Bracket :=
  ⟨387, 388, (Int.negSucc 15532172898394192), (Int.negSucc 15532172898394178), (Int.ofNat 10518969910485439), (Int.ofNat 10518969910485453),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf39 : Bracket :=
  ⟨392, 393, (Int.ofNat 23725953212666871), (Int.ofNat 23725953212666878), (Int.negSucc 3678830360114391), (Int.negSucc 3678830360114379),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf40 : Bracket :=
  ⟨406, 407, (Int.negSucc 41813227071643374), (Int.negSucc 41813227071643356), (Int.ofNat 5071939125908079), (Int.ofNat 5071939125908089),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf41 : Bracket :=
  ⟨415, 416, (Int.ofNat 10160519111203082), (Int.ofNat 10160519111203103), (Int.negSucc 18167799688844355), (Int.negSucc 18167799688844339),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf42 : Bracket :=
  ⟨422, 423, (Int.negSucc 15786079167363985), (Int.negSucc 15786079167363965), (Int.ofNat 15565878310858365), (Int.ofNat 15565878310858380),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf43 : Bracket :=
  ⟨433, 434, (Int.ofNat 32626789172608024), (Int.ofNat 32626789172608034), (Int.negSucc 2271830308312922), (Int.negSucc 2271830308312913),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf44 : Bracket :=
  ⟨442, 443, (Int.negSucc 994863896063240), (Int.negSucc 994863896063232), (Int.ofNat 21167689821118120), (Int.ofNat 21167689821118133),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf45 : Bracket :=
  ⟨446, 447, (Int.ofNat 26358701929581376), (Int.ofNat 26358701929581392), (Int.negSucc 3028431647282688), (Int.negSucc 3028431647282676),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf46 : Bracket :=
  ⟨465, 466, (Int.negSucc 21353228099804675), (Int.negSucc 21353228099804663), (Int.ofNat 9145401672647126), (Int.ofNat 9145401672647141),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf47 : Bracket :=
  ⟨467, 468, (Int.ofNat 12030483055801111), (Int.ofNat 12030483055801132), (Int.negSucc 13284532108457623), (Int.negSucc 13284532108457608),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf48 : Bracket :=
  ⟨481, 482, (Int.negSucc 124321560106565122), (Int.negSucc 124321560106565105), (Int.ofNat 16863653986563522), (Int.ofNat 16863653986563539),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf49 : Bracket :=
  ⟨491, 492, (Int.ofNat 84507053580672410), (Int.ofNat 84507053580672426), (Int.negSucc 74997905404398312), (Int.negSucc 74997905404398305),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf50 : Bracket :=
  ⟨503, 504, (Int.negSucc 32993879950170621), (Int.negSucc 32993879950170611), (Int.ofNat 151568854539439085), (Int.ofNat 151568854539439089),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf51 : Bracket :=
  ⟨514, 515, (Int.ofNat 46652985963388354), (Int.ofNat 46652985963388360), (Int.negSucc 119587624797006951), (Int.negSucc 119587624797006937),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf52 : Bracket :=
  ⟨525, 526, (Int.negSucc 85683321850633681), (Int.negSucc 85683321850633666), (Int.ofNat 29730867790870301), (Int.ofNat 29730867790870317),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf53 : Bracket :=
  ⟨536, 537, (Int.ofNat 9266529027514094), (Int.ofNat 9266529027514100), (Int.negSucc 23499805761571179), (Int.negSucc 23499805761571162),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf54 : Bracket :=
  ⟨540, 541, (Int.negSucc 989199851216965), (Int.negSucc 989199851216954), (Int.ofNat 41053421615628187), (Int.ofNat 41053421615628196),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf55 : Bracket :=
  ⟨549, 550, (Int.ofNat 1221001431405357), (Int.ofNat 1221001431405367), (Int.negSucc 112121500177531542), (Int.negSucc 112121500177531533),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf56 : Bracket :=
  ⟨559, 560, (Int.negSucc 194527735083928986), (Int.negSucc 194527735083928974), (Int.ofNat 21410582582760660), (Int.ofNat 21410582582760670),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf57 : Bracket :=
  ⟨569, 570, (Int.ofNat 417023012962427894), (Int.ofNat 417023012962427915), (Int.negSucc 4356398750764848), (Int.negSucc 4356398750764836),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf58 : Bracket :=
  ⟨589, 590, (Int.negSucc 208290659921270174), (Int.negSucc 208290659921270165), (Int.ofNat 288152933359310184), (Int.ofNat 288152933359310199),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf59 : Bracket :=
  ⟨602, 603, (Int.ofNat 44573354012070693), (Int.ofNat 44573354012070708), (Int.negSucc 78048904391743663), (Int.negSucc 78048904391743650),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf60 : Bracket :=
  ⟨610, 611, (Int.negSucc 23528091085131134), (Int.negSucc 23528091085131112), (Int.ofNat 23385777610533993), (Int.ofNat 23385777610534014),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf61 : Bracket :=
  ⟨617, 618, (Int.ofNat 8289357881881010), (Int.ofNat 8289357881881028), (Int.negSucc 20189067179612971), (Int.negSucc 20189067179612950),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf62 : Bracket :=
  ⟨622, 623, (Int.negSucc 31221192097501650), (Int.negSucc 31221192097501632), (Int.ofNat 1937988451770085), (Int.ofNat 1937988451770100),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf63 : Bracket :=
  ⟨637, 638, (Int.ofNat 3042261948816970), (Int.ofNat 3042261948816988), (Int.negSucc 28916390796480853), (Int.negSucc 28916390796480832),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf64 : Bracket :=
  ⟨641, 642, (Int.negSucc 16274003497426197), (Int.negSucc 16274003497426185), (Int.ofNat 23821120496761131), (Int.ofNat 23821120496761146),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf65 : Bracket :=
  ⟨654, 655, (Int.ofNat 43245115436320301), (Int.ofNat 43245115436320315), (Int.negSucc 31626035374793169), (Int.negSucc 31626035374793155),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf66 : Bracket :=
  ⟨662, 663, (Int.negSucc 30772011754751872), (Int.negSucc 30772011754751858), (Int.ofNat 48576010436263830), (Int.ofNat 48576010436263848),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf67 : Bracket :=
  ⟨673, 674, (Int.ofNat 69657446238932541), (Int.ofNat 69657446238932559), (Int.negSucc 14281019507906692), (Int.negSucc 14281019507906678),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf68 : Bracket :=
  ⟨679, 680, (Int.negSucc 34023753857523798), (Int.negSucc 34023753857523785), (Int.ofNat 87368589147358495), (Int.ofNat 87368589147358509),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf69 : Bracket :=
  ⟨698, 699, (Int.ofNat 100617566335267295), (Int.ofNat 100617566335267312), (Int.negSucc 95569230754387324), (Int.negSucc 95569230754387307),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf70 : Bracket :=
  ⟨708, 709, (Int.negSucc 45205675368455697), (Int.negSucc 45205675368455693), (Int.ofNat 43290919295811991), (Int.ofNat 43290919295812007),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf71 : Bracket :=
  ⟨717, 718, (Int.ofNat 14376551832176882), (Int.ofNat 14376551832176897), (Int.negSucc 29227460325558904), (Int.negSucc 29227460325558883),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf72 : Bracket :=
  ⟨722, 723, (Int.negSucc 37888382891691807), (Int.negSucc 37888382891691793), (Int.ofNat 6358191406542705), (Int.ofNat 6358191406542713),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf73 : Bracket :=
  ⟨732, 733, (Int.ofNat 100542844688666625), (Int.ofNat 100542844688666639), (Int.negSucc 9990388671312347), (Int.negSucc 9990388671312327),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf74 : Bracket :=
  ⟨754, 755, (Int.negSucc 4802155841023918), (Int.negSucc 4802155841023904), (Int.ofNat 7022914640950743), (Int.ofNat 7022914640950751),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf75 : Bracket :=
  ⟨757, 758, (Int.ofNat 141886113720619), (Int.ofNat 141886113720634), (Int.negSucc 10662741886713984), (Int.negSucc 10662741886713973),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf76 : Bracket :=
  ⟨765, 766, (Int.negSucc 7967950399979740), (Int.negSucc 7967950399979726), (Int.ofNat 1362872352401888), (Int.ofNat 1362872352401895),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf77 : Bracket :=
  ⟨770, 771, (Int.ofNat 2562086905215439), (Int.ofNat 2562086905215446), (Int.negSucc 6569008801377493), (Int.negSucc 6569008801377486),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf78 : Bracket :=
  ⟨776, 777, (Int.negSucc 8867024141270695), (Int.negSucc 8867024141270688), (Int.ofNat 16586143528685345), (Int.ofNat 16586143528685358),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf79 : Bracket :=
  ⟨792, 793, (Int.ofNat 38451651010832503), (Int.ofNat 38451651010832515), (Int.negSucc 29655356117362122), (Int.negSucc 29655356117362104),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf80 : Bracket :=
  ⟨798, 799, (Int.negSucc 40029350486938119), (Int.negSucc 40029350486938103), (Int.ofNat 39398074051903819), (Int.ofNat 39398074051903826),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf81 : Bracket :=
  ⟨814, 815, (Int.ofNat 59449477994835204), (Int.ofNat 59449477994835220), (Int.negSucc 25772385810234079), (Int.negSucc 25772385810234062),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf82 : Bracket :=
  ⟨819, 820, (Int.negSucc 48457512310734642), (Int.negSucc 48457512310734629), (Int.ofNat 21065448924269198), (Int.ofNat 21065448924269203),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf83 : Bracket :=
  ⟨829, 830, (Int.ofNat 96731310029472398), (Int.ofNat 96731310029472409), (Int.negSucc 63143484365692239), (Int.negSucc 63143484365692227),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf84 : Bracket :=
  ⟨840, 841, (Int.negSucc 68995789651900669), (Int.negSucc 68995789651900662), (Int.ofNat 256918825666954012), (Int.ofNat 256918825666954023),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf85 : Bracket :=
  ⟨856, 857, (Int.ofNat 133065425103635827), (Int.ofNat 133065425103635833), (Int.negSucc 133323178535653124), (Int.negSucc 133323178535653115),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf86 : Bracket :=
  ⟨865, 866, (Int.negSucc 38074327234455536), (Int.negSucc 38074327234455523), (Int.ofNat 72461534302556713), (Int.ofNat 72461534302556727),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf87 : Bracket :=
  ⟨869, 870, (Int.ofNat 58298303804285335), (Int.ofNat 58298303804285349), (Int.negSucc 97421482914231432), (Int.negSucc 97421482914231414),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf88 : Bracket :=
  ⟨886, 887, (Int.negSucc 316737220012977095), (Int.negSucc 316737220012977082), (Int.ofNat 166175015537785198), (Int.ofNat 166175015537785216),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf89 : Bracket :=
  ⟨897, 898, (Int.ofNat 126649715757965826), (Int.ofNat 126649715757965843), (Int.negSucc 273633458302881961), (Int.negSucc 273633458302881954),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf90 : Bracket :=
  ⟨912, 913, (Int.negSucc 27694860126575159), (Int.negSucc 27694860126575156), (Int.ofNat 140007904298860148), (Int.ofNat 140007904298860165),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf91 : Bracket :=
  ⟨922, 923, (Int.ofNat 38263229832093377), (Int.ofNat 38263229832093388), (Int.negSucc 1961577508104278), (Int.negSucc 1961577508104271),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf92 : Bracket :=
  ⟨925, 926, (Int.negSucc 20089723291494498), (Int.negSucc 20089723291494480), (Int.ofNat 177183368361344), (Int.ofNat 177183368361363),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf93 : Bracket :=
  ⟨937, 938, (Int.ofNat 42832935272677481), (Int.ofNat 42832935272677493), (Int.negSucc 13899522890892974), (Int.negSucc 13899522890892955),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf94 : Bracket :=
  ⟨949, 950, (Int.negSucc 2831753428799421), (Int.negSucc 2831753428799403), (Int.ofNat 13370372346679733), (Int.ofNat 13370372346679742),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf95 : Bracket :=
  ⟨953, 954, (Int.ofNat 338788507060191), (Int.ofNat 338788507060206), (Int.negSucc 18316287037531561), (Int.negSucc 18316287037531552),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf96 : Bracket :=
  ⟨959, 960, (Int.negSucc 11463992413950616), (Int.negSucc 11463992413950598), (Int.ofNat 41186002202604749), (Int.ofNat 41186002202604752),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf97 : Bracket :=
  ⟨978, 979, (Int.ofNat 74033309489372755), (Int.ofNat 74033309489372767), (Int.negSucc 38470257385693904), (Int.negSucc 38470257385693897),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf98 : Bracket :=
  ⟨988, 989, (Int.negSucc 15260116055913639), (Int.negSucc 15260116055913636), (Int.ofNat 34924689875517379), (Int.ofNat 34924689875517395),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf99 : Bracket :=
  ⟨997, 998, (Int.ofNat 2715597305614971), (Int.ofNat 2715597305614985), (Int.negSucc 20870670061747577), (Int.negSucc 20870670061747557),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf100 : Bracket :=
  ⟨1002, 1003, (Int.negSucc 5814468540420591), (Int.negSucc 5814468540420578), (Int.ofNat 26459626455423662), (Int.ofNat 26459626455423675),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf101 : Bracket :=
  ⟨1015, 1016, (Int.ofNat 17791253369981245), (Int.ofNat 17791253369981258), (Int.negSucc 22503646241960894), (Int.negSucc 22503646241960891),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf102 : Bracket :=
  ⟨1021, 1022, (Int.negSucc 28294985849803935), (Int.negSucc 28294985849803929), (Int.ofNat 12124381889664797), (Int.ofNat 12124381889664815),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf103 : Bracket :=
  ⟨1033, 1034, (Int.ofNat 17790792936021751), (Int.ofNat 17790792936021760), (Int.negSucc 44727611849014636), (Int.negSucc 44727611849014621),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf104 : Bracket :=
  ⟨1042, 1043, (Int.negSucc 43589671657973545), (Int.negSucc 43589671657973534), (Int.ofNat 13840915358351151), (Int.ofNat 13840915358351161),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf105 : Bracket :=
  ⟨1050, 1051, (Int.ofNat 29707046121999308), (Int.ofNat 29707046121999317), (Int.negSucc 39975704839960768), (Int.negSucc 39975704839960761),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf106 : Bracket :=
  ⟨1059, 1060, (Int.negSucc 35231539227273849), (Int.negSucc 35231539227273830), (Int.ofNat 115219337820736515), (Int.ofNat 115219337820736530),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf107 : Bracket :=
  ⟨1074, 1075, (Int.ofNat 144955478897020762), (Int.ofNat 144955478897020780), (Int.negSucc 97722271862378481), (Int.negSucc 97722271862378467),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf108 : Bracket :=
  ⟨1088, 1089, (Int.negSucc 2659977539846718), (Int.negSucc 2659977539846715), (Int.ofNat 21313028456266566), (Int.ofNat 21313028456266585),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf109 : Bracket :=
  ⟨1089, 1090, (Int.ofNat 21313028456266566), (Int.ofNat 21313028456266585), (Int.negSucc 2643168416949186), (Int.negSucc 2643168416949174),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf110 : Bracket :=
  ⟨1106, 1107, (Int.negSucc 88664125562437036), (Int.negSucc 88664125562437026), (Int.ofNat 130175078615804917), (Int.ofNat 130175078615804933),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf111 : Bracket :=
  ⟨1119, 1120, (Int.ofNat 37327189764757112), (Int.ofNat 37327189764757124), (Int.negSucc 32956406327439704), (Int.negSucc 32956406327439701),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf112 : Bracket :=
  ⟨1124, 1125, (Int.negSucc 28782509443006250), (Int.negSucc 28782509443006236), (Int.ofNat 25985881789339629), (Int.ofNat 25985881789339641),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf113 : Bracket :=
  ⟨1135, 1136, (Int.ofNat 21661961720629302), (Int.ofNat 21661961720629320), (Int.negSucc 35758513890367543), (Int.negSucc 35758513890367537),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf114 : Bracket :=
  ⟨1141, 1142, (Int.negSucc 30538579479480154), (Int.negSucc 30538579479480138), (Int.ofNat 37829432227434400), (Int.ofNat 37829432227434413),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf115 : Bracket :=
  ⟨1151, 1152, (Int.ofNat 130328800721135790), (Int.ofNat 130328800721135808), (Int.negSucc 14226425851809980), (Int.negSucc 14226425851809978),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf116 : Bracket :=
  ⟨1165, 1166, (Int.negSucc 17777548162146050), (Int.negSucc 17777548162146036), (Int.ofNat 177860829019652321), (Int.ofNat 177860829019652334),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf117 : Bracket :=
  ⟨1176, 1177, (Int.ofNat 5484041443157841), (Int.ofNat 5484041443157846), (Int.negSucc 134159748968301537), (Int.negSucc 134159748968301520),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf118 : Bracket :=
  ⟨1184, 1185, (Int.negSucc 57389346458826249), (Int.negSucc 57389346458826245), (Int.ofNat 84305049819815806), (Int.ofNat 84305049819815812),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf119 : Bracket :=
  ⟨1195, 1196, (Int.ofNat 115437056561755889), (Int.ofNat 115437056561755907), (Int.negSucc 24392356993572507), (Int.negSucc 24392356993572500),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf120 : Bracket :=
  ⟨1204, 1205, (Int.negSucc 17717768282699331), (Int.negSucc 17717768282699314), (Int.ofNat 112526683422544815), (Int.ofNat 112526683422544830),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf121 : Bracket :=
  ⟨1212, 1213, (Int.ofNat 27215940752835359), (Int.ofNat 27215940752835362), (Int.negSucc 209411969123668825), (Int.negSucc 209411969123668809),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf122 : Bracket :=
  ⟨1229, 1230, (Int.negSucc 123154043954410479), (Int.negSucc 123154043954410471), (Int.ofNat 153721112712949079), (Int.ofNat 153721112712949093),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf123 : Bracket :=
  ⟨1239, 1240, (Int.ofNat 122124357632224150), (Int.ofNat 122124357632224160), (Int.negSucc 32846307371610957), (Int.negSucc 32846307371610953),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf124 : Bracket :=
  ⟨1249, 1250, (Int.negSucc 36823226560055422), (Int.negSucc 36823226560055404), (Int.ofNat 66904922136727030), (Int.ofNat 66904922136727045),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf125 : Bracket :=
  ⟨1261, 1262, (Int.ofNat 7821777129340409), (Int.ofNat 7821777129340418), (Int.negSucc 35611595947029647), (Int.negSucc 35611595947029627),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf126 : Bracket :=
  ⟨1268, 1269, (Int.negSucc 19000750969720142), (Int.negSucc 19000750969720139), (Int.ofNat 5502096008638397), (Int.ofNat 5502096008638415),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf127 : Bracket :=
  ⟨1275, 1276, (Int.ofNat 6346348665655), (Int.ofNat 6346348665671), (Int.negSucc 22159069010417557), (Int.negSucc 22159069010417553),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf128 : Bracket :=
  ⟨1281, 1282, (Int.negSucc 31999461133318539), (Int.negSucc 31999461133318527), (Int.ofNat 1289326300898776), (Int.ofNat 1289326300898786),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf129 : Bracket :=
  ⟨1293, 1294, (Int.ofNat 65292203582283386), (Int.ofNat 65292203582283393), (Int.negSucc 23418132923378134), (Int.negSucc 23418132923378121),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf130 : Bracket :=
  ⟨1307, 1308, (Int.negSucc 14863004939407386), (Int.negSucc 14863004939407371), (Int.ofNat 51771932580153410), (Int.ofNat 51771932580153414),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf131 : Bracket :=
  ⟨1313, 1314, (Int.ofNat 50781556507012529), (Int.ofNat 50781556507012544), (Int.negSucc 15208987683425005), (Int.negSucc 15208987683424996),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf132 : Bracket :=
  ⟨1328, 1329, (Int.negSucc 37255629574866989), (Int.negSucc 37255629574866979), (Int.ofNat 13827218482928295), (Int.ofNat 13827218482928311),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf133 : Bracket :=
  ⟨1334, 1335, (Int.ofNat 3833345284838832), (Int.ofNat 3833345284838847), (Int.negSucc 40069857440851319), (Int.negSucc 40069857440851311),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf134 : Bracket :=
  ⟨1346, 1347, (Int.negSucc 13673726193665836), (Int.negSucc 13673726193665820), (Int.ofNat 28499920032683358), (Int.ofNat 28499920032683366),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf135 : Bracket :=
  ⟨1354, 1355, (Int.ofNat 17131535594012166), (Int.ofNat 17131535594012180), (Int.negSucc 9380060959280039), (Int.negSucc 9380060959280022),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf136 : Bracket :=
  ⟨1359, 1360, (Int.negSucc 16122377159632547), (Int.negSucc 16122377159632540), (Int.ofNat 18366295518326226), (Int.ofNat 18366295518326230),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf137 : Bracket :=
  ⟨1373, 1374, (Int.ofNat 65357965245708833), (Int.ofNat 65357965245708847), (Int.negSucc 20216864972712338), (Int.negSucc 20216864972712323),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf138 : Bracket :=
  ⟨1384, 1385, (Int.negSucc 31619816163919177), (Int.negSucc 31619816163919165), (Int.ofNat 12041478771410855), (Int.ofNat 12041478771410868),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf139 : Bracket :=
  ⟨1389, 1390, (Int.ofNat 3554747395974241), (Int.ofNat 3554747395974249), (Int.negSucc 47695331296431685), (Int.negSucc 47695331296431673),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf140 : Bracket :=
  ⟨1400, 1401, (Int.negSucc 60490814401371903), (Int.negSucc 60490814401371899), (Int.ofNat 46474137648250928), (Int.ofNat 46474137648250942),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf141 : Bracket :=
  ⟨1407, 1408, (Int.ofNat 82489080222441781), (Int.ofNat 82489080222441787), (Int.negSucc 106758402102702799), (Int.negSucc 106758402102702797),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf142 : Bracket :=
  ⟨1425, 1426, (Int.negSucc 66478815626341392), (Int.negSucc 66478815626341374), (Int.ofNat 263477969903599389), (Int.ofNat 263477969903599397),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf143 : Bracket :=
  ⟨1431, 1432, (Int.ofNat 300099728715795140), (Int.ofNat 300099728715795159), (Int.negSucc 40688372526421657), (Int.negSucc 40688372526421645),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf144 : Bracket :=
  ⟨1446, 1447, (Int.negSucc 2260794235255688), (Int.negSucc 2260794235255675), (Int.ofNat 717407955358690611), (Int.ofNat 717407955358690627),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf145 : Bracket :=
  ⟨1463, 1464, (Int.ofNat 79390631728518207), (Int.ofNat 79390631728518226), (Int.negSucc 155876870837527739), (Int.negSucc 155876870837527735),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf146 : Bracket :=
  ⟨1471, 1472, (Int.negSucc 48110101132765919), (Int.negSucc 48110101132765907), (Int.ofNat 49073822005707201), (Int.ofNat 49073822005707204),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf147 : Bracket :=
  ⟨1478, 1479, (Int.ofNat 45508311577983112), (Int.ofNat 45508311577983132), (Int.negSucc 29237741142266435), (Int.negSucc 29237741142266418),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf148 : Bracket :=
  ⟨1488, 1489, (Int.negSucc 18073414762526953), (Int.negSucc 18073414762526950), (Int.ofNat 47000431470646783), (Int.ofNat 47000431470646799),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf149 : Bracket :=
  ⟨1495, 1496, (Int.ofNat 10611603917977258), (Int.ofNat 10611603917977271), (Int.negSucc 75617485983254661), (Int.negSucc 75617485983254648),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf150 : Bracket :=
  ⟨1507, 1508, (Int.negSucc 48224740197775130), (Int.negSucc 48224740197775112), (Int.ofNat 89021657563391767), (Int.ofNat 89021657563391781),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf151 : Bracket :=
  ⟨1521, 1522, (Int.ofNat 35416681036729895), (Int.ofNat 35416681036729905), (Int.negSucc 32703685172713248), (Int.negSucc 32703685172713241),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf152 : Bracket :=
  ⟨1529, 1530, (Int.negSucc 11695426841487074), (Int.negSucc 11695426841487056), (Int.ofNat 24183876312707169), (Int.ofNat 24183876312707183),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf153 : Bracket :=
  ⟨1538, 1539, (Int.ofNat 4776216503742709), (Int.ofNat 4776216503742716), (Int.negSucc 16253360394922305), (Int.negSucc 16253360394922288),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf154 : Bracket :=
  ⟨1544, 1545, (Int.negSucc 6971323135921999), (Int.negSucc 6971323135921996), (Int.ofNat 14989552595501885), (Int.ofNat 14989552595501893),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf155 : Bracket :=
  ⟨1552, 1553, (Int.ofNat 23065123487734863), (Int.ofNat 23065123487734866), (Int.negSucc 11847621149351340), (Int.negSucc 11847621149351327),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf156 : Bracket :=
  ⟨1562, 1563, (Int.negSucc 95646555557274), (Int.negSucc 95646555557257), (Int.ofNat 70190798572548319), (Int.ofNat 70190798572548330),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf157 : Bracket :=
  ⟨1576, 1577, (Int.ofNat 3129094309642681), (Int.ofNat 3129094309642685), (Int.negSucc 25359674139287996), (Int.negSucc 25359674139287978),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf158 : Bracket :=
  ⟨1578, 1579, (Int.negSucc 26184490950563822), (Int.negSucc 26184490950563808), (Int.ofNat 4203601381132982), (Int.ofNat 4203601381133001),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf159 : Bracket :=
  ⟨1594, 1595, (Int.ofNat 15673762985239618), (Int.ofNat 15673762985239631), (Int.negSucc 242505023833753246), (Int.negSucc 242505023833753234),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf160 : Bracket :=
  ⟨1610, 1611, (Int.negSucc 49298378219164009), (Int.negSucc 49298378219163992), (Int.ofNat 66502919588357690), (Int.ofNat 66502919588357702),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf161 : Bracket :=
  ⟨1617, 1618, (Int.ofNat 16571897467730311), (Int.ofNat 16571897467730325), (Int.negSucc 58161913341318530), (Int.negSucc 58161913341318513),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf162 : Bracket :=
  ⟨1626, 1627, (Int.negSucc 1126002573202075), (Int.negSucc 1126002573202056), (Int.ofNat 86503159494043963), (Int.ofNat 86503159494043973),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf163 : Bracket :=
  ⟨1640, 1641, (Int.ofNat 4238046456469895), (Int.ofNat 4238046456469900), (Int.negSucc 21271621681080264), (Int.negSucc 21271621681080248),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf164 : Bracket :=
  ⟨1644, 1645, (Int.negSucc 74961876609241), (Int.negSucc 74961876609231), (Int.ofNat 30681623658163251), (Int.ofNat 30681623658163261),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf165 : Bracket :=
  ⟨1653, 1654, (Int.ofNat 32762196330414669), (Int.ofNat 32762196330414678), (Int.negSucc 23237124434164978), (Int.negSucc 23237124434164962),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf166 : Bracket :=
  ⟨1663, 1664, (Int.negSucc 33296147701574858), (Int.negSucc 33296147701574845), (Int.ofNat 53823521612296443), (Int.ofNat 53823521612296446),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf167 : Bracket :=
  ⟨1677, 1678, (Int.ofNat 13026676293668095), (Int.ofNat 13026676293668102), (Int.negSucc 43406110297084172), (Int.negSucc 43406110297084158),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf168 : Bracket :=
  ⟨1684, 1685, (Int.negSucc 2827870328090984), (Int.negSucc 2827870328090970), (Int.ofNat 37826319357518808), (Int.ofNat 37826319357518824),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf169 : Bracket :=
  ⟨1690, 1691, (Int.ofNat 37616946199144636), (Int.ofNat 37616946199144654), (Int.negSucc 19571800997707846), (Int.negSucc 19571800997707839),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf170 : Bracket :=
  ⟨1702, 1703, (Int.negSucc 59721866346064764), (Int.negSucc 59721866346064754), (Int.ofNat 50137359012459262), (Int.ofNat 50137359012459277),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf171 : Bracket :=
  ⟨1709, 1710, (Int.ofNat 129357930307593650), (Int.ofNat 129357930307593667), (Int.negSucc 20641108240066008), (Int.negSucc 20641108240065992),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf172 : Bracket :=
  ⟨1724, 1725, (Int.negSucc 167644497655204681), (Int.negSucc 167644497655204678), (Int.ofNat 188202498852837467), (Int.ofNat 188202498852837484),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf173 : Bracket :=
  ⟨1736, 1737, (Int.ofNat 50003201616937675), (Int.ofNat 50003201616937679), (Int.negSucc 272345787402769916), (Int.negSucc 272345787402769910),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf174 : Bracket :=
  ⟨1746, 1747, (Int.negSucc 295788891327830392), (Int.negSucc 295788891327830382), (Int.ofNat 3071447359231457), (Int.ofNat 3071447359231465),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf175 : Bracket :=
  ⟨1761, 1762, (Int.ofNat 85114766706623398), (Int.ofNat 85114766706623407), (Int.negSucc 19163618868328166), (Int.negSucc 19163618868328153),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf176 : Bracket :=
  ⟨1766, 1767, (Int.negSucc 45419663312416007), (Int.negSucc 45419663312415987), (Int.ofNat 15211886376316195), (Int.ofNat 15211886376316210),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf177 : Bracket :=
  ⟨1774, 1775, (Int.ofNat 23086241474831080), (Int.ofNat 23086241474831097), (Int.negSucc 90612943717956858), (Int.negSucc 90612943717956843),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf178 : Bracket :=
  ⟨1787, 1788, (Int.negSucc 132073801059384804), (Int.negSucc 132073801059384798), (Int.ofNat 20005445591790005), (Int.ofNat 20005445591790007),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf179 : Bracket :=
  ⟨1797, 1798, (Int.ofNat 77249607410663426), (Int.ofNat 77249607410663430), (Int.negSucc 9730036372318200), (Int.negSucc 9730036372318181),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf180 : Bracket :=
  ⟨1802, 1803, (Int.negSucc 57035638236318587), (Int.negSucc 57035638236318577), (Int.ofNat 36613999984672535), (Int.ofNat 36613999984672550),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf181 : Bracket :=
  ⟨1819, 1820, (Int.ofNat 22926145848951187), (Int.ofNat 22926145848951197), (Int.negSucc 178776737929341819), (Int.negSucc 178776737929341816),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf182 : Bracket :=
  ⟨1828, 1829, (Int.negSucc 2194757925338190), (Int.negSucc 2194757925338186), (Int.ofNat 188324220356320536), (Int.ofNat 188324220356320552),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf183 : Bracket :=
  ⟨1842, 1843, (Int.ofNat 34875281903993006), (Int.ofNat 34875281903993022), (Int.negSucc 81351187533292676), (Int.negSucc 81351187533292663),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf184 : Bracket :=
  ⟨1853, 1854, (Int.negSucc 14421322864824853), (Int.negSucc 14421322864824845), (Int.ofNat 18080254990271548), (Int.ofNat 18080254990271566),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf185 : Bracket :=
  ⟨1859, 1860, (Int.ofNat 9230789197725085), (Int.ofNat 9230789197725102), (Int.negSucc 8467357128465834), (Int.negSucc 8467357128465830),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf186 : Bracket :=
  ⟨1864, 1865, (Int.negSucc 13369710195289047), (Int.negSucc 13369710195289044), (Int.ofNat 9829400158248319), (Int.ofNat 9829400158248335),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf187 : Bracket :=
  ⟨1880, 1881, (Int.ofNat 4802800894972669), (Int.ofNat 4802800894972672), (Int.negSucc 20657562451359146), (Int.negSucc 20657562451359141),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf188 : Bracket :=
  ⟨1886, 1887, (Int.negSucc 15505924628462610), (Int.negSucc 15505924628462591), (Int.ofNat 2652023829739872), (Int.ofNat 2652023829739884),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf189 : Bracket :=
  ⟨1896, 1897, (Int.ofNat 8751118837235606), (Int.ofNat 8751118837235609), (Int.negSucc 380933340246419), (Int.negSucc 380933340246408),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf190 : Bracket :=
  ⟨1899, 1900, (Int.negSucc 3510258869737821), (Int.negSucc 3510258869737808), (Int.ofNat 3838028812302688), (Int.ofNat 3838028812302696),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf191 : Bracket :=
  ⟨1908, 1909, (Int.ofNat 28860159662906397), (Int.ofNat 28860159662906400), (Int.negSucc 9567205607797037), (Int.negSucc 9567205607797029),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf192 : Bracket :=
  ⟨1919, 1920, (Int.negSucc 98244972535490414), (Int.negSucc 98244972535490397), (Int.ofNat 26648173009154084), (Int.ofNat 26648173009154086),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf193 : Bracket :=
  ⟨1939, 1940, (Int.ofNat 13470969530822315), (Int.ofNat 13470969530822327), (Int.negSucc 26848611870666913), (Int.negSucc 26848611870666910),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf194 : Bracket :=
  ⟨1941, 1942, (Int.negSucc 30111523767259655), (Int.negSucc 30111523767259639), (Int.ofNat 127712842593307), (Int.ofNat 127712842593317),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf195 : Bracket :=
  ⟨1954, 1955, (Int.ofNat 46167123604579122), (Int.ofNat 46167123604579140), (Int.negSucc 65324315409922215), (Int.negSucc 65324315409922202),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf196 : Bracket :=
  ⟨1963, 1964, (Int.negSucc 48121989797334816), (Int.negSucc 48121989797334801), (Int.ofNat 61134901973235597), (Int.ofNat 61134901973235602),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf197 : Bracket :=
  ⟨1971, 1972, (Int.ofNat 15527152371480936), (Int.ofNat 15527152371480951), (Int.negSucc 171083917672619930), (Int.negSucc 171083917672619928),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf198 : Bracket :=
  ⟨1986, 1987, (Int.negSucc 39084467092197118), (Int.negSucc 39084467092197111), (Int.ofNat 228330441463386360), (Int.ofNat 228330441463386365),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf199 : Bracket :=
  ⟨1996, 1997, (Int.ofNat 78992499668176471), (Int.ofNat 78992499668176484), (Int.negSucc 124498473408890054), (Int.negSucc 124498473408890042),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf200 : Bracket :=
  ⟨2004, 2005, (Int.negSucc 165343509348519064), (Int.negSucc 165343509348519061), (Int.ofNat 53184236324731205), (Int.ofNat 53184236324731223),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf201 : Bracket :=
  ⟨2016, 2017, (Int.ofNat 55687743922658484), (Int.ofNat 55687743922658487), (Int.negSucc 297043398643061000), (Int.negSucc 297043398643060988),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf202 : Bracket :=
  ⟨2035, 2036, (Int.negSucc 24725140188464116), (Int.negSucc 24725140188464110), (Int.ofNat 19032812427005276), (Int.ofNat 19032812427005279),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf203 : Bracket :=
  ⟨2039, 2040, (Int.ofNat 12842320019626498), (Int.ofNat 12842320019626502), (Int.negSucc 2350324301045595), (Int.negSucc 2350324301045593),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf204 : Bracket :=
  ⟨2042, 2043, (Int.negSucc 483327842698601), (Int.negSucc 483327842698584), (Int.ofNat 25995947483749408), (Int.ofNat 25995947483749412),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf205 : Bracket :=
  ⟨2054, 2055, (Int.ofNat 73950319004578671), (Int.ofNat 73950319004578686), (Int.negSucc 74557759113546722), (Int.negSucc 74557759113546719),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf206 : Bracket :=
  ⟨2066, 2067, (Int.negSucc 133987332708650419), (Int.negSucc 133987332708650406), (Int.ofNat 104719277341854252), (Int.ofNat 104719277341854260),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf207 : Bracket :=
  ⟨2081, 2082, (Int.ofNat 124947943344952762), (Int.ofNat 124947943344952766), (Int.negSucc 24699807524495120), (Int.negSucc 24699807524495105),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf208 : Bracket :=
  ⟨2091, 2092, (Int.negSucc 16575638395203512), (Int.negSucc 16575638395203503), (Int.ofNat 32175123378229612), (Int.ofNat 32175123378229615),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf209 : Bracket :=
  ⟨2096, 2097, (Int.ofNat 29746871063289273), (Int.ofNat 29746871063289275), (Int.negSucc 17536844623458657), (Int.negSucc 17536844623458653),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf210 : Bracket :=
  ⟨2111, 2112, (Int.negSucc 16388081469799631), (Int.negSucc 16388081469799623), (Int.ofNat 7040751628387300), (Int.ofNat 7040751628387302),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf211 : Bracket :=
  ⟨2115, 2116, (Int.ofNat 6462622031442227), (Int.ofNat 6462622031442235), (Int.negSucc 9035097259685894), (Int.negSucc 9035097259685891),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf212 : Bracket :=
  ⟨2121, 2122, (Int.negSucc 5924775337009792), (Int.negSucc 5924775337009786), (Int.ofNat 31317321497939792), (Int.ofNat 31317321497939804),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf213 : Bracket :=
  ⟨2131, 2132, (Int.ofNat 108171030238830120), (Int.ofNat 108171030238830126), (Int.negSucc 20519314184496206), (Int.negSucc 20519314184496202),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf214 : Bracket :=
  ⟨2151, 2152, (Int.negSucc 31042044224355472), (Int.negSucc 31042044224355456), (Int.ofNat 85767924262182481), (Int.ofNat 85767924262182496),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf215 : Bracket :=
  ⟨2158, 2159, (Int.ofNat 48203000693073161), (Int.ofNat 48203000693073169), (Int.negSucc 25235274571005512), (Int.negSucc 25235274571005505),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf216 : Bracket :=
  ⟨2168, 2169, (Int.negSucc 35753419256815213), (Int.negSucc 35753419256815210), (Int.ofNat 10411245762542253), (Int.ofNat 10411245762542268),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf217 : Bracket :=
  ⟨2173, 2174, (Int.ofNat 27099472034914118), (Int.ofNat 27099472034914128), (Int.negSucc 22519751876648603), (Int.negSucc 22519751876648592),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf218 : Bracket :=
  ⟨2190, 2191, (Int.negSucc 40374589675656522), (Int.negSucc 40374589675656503), (Int.ofNat 4596530546833405), (Int.ofNat 4596530546833415),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf219 : Bracket :=
  ⟨2194, 2195, (Int.ofNat 15323038062012329), (Int.ofNat 15323038062012341), (Int.negSucc 17052920223502118), (Int.negSucc 17052920223502106),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf220 : Bracket :=
  ⟨2204, 2205, (Int.negSucc 68085629406984796), (Int.negSucc 68085629406984781), (Int.ofNat 8288933579800087), (Int.ofNat 8288933579800097),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf221 : Bracket :=
  ⟨2218, 2219, (Int.ofNat 5631432065585125), (Int.ofNat 5631432065585136), (Int.negSucc 53371598489971830), (Int.negSucc 53371598489971820),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf222 : Bracket :=
  ⟨2224, 2225, (Int.negSucc 31456655143283603), (Int.negSucc 31456655143283600), (Int.ofNat 30339222884877790), (Int.ofNat 30339222884877797),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf223 : Bracket :=
  ⟨2236, 2237, (Int.ofNat 42869940913206857), (Int.ofNat 42869940913206860), (Int.negSucc 31016311931329804), (Int.negSucc 31016311931329785),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf224 : Bracket :=
  ⟨2243, 2244, (Int.negSucc 62203302380912855), (Int.negSucc 62203302380912839), (Int.ofNat 18270798572450513), (Int.ofNat 18270798572450516),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf225 : Bracket :=
  ⟨2258, 2259, (Int.ofNat 44834978621609975), (Int.ofNat 44834978621609990), (Int.negSucc 43283842926588395), (Int.negSucc 43283842926588389),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf226 : Bracket :=
  ⟨2268, 2269, (Int.negSucc 7007494282904665), (Int.negSucc 7007494282904662), (Int.ofNat 31781654888741646), (Int.ofNat 31781654888741655),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf227 : Bracket :=
  ⟨2275, 2276, (Int.ofNat 13582294973253430), (Int.ofNat 13582294973253445), (Int.negSucc 14122451047446462), (Int.negSucc 14122451047446458),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf228 : Bracket :=
  ⟨2283, 2284, (Int.negSucc 7140982088207495), (Int.negSucc 7140982088207489), (Int.ofNat 9478830498053229), (Int.ofNat 9478830498053232),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf229 : Bracket :=
  ⟨2286, 2287, (Int.ofNat 10349362835476826), (Int.ofNat 10349362835476843), (Int.negSucc 13611761484499489), (Int.negSucc 13611761484499475),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf230 : Bracket :=
  ⟨2297, 2298, (Int.negSucc 184286470063680226), (Int.negSucc 184286470063680215), (Int.ofNat 13802144892659005), (Int.ofNat 13802144892659014),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf231 : Bracket :=
  ⟨2315, 2316, (Int.ofNat 347754729018835475), (Int.ofNat 347754729018835493), (Int.negSucc 101732312478110912), (Int.negSucc 101732312478110908),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf232 : Bracket :=
  ⟨2322, 2323, (Int.negSucc 219459460507040062), (Int.negSucc 219459460507040050), (Int.ofNat 297686510028769704), (Int.ofNat 297686510028769718),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf233 : Bracket :=
  ⟨2340, 2341, (Int.ofNat 472863896896084690), (Int.ofNat 472863896896084694), (Int.negSucc 293332053799973549), (Int.negSucc 293332053799973536),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf234 : Bracket :=
  ⟨2352, 2353, (Int.negSucc 337699331043837319), (Int.negSucc 337699331043837310), (Int.ofNat 32063479086823428), (Int.ofNat 32063479086823439),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf235 : Bracket :=
  ⟨2362, 2363, (Int.ofNat 170997658772335459), (Int.ofNat 170997658772335469), (Int.negSucc 25786949098071594), (Int.negSucc 25786949098071585),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf236 : Bracket :=
  ⟨2374, 2375, (Int.negSucc 32063292829451495), (Int.negSucc 32063292829451488), (Int.ofNat 46968873591694564), (Int.ofNat 46968873591694569),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf237 : Bracket :=
  ⟨2383, 2384, (Int.ofNat 6087567070062584), (Int.ofNat 6087567070062593), (Int.negSucc 19259028916063964), (Int.negSucc 19259028916063957),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf238 : Bracket :=
  ⟨2387, 2388, (Int.negSucc 18414157453512861), (Int.negSucc 18414157453512846), (Int.ofNat 6116368273231514), (Int.ofNat 6116368273231517),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf239 : Bracket :=
  ⟨2397, 2398, (Int.ofNat 43360750771976182), (Int.ofNat 43360750771976192), (Int.negSucc 8865118509282406), (Int.negSucc 8865118509282399),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf240 : Bracket :=
  ⟨2411, 2412, (Int.negSucc 20274242172208753), (Int.negSucc 20274242172208741), (Int.ofNat 1314245633582891), (Int.ofNat 1314245633582894),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf241 : Bracket :=
  ⟨2414, 2415, (Int.ofNat 7094855852702604), (Int.ofNat 7094855852702619), (Int.negSucc 8008395909229752), (Int.negSucc 8008395909229747),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf242 : Bracket :=
  ⟨2425, 2426, (Int.negSucc 16013713264788317), (Int.negSucc 16013713264788303), (Int.ofNat 42246175972832335), (Int.ofNat 42246175972832351),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf243 : Bracket :=
  ⟨2437, 2438, (Int.ofNat 15075452738889390), (Int.ofNat 15075452738889398), (Int.negSucc 52253182389507220), (Int.negSucc 52253182389507214),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf244 : Bracket :=
  ⟨2447, 2448, (Int.negSucc 32892546176029678), (Int.negSucc 32892546176029660), (Int.ofNat 10071571016012658), (Int.ofNat 10071571016012660),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf245 : Bracket :=
  ⟨2452, 2453, (Int.ofNat 24843294759300145), (Int.ofNat 24843294759300148), (Int.negSucc 23587023641283820), (Int.negSucc 23587023641283811),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf246 : Bracket :=
  ⟨2468, 2469, (Int.negSucc 57702175381669264), (Int.negSucc 57702175381669254), (Int.ofNat 37754278598497223), (Int.ofNat 37754278598497235),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf247 : Bracket :=
  ⟨2477, 2478, (Int.ofNat 39950431915456615), (Int.ofNat 39950431915456629), (Int.negSucc 26904278465288805), (Int.negSucc 26904278465288794),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf248 : Bracket :=
  ⟨2489, 2490, (Int.negSucc 5015460084458454), (Int.negSucc 5015460084458440), (Int.ofNat 16449826405749328), (Int.ofNat 16449826405749340),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf249 : Bracket :=
  ⟨2492, 2493, (Int.ofNat 16213423512334898), (Int.ofNat 16213423512334905), (Int.negSucc 5322174740777091), (Int.negSucc 5322174740777082),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf250 : Bracket :=
  ⟨2503, 2504, (Int.negSucc 46908166288069104), (Int.negSucc 46908166288069097), (Int.ofNat 24354646868583745), (Int.ofNat 24354646868583748),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf251 : Bracket :=
  ⟨2513, 2514, (Int.ofNat 96881357566337040), (Int.ofNat 96881357566337046), (Int.negSucc 2867568037755588), (Int.negSucc 2867568037755583),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf252 : Bracket :=
  ⟨2525, 2526, (Int.negSucc 86446124916356161), (Int.negSucc 86446124916356155), (Int.ofNat 10343684925624562), (Int.ofNat 10343684925624580),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf253 : Bracket :=
  ⟨2531, 2532, (Int.ofNat 80068047152265704), (Int.ofNat 80068047152265722), (Int.negSucc 25112906937480121), (Int.negSucc 25112906937480119),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf254 : Bracket :=
  ⟨2549, 2550, (Int.negSucc 45440414421062834), (Int.negSucc 45440414421062817), (Int.ofNat 70912341387430124), (Int.ofNat 70912341387430135),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf255 : Bracket :=
  ⟨2555, 2556, (Int.ofNat 48729993978628364), (Int.ofNat 48729993978628372), (Int.negSucc 38024184057733047), (Int.negSucc 38024184057733043),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf256 : Bracket :=
  ⟨2563, 2564, (Int.negSucc 83653269514097823), (Int.negSucc 83653269514097807), (Int.ofNat 45956133179871482), (Int.ofNat 45956133179871485),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf257 : Bracket :=
  ⟨2574, 2575, (Int.ofNat 114969534912217914), (Int.ofNat 114969534912217923), (Int.negSucc 152240873364977076), (Int.negSucc 152240873364977061),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf258 : Bracket :=
  ⟨2591, 2592, (Int.negSucc 2237091213228698), (Int.negSucc 2237091213228693), (Int.ofNat 132453639675813471), (Int.ofNat 132453639675813474),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf259 : Bracket :=
  ⟨2596, 2597, (Int.ofNat 98875576923514362), (Int.ofNat 98875576923514365), (Int.negSucc 22594200052249383), (Int.negSucc 22594200052249368),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf260 : Bracket :=
  ⟨2608, 2609, (Int.negSucc 70597388723328515), (Int.negSucc 70597388723328512), (Int.ofNat 98081611428866659), (Int.ofNat 98081611428866676),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf261 : Bracket :=
  ⟨2619, 2620, (Int.ofNat 60458401040116932), (Int.ofNat 60458401040116942), (Int.negSucc 63384867625082380), (Int.negSucc 63384867625082377),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf262 : Bracket :=
  ⟨2627, 2628, (Int.negSucc 71231073967767441), (Int.negSucc 71231073967767437), (Int.ofNat 43895521858348205), (Int.ofNat 43895521858348208),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf263 : Bracket :=
  ⟨2641, 2642, (Int.ofNat 2442523566433540), (Int.ofNat 2442523566433546), (Int.negSucc 43117218509005580), (Int.negSucc 43117218509005563),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf264 : Bracket :=
  ⟨2645, 2646, (Int.negSucc 19569275271292595), (Int.negSucc 19569275271292587), (Int.ofNat 34067547244090056), (Int.ofNat 34067547244090073),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf265 : Bracket :=
  ⟨2655, 2656, (Int.ofNat 60752735237736013), (Int.ofNat 60752735237736030), (Int.negSucc 64314524301679627), (Int.negSucc 64314524301679624),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf266 : Bracket :=
  ⟨2668, 2669, (Int.negSucc 80124981350548906), (Int.negSucc 80124981350548901), (Int.ofNat 75573237528500515), (Int.ofNat 75573237528500521),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf267 : Bracket :=
  ⟨2679, 2680, (Int.ofNat 61578043292565521), (Int.ofNat 61578043292565532), (Int.negSucc 38906840536894666), (Int.negSucc 38906840536894663),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf268 : Bracket :=
  ⟨2687, 2688, (Int.negSucc 45242192463155794), (Int.negSucc 45242192463155778), (Int.ofNat 30532724706991454), (Int.ofNat 30532724706991457),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf269 : Bracket :=
  ⟨2694, 2695, (Int.ofNat 60976906137247366), (Int.ofNat 60976906137247380), (Int.negSucc 48777955194627033), (Int.negSucc 48777955194627027),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf270 : Bracket :=
  ⟨2710, 2711, (Int.negSucc 89632127016285872), (Int.negSucc 89632127016285854), (Int.ofNat 45054537958839361), (Int.ofNat 45054537958839366),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf271 : Bracket :=
  ⟨2717, 2718, (Int.ofNat 37697778000026368), (Int.ofNat 37697778000026373), (Int.negSucc 84781371407063909), (Int.negSucc 84781371407063897),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf272 : Bracket :=
  ⟨2730, 2731, (Int.negSucc 101714516649053616), (Int.negSucc 101714516649053599), (Int.ofNat 34695364372252299), (Int.ofNat 34695364372252311),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf273 : Bracket :=
  ⟨2742, 2743, (Int.ofNat 41459111381658661), (Int.ofNat 41459111381658668), (Int.negSucc 13526523385510715), (Int.negSucc 13526523385510710),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf274 : Bracket :=
  ⟨2748, 2749, (Int.negSucc 25986001591198480), (Int.negSucc 25986001591198477), (Int.ofNat 11435209885841940), (Int.ofNat 11435209885841955),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf275 : Bracket :=
  ⟨2757, 2758, (Int.ofNat 39382886462327520), (Int.ofNat 39382886462327528), (Int.negSucc 8591971599068454), (Int.negSucc 8591971599068439),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf276 : Bracket :=
  ⟨2767, 2768, (Int.negSucc 22875043338066467), (Int.negSucc 22875043338066460), (Int.ofNat 39284075791822711), (Int.ofNat 39284075791822714),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf277 : Bracket :=
  ⟨2780, 2781, (Int.ofNat 9286056675334482), (Int.ofNat 9286056675334486), (Int.negSucc 31598396213082023), (Int.negSucc 31598396213082007),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf278 : Bracket :=
  ⟨2787, 2788, (Int.negSucc 14247556774073453), (Int.negSucc 14247556774073444), (Int.ofNat 19805671767199405), (Int.ofNat 19805671767199408),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf279 : Bracket :=
  ⟨2798, 2799, (Int.ofNat 13184400890127600), (Int.ofNat 13184400890127619), (Int.negSucc 9193644080567528), (Int.negSucc 9193644080567513),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf280 : Bracket :=
  ⟨2804, 2805, (Int.negSucc 4868037378876931), (Int.negSucc 4868037378876928), (Int.ofNat 15027413034431888), (Int.ofNat 15027413034431900),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf281 : Bracket :=
  ⟨2812, 2813, (Int.ofNat 15314334038483069), (Int.ofNat 15314334038483071), (Int.negSucc 14672658628475642), (Int.negSucc 14672658628475630),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf282 : Bracket :=
  ⟨2819, 2820, (Int.negSucc 43257763346000983), (Int.negSucc 43257763346000974), (Int.ofNat 9377064632158995), (Int.ofNat 9377064632158998),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf283 : Bracket :=
  ⟨2832, 2833, (Int.ofNat 22177085027130973), (Int.ofNat 22177085027130976), (Int.negSucc 158310699820478715), (Int.negSucc 158310699820478697),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf284 : Bracket :=
  ⟨2847, 2848, (Int.negSucc 25925906551855231), (Int.negSucc 25925906551855214), (Int.ofNat 77254550916039464), (Int.ofNat 77254550916039466),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf285 : Bracket :=
  ⟨2851, 2852, (Int.ofNat 52639989550041901), (Int.ofNat 52639989550041907), (Int.negSucc 74682314919584695), (Int.negSucc 74682314919584692),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf286 : Bracket :=
  ⟨2866, 2867, (Int.negSucc 241935450798329911), (Int.negSucc 241935450798329896), (Int.ofNat 82189489682474707), (Int.ofNat 82189489682474717),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf287 : Bracket :=
  ⟨2877, 2878, (Int.ofNat 141298045632145768), (Int.ofNat 141298045632145772), (Int.negSucc 120653523921119772), (Int.negSucc 120653523921119759),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf288 : Bracket :=
  ⟨2887, 2888, (Int.negSucc 181426886736977029), (Int.negSucc 181426886736977013), (Int.ofNat 33010411530033366), (Int.ofNat 33010411530033369),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf289 : Bracket :=
  ⟨2895, 2896, (Int.ofNat 197685101393673930), (Int.ofNat 197685101393673946), (Int.negSucc 38822466276383588), (Int.negSucc 38822466276383585),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf290 : Bracket :=
  ⟨2909, 2910, (Int.negSucc 157990765068168825), (Int.negSucc 157990765068168815), (Int.ofNat 163120230336610926), (Int.ofNat 163120230336610933),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf291 : Bracket :=
  ⟨2921, 2922, (Int.ofNat 24596229639158310), (Int.ofNat 24596229639158322), (Int.negSucc 164428051260469218), (Int.negSucc 164428051260469210),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf292 : Bracket :=
  ⟨2929, 2930, (Int.negSucc 117690026894282148), (Int.negSucc 117690026894282131), (Int.ofNat 37584665622903957), (Int.ofNat 37584665622903976),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf293 : Bracket :=
  ⟨2941, 2942, (Int.ofNat 54415231042986176), (Int.ofNat 54415231042986185), (Int.negSucc 19950282110146755), (Int.negSucc 19950282110146750),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf294 : Bracket :=
  ⟨2944, 2945, (Int.negSucc 50766707550111216), (Int.negSucc 50766707550111214), (Int.ofNat 5939735646579883), (Int.ofNat 5939735646579898),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf295 : Bracket :=
  ⟨2966, 2967, (Int.ofNat 71787498950611413), (Int.ofNat 71787498950611421), (Int.negSucc 19199573288568749), (Int.negSucc 19199573288568743),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf296 : Bracket :=
  ⟨2973, 2974, (Int.negSucc 9441665432890046), (Int.negSucc 9441665432890042), (Int.ofNat 24254653893914262), (Int.ofNat 24254653893914273),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf297 : Bracket :=
  ⟨2980, 2981, (Int.ofNat 10768407295563216), (Int.ofNat 10768407295563218), (Int.negSucc 16588655663109631), (Int.negSucc 16588655663109615),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf298 : Bracket :=
  ⟨2987, 2988, (Int.negSucc 19595093408655795), (Int.negSucc 19595093408655786), (Int.ofNat 14516986950771072), (Int.ofNat 14516986950771075),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf299 : Bracket :=
  ⟨2998, 2999, (Int.ofNat 21023427573413098), (Int.ofNat 21023427573413106), (Int.negSucc 26630486759991061), (Int.negSucc 26630486759991054),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf300 : Bracket :=
  ⟨3007, 3008, (Int.negSucc 41547693445285151), (Int.negSucc 41547693445285138), (Int.ofNat 4923623885976323), (Int.ofNat 4923623885976326),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf301 : Bracket :=
  ⟨3016, 3017, (Int.ofNat 42051524078485558), (Int.ofNat 42051524078485561), (Int.negSucc 11491018271575268), (Int.negSucc 11491018271575261),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf302 : Bracket :=
  ⟨3029, 3030, (Int.negSucc 28443736493179515), (Int.negSucc 28443736493179508), (Int.ofNat 7360754732786994), (Int.ofNat 7360754732787012),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf303 : Bracket :=
  ⟨3034, 3035, (Int.ofNat 12134589169707389), (Int.ofNat 12134589169707395), (Int.negSucc 22380239694587165), (Int.negSucc 22380239694587152),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf304 : Bracket :=
  ⟨3050, 3051, (Int.negSucc 11498343698052509), (Int.negSucc 11498343698052504), (Int.ofNat 365130194480168), (Int.ofNat 365130194480172),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf305 : Bracket :=
  ⟨3052, 3053, (Int.ofNat 2018323006790951), (Int.ofNat 2018323006790954), (Int.negSucc 3877906481067394), (Int.negSucc 3877906481067390),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf306 : Bracket :=
  ⟨3057, 3058, (Int.negSucc 60128954893250), (Int.negSucc 60128954893243), (Int.ofNat 37331366640340028), (Int.ofNat 37331366640340035),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf307 : Bracket :=
  ⟨3071, 3072, (Int.ofNat 228664606604180111), (Int.ofNat 228664606604180114), (Int.negSucc 148348216264564682), (Int.negSucc 148348216264564680),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf308 : Bracket :=
  ⟨3099, 3100, (Int.negSucc 22566467928123311), (Int.negSucc 22566467928123298), (Int.ofNat 16623687449846809), (Int.ofNat 16623687449846811),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf309 : Bracket :=
  ⟨3102, 3103, (Int.ofNat 9456636932114017), (Int.ofNat 9456636932114034), (Int.negSucc 14526119676387093), (Int.negSucc 14526119676387077),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf310 : Bracket :=
  ⟨3110, 3111, (Int.negSucc 10540327221190014), (Int.negSucc 10540327221190010), (Int.ofNat 13681914275234335), (Int.ofNat 13681914275234348),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf311 : Bracket :=
  ⟨3117, 3118, (Int.ofNat 16586427473910969), (Int.ofNat 16586427473910985), (Int.negSucc 2960307945713498), (Int.negSucc 2960307945713493),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf312 : Bracket :=
  ⟨3122, 3123, (Int.negSucc 21088578673227375), (Int.negSucc 21088578673227367), (Int.ofNat 2507236176071660), (Int.ofNat 2507236176071665),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf313 : Bracket :=
  ⟨3136, 3137, (Int.ofNat 56809232836153073), (Int.ofNat 56809232836153075), (Int.negSucc 7553829018204046), (Int.negSucc 7553829018204033),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf314 : Bracket :=
  ⟨3143, 3144, (Int.negSucc 49980220285056455), (Int.negSucc 49980220285056449), (Int.ofNat 13270183976335783), (Int.ofNat 13270183976335786),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf315 : Bracket :=
  ⟨3154, 3155, (Int.ofNat 16373930598332993), (Int.ofNat 16373930598333003), (Int.negSucc 103963275217823436), (Int.negSucc 103963275217823421),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf316 : Bracket :=
  ⟨3163, 3164, (Int.negSucc 170893925861008830), (Int.negSucc 170893925861008820), (Int.ofNat 3860522351618116), (Int.ofNat 3860522351618119),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf317 : Bracket :=
  ⟨3176, 3177, (Int.ofNat 64866774864402849), (Int.ofNat 64866774864402852), (Int.negSucc 220553017528357302), (Int.negSucc 220553017528357286),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf318 : Bracket :=
  ⟨3188, 3189, (Int.negSucc 140154210628707317), (Int.negSucc 140154210628707314), (Int.ofNat 130174665116615196), (Int.ofNat 130174665116615205),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf319 : Bracket :=
  ⟨3199, 3200, (Int.ofNat 107270195047530737), (Int.ofNat 107270195047530753), (Int.negSucc 88215164812731520), (Int.negSucc 88215164812731518),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf320 : Bracket :=
  ⟨3208, 3209, (Int.negSucc 131944322858336214), (Int.negSucc 131944322858336212), (Int.ofNat 23264779971393601), (Int.ofNat 23264779971393610),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf321 : Bracket :=
  ⟨3217, 3218, (Int.ofNat 135836149989958041), (Int.ofNat 135836149989958058), (Int.negSucc 27065834369733493), (Int.negSucc 27065834369733482),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf322 : Bracket :=
  ⟨3229, 3230, (Int.negSucc 53648916549688188), (Int.negSucc 53648916549688179), (Int.ofNat 115157000280437115), (Int.ofNat 115157000280437127),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf323 : Bracket :=
  ⟨3237, 3238, (Int.ofNat 166406565623513917), (Int.ofNat 166406565623513933), (Int.negSucc 6870602126948343), (Int.negSucc 6870602126948328),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf324 : Bracket :=
  ⟨3249, 3250, (Int.negSucc 196424697325628436), (Int.negSucc 196424697325628419), (Int.ofNat 24295550845366950), (Int.ofNat 24295550845366963),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf325 : Bracket :=
  ⟨3261, 3262, (Int.ofNat 110326334216934199), (Int.ofNat 110326334216934213), (Int.negSucc 67526291117890064), (Int.negSucc 67526291117890048),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf326 : Bracket :=
  ⟨3273, 3274, (Int.negSucc 15743833909834925), (Int.negSucc 15743833909834913), (Int.ofNat 68621167521595407), (Int.ofNat 68621167521595415),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf327 : Bracket :=
  ⟨3280, 3281, (Int.ofNat 49889789858973861), (Int.ofNat 49889789858973864), (Int.negSucc 13302854700154364), (Int.negSucc 13302854700154354),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf328 : Bracket :=
  ⟨3289, 3290, (Int.negSucc 7410560948694934), (Int.negSucc 7410560948694928), (Int.ofNat 72014082893014054), (Int.ofNat 72014082893014072),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf329 : Bracket :=
  ⟨3303, 3304, (Int.ofNat 14841708562558887), (Int.ofNat 14841708562558902), (Int.negSucc 24148598999376047), (Int.negSucc 24148598999376044),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf330 : Bracket :=
  ⟨3308, 3309, (Int.negSucc 14754699464008179), (Int.negSucc 14754699464008176), (Int.ofNat 20286662762610641), (Int.ofNat 20286662762610646),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf331 : Bracket :=
  ⟨3320, 3321, (Int.ofNat 22808104798730894), (Int.ofNat 22808104798730896), (Int.negSucc 6093719638079714), (Int.negSucc 6093719638079706),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf332 : Bracket :=
  ⟨3324, 3325, (Int.negSucc 20218570406124052), (Int.negSucc 20218570406124050), (Int.ofNat 3935888911026690), (Int.ofNat 3935888911026696),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf333 : Bracket :=
  ⟨3338, 3339, (Int.ofNat 35974284775112857), (Int.ofNat 35974284775112868), (Int.negSucc 30074621326462342), (Int.negSucc 30074621326462325),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf334 : Bracket :=
  ⟨3346, 3347, (Int.negSucc 47067388089973052), (Int.negSucc 47067388089973037), (Int.ofNat 24118423067179986), (Int.ofNat 24118423067179992),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf335 : Bracket :=
  ⟨3361, 3362, (Int.ofNat 37662956556890985), (Int.ofNat 37662956556890995), (Int.negSucc 623314774472286), (Int.negSucc 623314774472273),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf336 : Bracket :=
  ⟨3365, 3366, (Int.negSucc 13868743913644032), (Int.negSucc 13868743913644021), (Int.ofNat 13102022863285710), (Int.ofNat 13102022863285720),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf337 : Bracket :=
  ⟨3377, 3378, (Int.ofNat 51039318488450727), (Int.ofNat 51039318488450731), (Int.negSucc 3852071694699796), (Int.negSucc 3852071694699789),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf338 : Bracket :=
  ⟨3387, 3388, (Int.negSucc 10328022834767973), (Int.negSucc 10328022834767958), (Int.ofNat 35353468487339196), (Int.ofNat 35353468487339199),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf339 : Bracket :=
  ⟨3398, 3399, (Int.ofNat 1493054532044682), (Int.ofNat 1493054532044699), (Int.negSucc 16494860559972040), (Int.negSucc 16494860559972034),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf340 : Bracket :=
  ⟨3402, 3403, (Int.negSucc 12687068799413518), (Int.negSucc 12687068799413506), (Int.ofNat 2044556012406357), (Int.ofNat 2044556012406361),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf341 : Bracket :=
  ⟨3406, 3407, (Int.ofNat 13977877060744292), (Int.ofNat 13977877060744298), (Int.negSucc 15866005294598856), (Int.negSucc 15866005294598840),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf342 : Bracket :=
  ⟨3425, 3426, (Int.negSucc 76243602103777961), (Int.negSucc 76243602103777944), (Int.ofNat 287446675372597053), (Int.ofNat 287446675372597066),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf343 : Bracket :=
  ⟨3439, 3440, (Int.ofNat 99990706933449815), (Int.ofNat 99990706933449821), (Int.negSucc 118587999013663760), (Int.negSucc 118587999013663757),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf344 : Bracket :=
  ⟨3448, 3449, (Int.negSucc 7935884892791014), (Int.negSucc 7935884892791011), (Int.ofNat 79876899936195502), (Int.ofNat 79876899936195516),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf345 : Bracket :=
  ⟨3452, 3453, (Int.ofNat 15129916034733957), (Int.ofNat 15129916034733960), (Int.negSucc 146259812429277676), (Int.negSucc 146259812429277661),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf346 : Bracket :=
  ⟨3468, 3469, (Int.negSucc 176316677036967476), (Int.negSucc 176316677036967473), (Int.ofNat 379316070738153746), (Int.ofNat 379316070738153762),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf347 : Bracket :=
  ⟨3481, 3482, (Int.ofNat 360143227540128891), (Int.ofNat 360143227540128902), (Int.negSucc 43731082280461482), (Int.negSucc 43731082280461465),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf348 : Bracket :=
  ⟨3490, 3491, (Int.negSucc 150434677650196859), (Int.negSucc 150434677650196842), (Int.ofNat 199736963097956839), (Int.ofNat 199736963097956849),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf349 : Bracket :=
  ⟨3510, 3511, (Int.ofNat 17570401018017130), (Int.ofNat 17570401018017142), (Int.negSucc 10232904771302037), (Int.negSucc 10232904771302025),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf350 : Bracket :=
  ⟨3512, 3513, (Int.negSucc 12103569707541096), (Int.negSucc 12103569707541093), (Int.ofNat 3620415252221014), (Int.ofNat 3620415252221021),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf351 : Bracket :=
  ⟨3521, 3522, (Int.ofNat 819509105759572), (Int.ofNat 819509105759580), (Int.negSucc 38198582938430464), (Int.negSucc 38198582938430449),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf352 : Bracket :=
  ⟨3533, 3534, (Int.negSucc 1879244139867699), (Int.negSucc 1879244139867688), (Int.ofNat 14009011030115292), (Int.ofNat 14009011030115309),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf353 : Bracket :=
  ⟨3537, 3538, (Int.ofNat 11249448237858112), (Int.ofNat 11249448237858119), (Int.negSucc 1864496540642994), (Int.negSucc 1864496540642981),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf354 : Bracket :=
  ⟨3543, 3544, (Int.negSucc 13759557344428714), (Int.negSucc 13759557344428704), (Int.ofNat 12548039704831352), (Int.ofNat 12548039704831355),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf355 : Bracket :=
  ⟨3554, 3555, (Int.ofNat 73748571927726514), (Int.ofNat 73748571927726527), (Int.negSucc 22863914065433881), (Int.negSucc 22863914065433877),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf356 : Bracket :=
  ⟨3569, 3570, (Int.negSucc 36571180764168168), (Int.negSucc 36571180764168164), (Int.ofNat 87733359503988041), (Int.ofNat 87733359503988045),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf357 : Bracket :=
  ⟨3577, 3578, (Int.ofNat 34121802060554768), (Int.ofNat 34121802060554772), (Int.negSucc 98341397818342802), (Int.negSucc 98341397818342798),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf358 : Bracket :=
  ⟨3590, 3591, (Int.negSucc 62775982794649251), (Int.negSucc 62775982794649237), (Int.ofNat 70491122709296853), (Int.ofNat 70491122709296856),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf359 : Bracket :=
  ⟨3599, 3600, (Int.ofNat 96091160743078980), (Int.ofNat 96091160743078990), (Int.negSucc 3868871657041773), (Int.negSucc 3868871657041771),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf360 : Bracket :=
  ⟨3608, 3609, (Int.negSucc 79142455090926854), (Int.negSucc 79142455090926852), (Int.ofNat 22971838781703165), (Int.ofNat 22971838781703174),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf361 : Bracket :=
  ⟨3621, 3622, (Int.ofNat 38817242317606763), (Int.ofNat 38817242317606778), (Int.negSucc 48246253098585320), (Int.negSucc 48246253098585304),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf362 : Bracket :=
  ⟨3630, 3631, (Int.negSucc 18731806132662145), (Int.negSucc 18731806132662138), (Int.ofNat 43174436737274305), (Int.ofNat 43174436737274308),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf363 : Bracket :=
  ⟨3640, 3641, (Int.ofNat 24148646017224007), (Int.ofNat 24148646017224011), (Int.negSucc 14254332786261326), (Int.negSucc 14254332786261318),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf364 : Bracket :=
  ⟨3646, 3647, (Int.negSucc 8529329255767167), (Int.negSucc 8529329255767157), (Int.ofNat 32357424383535675), (Int.ofNat 32357424383535682),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf365 : Bracket :=
  ⟨3655, 3656, (Int.ofNat 67359924023745485), (Int.ofNat 67359924023745502), (Int.negSucc 13122001284366768), (Int.negSucc 13122001284366766),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf366 : Bracket :=
  ⟨3672, 3673, (Int.negSucc 13199818654568341), (Int.negSucc 13199818654568338), (Int.ofNat 30010937173964424), (Int.ofNat 30010937173964429),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf367 : Bracket :=
  ⟨3677, 3678, (Int.ofNat 13662143664048337), (Int.ofNat 13662143664048350), (Int.negSucc 20896568232344543), (Int.negSucc 20896568232344526),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf368 : Bracket :=
  ⟨3685, 3686, (Int.negSucc 30538686238205524), (Int.negSucc 30538686238205514), (Int.ofNat 18334579621032811), (Int.ofNat 18334579621032815),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf369 : Bracket :=
  ⟨3693, 3694, (Int.ofNat 10626198006727483), (Int.ofNat 10626198006727496), (Int.negSucc 98668906457965322), (Int.negSucc 98668906457965311),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf370 : Bracket :=
  ⟨3714, 3715, (Int.negSucc 8634178423617041), (Int.negSucc 8634178423617024), (Int.ofNat 9598998595320255), (Int.ofNat 9598998595320271),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf371 : Bracket :=
  ⟨3716, 3717, (Int.ofNat 2996126901657059), (Int.ofNat 2996126901657062), (Int.negSucc 21813949702446202), (Int.negSucc 21813949702446199),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf372 : Bracket :=
  ⟨3724, 3725, (Int.negSucc 19903424885811208), (Int.negSucc 19903424885811205), (Int.ofNat 65312678219431860), (Int.ofNat 65312678219431864),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf373 : Bracket :=
  ⟨3739, 3740, (Int.ofNat 97450903097926609), (Int.ofNat 97450903097926614), (Int.negSucc 539300552471627), (Int.negSucc 539300552471624),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf374 : Bracket :=
  ⟨3746, 3747, (Int.negSucc 10477204527453411), (Int.negSucc 10477204527453395), (Int.ofNat 61945688592240804), (Int.ofNat 61945688592240807),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf375 : Bracket :=
  ⟨3754, 3755, (Int.ofNat 70349960423420896), (Int.ofNat 70349960423420910), (Int.negSucc 41076110954550998), (Int.negSucc 41076110954550992),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf376 : Bracket :=
  ⟨3764, 3765, (Int.negSucc 190361810165511520), (Int.negSucc 190361810165511517), (Int.ofNat 5340891306212795), (Int.ofNat 5340891306212808),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf377 : Bracket :=
  ⟨3776, 3777, (Int.ofNat 112272170444876879), (Int.ofNat 112272170444876882), (Int.negSucc 211365686644573150), (Int.negSucc 211365686644573146),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf378 : Bracket :=
  ⟨3786, 3787, (Int.negSucc 316292808371695142), (Int.negSucc 316292808371695125), (Int.ofNat 172321843718537983), (Int.ofNat 172321843718537990),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf379 : Bracket :=
  ⟨3804, 3805, (Int.ofNat 340271688397804664), (Int.ofNat 340271688397804666), (Int.negSucc 1174287531616375), (Int.negSucc 1174287531616371),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf380 : Bracket :=
  ⟨3812, 3813, (Int.negSucc 136635583987542100), (Int.negSucc 136635583987542097), (Int.ofNat 30332690697284040), (Int.ofNat 30332690697284044),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf381 : Bracket :=
  ⟨3822, 3823, (Int.ofNat 95530092702830235), (Int.ofNat 95530092702830245), (Int.negSucc 24965926659495600), (Int.negSucc 24965926659495587),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf382 : Bracket :=
  ⟨3830, 3831, (Int.negSucc 70207658415736756), (Int.negSucc 70207658415736740), (Int.ofNat 38544858735420333), (Int.ofNat 38544858735420336),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf383 : Bracket :=
  ⟨3840, 3841, (Int.ofNat 71042861740828947), (Int.ofNat 71042861740828949), (Int.negSucc 80735850673614938), (Int.negSucc 80735850673614935),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf384 : Bracket :=
  ⟨3854, 3855, (Int.negSucc 96862791962400459), (Int.negSucc 96862791962400448), (Int.ofNat 19907565097239569), (Int.ofNat 19907565097239573),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf385 : Bracket :=
  ⟨3864, 3865, (Int.ofNat 44340698992238513), (Int.ofNat 44340698992238515), (Int.negSucc 5377485967555237), (Int.negSucc 5377485967555233),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf386 : Bracket :=
  ⟨3871, 3872, (Int.negSucc 30361330961999782), (Int.negSucc 30361330961999778), (Int.ofNat 2082948170745834), (Int.ofNat 2082948170745837),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf387 : Bracket :=
  ⟨3881, 3882, (Int.ofNat 23607442832538792), (Int.ofNat 23607442832538807), (Int.negSucc 2173816832899278), (Int.negSucc 2173816832899262),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf388 : Bracket :=
  ⟨3888, 3889, (Int.negSucc 774701791150033), (Int.negSucc 774701791150030), (Int.ofNat 25728964410478335), (Int.ofNat 25728964410478344),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf389 : Bracket :=
  ⟨3897, 3898, (Int.ofNat 24824257899021557), (Int.ofNat 24824257899021570), (Int.negSucc 18145436360807691), (Int.negSucc 18145436360807683),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf390 : Bracket :=
  ⟨3908, 3909, (Int.negSucc 48297481318728898), (Int.negSucc 48297481318728895), (Int.ofNat 4251756352190751), (Int.ofNat 4251756352190754),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf391 : Bracket :=
  ⟨3919, 3920, (Int.ofNat 21693752935020058), (Int.ofNat 21693752935020068), (Int.negSucc 13949265705264931), (Int.negSucc 13949265705264928),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf392 : Bracket :=
  ⟨3925, 3926, (Int.negSucc 30321297648188923), (Int.negSucc 30321297648188914), (Int.ofNat 1848165166932553), (Int.ofNat 1848165166932567),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf393 : Bracket :=
  ⟨3935, 3936, (Int.ofNat 42009062961710321), (Int.ofNat 42009062961710334), (Int.negSucc 17705901441775619), (Int.negSucc 17705901441775617),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf394 : Bracket :=
  ⟨3946, 3947, (Int.negSucc 13200722900463262), (Int.negSucc 13200722900463245), (Int.ofNat 75107224922407623), (Int.ofNat 75107224922407626),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf395 : Bracket :=
  ⟨3958, 3959, (Int.ofNat 22619334317022117), (Int.ofNat 22619334317022132), (Int.negSucc 38700322518574985), (Int.negSucc 38700322518574982),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf396 : Bracket :=
  ⟨3963, 3964, (Int.negSucc 40761794341905398), (Int.negSucc 40761794341905388), (Int.ofNat 27422917583429261), (Int.ofNat 27422917583429263),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf397 : Bracket :=
  ⟨3975, 3976, (Int.ofNat 10979588824097848), (Int.ofNat 10979588824097861), (Int.negSucc 194492882108806988), (Int.negSucc 194492882108806986),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf398 : Bracket :=
  ⟨3990, 3991, (Int.negSucc 58670662799987171), (Int.negSucc 58670662799987166), (Int.ofNat 82427746244622232), (Int.ofNat 82427746244622239),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf399 : Bracket :=
  ⟨3995, 3996, (Int.ofNat 84993658516056813), (Int.ofNat 84993658516056816), (Int.negSucc 60962089236483894), (Int.negSucc 60962089236483892),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf400 : Bracket :=
  ⟨4013, 4014, (Int.negSucc 60622105585921440), (Int.negSucc 60622105585921434), (Int.ofNat 57200750240996416), (Int.ofNat 57200750240996421),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf401 : Bracket :=
  ⟨4019, 4020, (Int.ofNat 22692180690232564), (Int.ofNat 22692180690232567), (Int.negSucc 59412216860480044), (Int.negSucc 59412216860480042),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf402 : Bracket :=
  ⟨4028, 4029, (Int.negSucc 9626207017246121), (Int.negSucc 9626207017246118), (Int.ofNat 98103839608843993), (Int.ofNat 98103839608844008),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf403 : Bracket :=
  ⟨4037, 4038, (Int.ofNat 129073425853811700), (Int.ofNat 129073425853811704), (Int.negSucc 7814696355588725), (Int.negSucc 7814696355588722),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf404 : Bracket :=
  ⟨4049, 4050, (Int.negSucc 33967333428242097), (Int.negSucc 33967333428242094), (Int.ofNat 123489515013068046), (Int.ofNat 123489515013068049),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf405 : Bracket :=
  ⟨4059, 4060, (Int.ofNat 77895554414682949), (Int.ofNat 77895554414682951), (Int.negSucc 54003914033742511), (Int.negSucc 54003914033742509),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf406 : Bracket :=
  ⟨4066, 4067, (Int.negSucc 136429228763341859), (Int.negSucc 136429228763341855), (Int.ofNat 8858053251805445), (Int.ofNat 8858053251805448),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf407 : Bracket :=
  ⟨4080, 4081, (Int.ofNat 124511535559554234), (Int.ofNat 124511535559554236), (Int.negSucc 98095310475646573), (Int.negSucc 98095310475646570),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf408 : Bracket :=
  ⟨4089, 4090, (Int.negSucc 133027743014443321), (Int.negSucc 133027743014443318), (Int.ofNat 89702976071813820), (Int.ofNat 89702976071813824),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def node0 : Tree 12 28 2 :=
  Tree.join (Tree.leaf leaf1) (Tree.leaf leaf2) (by decide +kernel)
noncomputable def node1 : Tree 9 28 3 :=
  Tree.join (Tree.leaf leaf0) (node0) (by decide +kernel)
noncomputable def node2 : Tree 44 56 2 :=
  Tree.join (Tree.leaf leaf4) (Tree.leaf leaf5) (by decide +kernel)
noncomputable def node3 : Tree 34 56 3 :=
  Tree.join (Tree.leaf leaf3) (node2) (by decide +kernel)
noncomputable def node4 : Tree 9 56 6 :=
  Tree.join (node1) (node3) (by decide +kernel)
noncomputable def node5 : Tree 72 83 2 :=
  Tree.join (Tree.leaf leaf7) (Tree.leaf leaf8) (by decide +kernel)
noncomputable def node6 : Tree 62 83 3 :=
  Tree.join (Tree.leaf leaf6) (node5) (by decide +kernel)
noncomputable def node7 : Tree 106 118 2 :=
  Tree.join (Tree.leaf leaf10) (Tree.leaf leaf11) (by decide +kernel)
noncomputable def node8 : Tree 98 118 3 :=
  Tree.join (Tree.leaf leaf9) (node7) (by decide +kernel)
noncomputable def node9 : Tree 62 118 6 :=
  Tree.join (node6) (node8) (by decide +kernel)
noncomputable def node10 : Tree 9 118 12 :=
  Tree.join (node4) (node9) (by decide +kernel)
noncomputable def node11 : Tree 127 138 2 :=
  Tree.join (Tree.leaf leaf13) (Tree.leaf leaf14) (by decide +kernel)
noncomputable def node12 : Tree 123 138 3 :=
  Tree.join (Tree.leaf leaf12) (node11) (by decide +kernel)
noncomputable def node13 : Tree 167 176 2 :=
  Tree.join (Tree.leaf leaf16) (Tree.leaf leaf17) (by decide +kernel)
noncomputable def node14 : Tree 155 176 3 :=
  Tree.join (Tree.leaf leaf15) (node13) (by decide +kernel)
noncomputable def node15 : Tree 123 176 6 :=
  Tree.join (node12) (node14) (by decide +kernel)
noncomputable def node16 : Tree 190 206 2 :=
  Tree.join (Tree.leaf leaf19) (Tree.leaf leaf20) (by decide +kernel)
noncomputable def node17 : Tree 181 206 3 :=
  Tree.join (Tree.leaf leaf18) (node16) (by decide +kernel)
noncomputable def node18 : Tree 212 225 2 :=
  Tree.join (Tree.leaf leaf21) (Tree.leaf leaf22) (by decide +kernel)
noncomputable def node19 : Tree 234 240 2 :=
  Tree.join (Tree.leaf leaf23) (Tree.leaf leaf24) (by decide +kernel)
noncomputable def node20 : Tree 212 240 4 :=
  Tree.join (node18) (node19) (by decide +kernel)
noncomputable def node21 : Tree 181 240 7 :=
  Tree.join (node17) (node20) (by decide +kernel)
noncomputable def node22 : Tree 123 240 13 :=
  Tree.join (node15) (node21) (by decide +kernel)
noncomputable def node23 : Tree 9 240 25 :=
  Tree.join (node10) (node22) (by decide +kernel)
noncomputable def node24 : Tree 256 273 2 :=
  Tree.join (Tree.leaf leaf26) (Tree.leaf leaf27) (by decide +kernel)
noncomputable def node25 : Tree 252 273 3 :=
  Tree.join (Tree.leaf leaf25) (node24) (by decide +kernel)
noncomputable def node26 : Tree 289 303 2 :=
  Tree.join (Tree.leaf leaf29) (Tree.leaf leaf30) (by decide +kernel)
noncomputable def node27 : Tree 283 303 3 :=
  Tree.join (Tree.leaf leaf28) (node26) (by decide +kernel)
noncomputable def node28 : Tree 252 303 6 :=
  Tree.join (node25) (node27) (by decide +kernel)
noncomputable def node29 : Tree 322 339 2 :=
  Tree.join (Tree.leaf leaf32) (Tree.leaf leaf33) (by decide +kernel)
noncomputable def node30 : Tree 315 339 3 :=
  Tree.join (Tree.leaf leaf31) (node29) (by decide +kernel)
noncomputable def node31 : Tree 349 360 2 :=
  Tree.join (Tree.leaf leaf34) (Tree.leaf leaf35) (by decide +kernel)
noncomputable def node32 : Tree 364 381 2 :=
  Tree.join (Tree.leaf leaf36) (Tree.leaf leaf37) (by decide +kernel)
noncomputable def node33 : Tree 349 381 4 :=
  Tree.join (node31) (node32) (by decide +kernel)
noncomputable def node34 : Tree 315 381 7 :=
  Tree.join (node30) (node33) (by decide +kernel)
noncomputable def node35 : Tree 252 381 13 :=
  Tree.join (node28) (node34) (by decide +kernel)
noncomputable def node36 : Tree 392 407 2 :=
  Tree.join (Tree.leaf leaf39) (Tree.leaf leaf40) (by decide +kernel)
noncomputable def node37 : Tree 387 407 3 :=
  Tree.join (Tree.leaf leaf38) (node36) (by decide +kernel)
noncomputable def node38 : Tree 422 434 2 :=
  Tree.join (Tree.leaf leaf42) (Tree.leaf leaf43) (by decide +kernel)
noncomputable def node39 : Tree 415 434 3 :=
  Tree.join (Tree.leaf leaf41) (node38) (by decide +kernel)
noncomputable def node40 : Tree 387 434 6 :=
  Tree.join (node37) (node39) (by decide +kernel)
noncomputable def node41 : Tree 446 466 2 :=
  Tree.join (Tree.leaf leaf45) (Tree.leaf leaf46) (by decide +kernel)
noncomputable def node42 : Tree 442 466 3 :=
  Tree.join (Tree.leaf leaf44) (node41) (by decide +kernel)
noncomputable def node43 : Tree 467 482 2 :=
  Tree.join (Tree.leaf leaf47) (Tree.leaf leaf48) (by decide +kernel)
noncomputable def node44 : Tree 491 504 2 :=
  Tree.join (Tree.leaf leaf49) (Tree.leaf leaf50) (by decide +kernel)
noncomputable def node45 : Tree 467 504 4 :=
  Tree.join (node43) (node44) (by decide +kernel)
noncomputable def node46 : Tree 442 504 7 :=
  Tree.join (node42) (node45) (by decide +kernel)
noncomputable def node47 : Tree 387 504 13 :=
  Tree.join (node40) (node46) (by decide +kernel)
noncomputable def node48 : Tree 252 504 26 :=
  Tree.join (node35) (node47) (by decide +kernel)
noncomputable def node49 : Tree 9 504 51 :=
  Tree.join (node23) (node48) (by decide +kernel)
noncomputable def node50 : Tree 525 537 2 :=
  Tree.join (Tree.leaf leaf52) (Tree.leaf leaf53) (by decide +kernel)
noncomputable def node51 : Tree 514 537 3 :=
  Tree.join (Tree.leaf leaf51) (node50) (by decide +kernel)
noncomputable def node52 : Tree 549 560 2 :=
  Tree.join (Tree.leaf leaf55) (Tree.leaf leaf56) (by decide +kernel)
noncomputable def node53 : Tree 540 560 3 :=
  Tree.join (Tree.leaf leaf54) (node52) (by decide +kernel)
noncomputable def node54 : Tree 514 560 6 :=
  Tree.join (node51) (node53) (by decide +kernel)
noncomputable def node55 : Tree 589 603 2 :=
  Tree.join (Tree.leaf leaf58) (Tree.leaf leaf59) (by decide +kernel)
noncomputable def node56 : Tree 569 603 3 :=
  Tree.join (Tree.leaf leaf57) (node55) (by decide +kernel)
noncomputable def node57 : Tree 617 623 2 :=
  Tree.join (Tree.leaf leaf61) (Tree.leaf leaf62) (by decide +kernel)
noncomputable def node58 : Tree 610 623 3 :=
  Tree.join (Tree.leaf leaf60) (node57) (by decide +kernel)
noncomputable def node59 : Tree 569 623 6 :=
  Tree.join (node56) (node58) (by decide +kernel)
noncomputable def node60 : Tree 514 623 12 :=
  Tree.join (node54) (node59) (by decide +kernel)
noncomputable def node61 : Tree 641 655 2 :=
  Tree.join (Tree.leaf leaf64) (Tree.leaf leaf65) (by decide +kernel)
noncomputable def node62 : Tree 637 655 3 :=
  Tree.join (Tree.leaf leaf63) (node61) (by decide +kernel)
noncomputable def node63 : Tree 673 680 2 :=
  Tree.join (Tree.leaf leaf67) (Tree.leaf leaf68) (by decide +kernel)
noncomputable def node64 : Tree 662 680 3 :=
  Tree.join (Tree.leaf leaf66) (node63) (by decide +kernel)
noncomputable def node65 : Tree 637 680 6 :=
  Tree.join (node62) (node64) (by decide +kernel)
noncomputable def node66 : Tree 708 718 2 :=
  Tree.join (Tree.leaf leaf70) (Tree.leaf leaf71) (by decide +kernel)
noncomputable def node67 : Tree 698 718 3 :=
  Tree.join (Tree.leaf leaf69) (node66) (by decide +kernel)
noncomputable def node68 : Tree 722 733 2 :=
  Tree.join (Tree.leaf leaf72) (Tree.leaf leaf73) (by decide +kernel)
noncomputable def node69 : Tree 754 758 2 :=
  Tree.join (Tree.leaf leaf74) (Tree.leaf leaf75) (by decide +kernel)
noncomputable def node70 : Tree 722 758 4 :=
  Tree.join (node68) (node69) (by decide +kernel)
noncomputable def node71 : Tree 698 758 7 :=
  Tree.join (node67) (node70) (by decide +kernel)
noncomputable def node72 : Tree 637 758 13 :=
  Tree.join (node65) (node71) (by decide +kernel)
noncomputable def node73 : Tree 514 758 25 :=
  Tree.join (node60) (node72) (by decide +kernel)
noncomputable def node74 : Tree 770 777 2 :=
  Tree.join (Tree.leaf leaf77) (Tree.leaf leaf78) (by decide +kernel)
noncomputable def node75 : Tree 765 777 3 :=
  Tree.join (Tree.leaf leaf76) (node74) (by decide +kernel)
noncomputable def node76 : Tree 798 815 2 :=
  Tree.join (Tree.leaf leaf80) (Tree.leaf leaf81) (by decide +kernel)
noncomputable def node77 : Tree 792 815 3 :=
  Tree.join (Tree.leaf leaf79) (node76) (by decide +kernel)
noncomputable def node78 : Tree 765 815 6 :=
  Tree.join (node75) (node77) (by decide +kernel)
noncomputable def node79 : Tree 829 841 2 :=
  Tree.join (Tree.leaf leaf83) (Tree.leaf leaf84) (by decide +kernel)
noncomputable def node80 : Tree 819 841 3 :=
  Tree.join (Tree.leaf leaf82) (node79) (by decide +kernel)
noncomputable def node81 : Tree 856 866 2 :=
  Tree.join (Tree.leaf leaf85) (Tree.leaf leaf86) (by decide +kernel)
noncomputable def node82 : Tree 869 887 2 :=
  Tree.join (Tree.leaf leaf87) (Tree.leaf leaf88) (by decide +kernel)
noncomputable def node83 : Tree 856 887 4 :=
  Tree.join (node81) (node82) (by decide +kernel)
noncomputable def node84 : Tree 819 887 7 :=
  Tree.join (node80) (node83) (by decide +kernel)
noncomputable def node85 : Tree 765 887 13 :=
  Tree.join (node78) (node84) (by decide +kernel)
noncomputable def node86 : Tree 912 923 2 :=
  Tree.join (Tree.leaf leaf90) (Tree.leaf leaf91) (by decide +kernel)
noncomputable def node87 : Tree 897 923 3 :=
  Tree.join (Tree.leaf leaf89) (node86) (by decide +kernel)
noncomputable def node88 : Tree 937 950 2 :=
  Tree.join (Tree.leaf leaf93) (Tree.leaf leaf94) (by decide +kernel)
noncomputable def node89 : Tree 925 950 3 :=
  Tree.join (Tree.leaf leaf92) (node88) (by decide +kernel)
noncomputable def node90 : Tree 897 950 6 :=
  Tree.join (node87) (node89) (by decide +kernel)
noncomputable def node91 : Tree 959 979 2 :=
  Tree.join (Tree.leaf leaf96) (Tree.leaf leaf97) (by decide +kernel)
noncomputable def node92 : Tree 953 979 3 :=
  Tree.join (Tree.leaf leaf95) (node91) (by decide +kernel)
noncomputable def node93 : Tree 988 998 2 :=
  Tree.join (Tree.leaf leaf98) (Tree.leaf leaf99) (by decide +kernel)
noncomputable def node94 : Tree 1002 1016 2 :=
  Tree.join (Tree.leaf leaf100) (Tree.leaf leaf101) (by decide +kernel)
noncomputable def node95 : Tree 988 1016 4 :=
  Tree.join (node93) (node94) (by decide +kernel)
noncomputable def node96 : Tree 953 1016 7 :=
  Tree.join (node92) (node95) (by decide +kernel)
noncomputable def node97 : Tree 897 1016 13 :=
  Tree.join (node90) (node96) (by decide +kernel)
noncomputable def node98 : Tree 765 1016 26 :=
  Tree.join (node85) (node97) (by decide +kernel)
noncomputable def node99 : Tree 514 1016 51 :=
  Tree.join (node73) (node98) (by decide +kernel)
noncomputable def node100 : Tree 9 1016 102 :=
  Tree.join (node49) (node99) (by decide +kernel)
noncomputable def node101 : Tree 1033 1043 2 :=
  Tree.join (Tree.leaf leaf103) (Tree.leaf leaf104) (by decide +kernel)
noncomputable def node102 : Tree 1021 1043 3 :=
  Tree.join (Tree.leaf leaf102) (node101) (by decide +kernel)
noncomputable def node103 : Tree 1059 1075 2 :=
  Tree.join (Tree.leaf leaf106) (Tree.leaf leaf107) (by decide +kernel)
noncomputable def node104 : Tree 1050 1075 3 :=
  Tree.join (Tree.leaf leaf105) (node103) (by decide +kernel)
noncomputable def node105 : Tree 1021 1075 6 :=
  Tree.join (node102) (node104) (by decide +kernel)
noncomputable def node106 : Tree 1089 1107 2 :=
  Tree.join (Tree.leaf leaf109) (Tree.leaf leaf110) (by decide +kernel)
noncomputable def node107 : Tree 1088 1107 3 :=
  Tree.join (Tree.leaf leaf108) (node106) (by decide +kernel)
noncomputable def node108 : Tree 1124 1136 2 :=
  Tree.join (Tree.leaf leaf112) (Tree.leaf leaf113) (by decide +kernel)
noncomputable def node109 : Tree 1119 1136 3 :=
  Tree.join (Tree.leaf leaf111) (node108) (by decide +kernel)
noncomputable def node110 : Tree 1088 1136 6 :=
  Tree.join (node107) (node109) (by decide +kernel)
noncomputable def node111 : Tree 1021 1136 12 :=
  Tree.join (node105) (node110) (by decide +kernel)
noncomputable def node112 : Tree 1151 1166 2 :=
  Tree.join (Tree.leaf leaf115) (Tree.leaf leaf116) (by decide +kernel)
noncomputable def node113 : Tree 1141 1166 3 :=
  Tree.join (Tree.leaf leaf114) (node112) (by decide +kernel)
noncomputable def node114 : Tree 1184 1196 2 :=
  Tree.join (Tree.leaf leaf118) (Tree.leaf leaf119) (by decide +kernel)
noncomputable def node115 : Tree 1176 1196 3 :=
  Tree.join (Tree.leaf leaf117) (node114) (by decide +kernel)
noncomputable def node116 : Tree 1141 1196 6 :=
  Tree.join (node113) (node115) (by decide +kernel)
noncomputable def node117 : Tree 1212 1230 2 :=
  Tree.join (Tree.leaf leaf121) (Tree.leaf leaf122) (by decide +kernel)
noncomputable def node118 : Tree 1204 1230 3 :=
  Tree.join (Tree.leaf leaf120) (node117) (by decide +kernel)
noncomputable def node119 : Tree 1239 1250 2 :=
  Tree.join (Tree.leaf leaf123) (Tree.leaf leaf124) (by decide +kernel)
noncomputable def node120 : Tree 1261 1269 2 :=
  Tree.join (Tree.leaf leaf125) (Tree.leaf leaf126) (by decide +kernel)
noncomputable def node121 : Tree 1239 1269 4 :=
  Tree.join (node119) (node120) (by decide +kernel)
noncomputable def node122 : Tree 1204 1269 7 :=
  Tree.join (node118) (node121) (by decide +kernel)
noncomputable def node123 : Tree 1141 1269 13 :=
  Tree.join (node116) (node122) (by decide +kernel)
noncomputable def node124 : Tree 1021 1269 25 :=
  Tree.join (node111) (node123) (by decide +kernel)
noncomputable def node125 : Tree 1281 1294 2 :=
  Tree.join (Tree.leaf leaf128) (Tree.leaf leaf129) (by decide +kernel)
noncomputable def node126 : Tree 1275 1294 3 :=
  Tree.join (Tree.leaf leaf127) (node125) (by decide +kernel)
noncomputable def node127 : Tree 1313 1329 2 :=
  Tree.join (Tree.leaf leaf131) (Tree.leaf leaf132) (by decide +kernel)
noncomputable def node128 : Tree 1307 1329 3 :=
  Tree.join (Tree.leaf leaf130) (node127) (by decide +kernel)
noncomputable def node129 : Tree 1275 1329 6 :=
  Tree.join (node126) (node128) (by decide +kernel)
noncomputable def node130 : Tree 1346 1355 2 :=
  Tree.join (Tree.leaf leaf134) (Tree.leaf leaf135) (by decide +kernel)
noncomputable def node131 : Tree 1334 1355 3 :=
  Tree.join (Tree.leaf leaf133) (node130) (by decide +kernel)
noncomputable def node132 : Tree 1359 1374 2 :=
  Tree.join (Tree.leaf leaf136) (Tree.leaf leaf137) (by decide +kernel)
noncomputable def node133 : Tree 1384 1390 2 :=
  Tree.join (Tree.leaf leaf138) (Tree.leaf leaf139) (by decide +kernel)
noncomputable def node134 : Tree 1359 1390 4 :=
  Tree.join (node132) (node133) (by decide +kernel)
noncomputable def node135 : Tree 1334 1390 7 :=
  Tree.join (node131) (node134) (by decide +kernel)
noncomputable def node136 : Tree 1275 1390 13 :=
  Tree.join (node129) (node135) (by decide +kernel)
noncomputable def node137 : Tree 1407 1426 2 :=
  Tree.join (Tree.leaf leaf141) (Tree.leaf leaf142) (by decide +kernel)
noncomputable def node138 : Tree 1400 1426 3 :=
  Tree.join (Tree.leaf leaf140) (node137) (by decide +kernel)
noncomputable def node139 : Tree 1446 1464 2 :=
  Tree.join (Tree.leaf leaf144) (Tree.leaf leaf145) (by decide +kernel)
noncomputable def node140 : Tree 1431 1464 3 :=
  Tree.join (Tree.leaf leaf143) (node139) (by decide +kernel)
noncomputable def node141 : Tree 1400 1464 6 :=
  Tree.join (node138) (node140) (by decide +kernel)
noncomputable def node142 : Tree 1478 1489 2 :=
  Tree.join (Tree.leaf leaf147) (Tree.leaf leaf148) (by decide +kernel)
noncomputable def node143 : Tree 1471 1489 3 :=
  Tree.join (Tree.leaf leaf146) (node142) (by decide +kernel)
noncomputable def node144 : Tree 1495 1508 2 :=
  Tree.join (Tree.leaf leaf149) (Tree.leaf leaf150) (by decide +kernel)
noncomputable def node145 : Tree 1521 1530 2 :=
  Tree.join (Tree.leaf leaf151) (Tree.leaf leaf152) (by decide +kernel)
noncomputable def node146 : Tree 1495 1530 4 :=
  Tree.join (node144) (node145) (by decide +kernel)
noncomputable def node147 : Tree 1471 1530 7 :=
  Tree.join (node143) (node146) (by decide +kernel)
noncomputable def node148 : Tree 1400 1530 13 :=
  Tree.join (node141) (node147) (by decide +kernel)
noncomputable def node149 : Tree 1275 1530 26 :=
  Tree.join (node136) (node148) (by decide +kernel)
noncomputable def node150 : Tree 1021 1530 51 :=
  Tree.join (node124) (node149) (by decide +kernel)
noncomputable def node151 : Tree 1544 1553 2 :=
  Tree.join (Tree.leaf leaf154) (Tree.leaf leaf155) (by decide +kernel)
noncomputable def node152 : Tree 1538 1553 3 :=
  Tree.join (Tree.leaf leaf153) (node151) (by decide +kernel)
noncomputable def node153 : Tree 1576 1579 2 :=
  Tree.join (Tree.leaf leaf157) (Tree.leaf leaf158) (by decide +kernel)
noncomputable def node154 : Tree 1562 1579 3 :=
  Tree.join (Tree.leaf leaf156) (node153) (by decide +kernel)
noncomputable def node155 : Tree 1538 1579 6 :=
  Tree.join (node152) (node154) (by decide +kernel)
noncomputable def node156 : Tree 1610 1618 2 :=
  Tree.join (Tree.leaf leaf160) (Tree.leaf leaf161) (by decide +kernel)
noncomputable def node157 : Tree 1594 1618 3 :=
  Tree.join (Tree.leaf leaf159) (node156) (by decide +kernel)
noncomputable def node158 : Tree 1640 1645 2 :=
  Tree.join (Tree.leaf leaf163) (Tree.leaf leaf164) (by decide +kernel)
noncomputable def node159 : Tree 1626 1645 3 :=
  Tree.join (Tree.leaf leaf162) (node158) (by decide +kernel)
noncomputable def node160 : Tree 1594 1645 6 :=
  Tree.join (node157) (node159) (by decide +kernel)
noncomputable def node161 : Tree 1538 1645 12 :=
  Tree.join (node155) (node160) (by decide +kernel)
noncomputable def node162 : Tree 1663 1678 2 :=
  Tree.join (Tree.leaf leaf166) (Tree.leaf leaf167) (by decide +kernel)
noncomputable def node163 : Tree 1653 1678 3 :=
  Tree.join (Tree.leaf leaf165) (node162) (by decide +kernel)
noncomputable def node164 : Tree 1690 1703 2 :=
  Tree.join (Tree.leaf leaf169) (Tree.leaf leaf170) (by decide +kernel)
noncomputable def node165 : Tree 1684 1703 3 :=
  Tree.join (Tree.leaf leaf168) (node164) (by decide +kernel)
noncomputable def node166 : Tree 1653 1703 6 :=
  Tree.join (node163) (node165) (by decide +kernel)
noncomputable def node167 : Tree 1724 1737 2 :=
  Tree.join (Tree.leaf leaf172) (Tree.leaf leaf173) (by decide +kernel)
noncomputable def node168 : Tree 1709 1737 3 :=
  Tree.join (Tree.leaf leaf171) (node167) (by decide +kernel)
noncomputable def node169 : Tree 1746 1762 2 :=
  Tree.join (Tree.leaf leaf174) (Tree.leaf leaf175) (by decide +kernel)
noncomputable def node170 : Tree 1766 1775 2 :=
  Tree.join (Tree.leaf leaf176) (Tree.leaf leaf177) (by decide +kernel)
noncomputable def node171 : Tree 1746 1775 4 :=
  Tree.join (node169) (node170) (by decide +kernel)
noncomputable def node172 : Tree 1709 1775 7 :=
  Tree.join (node168) (node171) (by decide +kernel)
noncomputable def node173 : Tree 1653 1775 13 :=
  Tree.join (node166) (node172) (by decide +kernel)
noncomputable def node174 : Tree 1538 1775 25 :=
  Tree.join (node161) (node173) (by decide +kernel)
noncomputable def node175 : Tree 1797 1803 2 :=
  Tree.join (Tree.leaf leaf179) (Tree.leaf leaf180) (by decide +kernel)
noncomputable def node176 : Tree 1787 1803 3 :=
  Tree.join (Tree.leaf leaf178) (node175) (by decide +kernel)
noncomputable def node177 : Tree 1828 1843 2 :=
  Tree.join (Tree.leaf leaf182) (Tree.leaf leaf183) (by decide +kernel)
noncomputable def node178 : Tree 1819 1843 3 :=
  Tree.join (Tree.leaf leaf181) (node177) (by decide +kernel)
noncomputable def node179 : Tree 1787 1843 6 :=
  Tree.join (node176) (node178) (by decide +kernel)
noncomputable def node180 : Tree 1859 1865 2 :=
  Tree.join (Tree.leaf leaf185) (Tree.leaf leaf186) (by decide +kernel)
noncomputable def node181 : Tree 1853 1865 3 :=
  Tree.join (Tree.leaf leaf184) (node180) (by decide +kernel)
noncomputable def node182 : Tree 1880 1887 2 :=
  Tree.join (Tree.leaf leaf187) (Tree.leaf leaf188) (by decide +kernel)
noncomputable def node183 : Tree 1896 1900 2 :=
  Tree.join (Tree.leaf leaf189) (Tree.leaf leaf190) (by decide +kernel)
noncomputable def node184 : Tree 1880 1900 4 :=
  Tree.join (node182) (node183) (by decide +kernel)
noncomputable def node185 : Tree 1853 1900 7 :=
  Tree.join (node181) (node184) (by decide +kernel)
noncomputable def node186 : Tree 1787 1900 13 :=
  Tree.join (node179) (node185) (by decide +kernel)
noncomputable def node187 : Tree 1919 1940 2 :=
  Tree.join (Tree.leaf leaf192) (Tree.leaf leaf193) (by decide +kernel)
noncomputable def node188 : Tree 1908 1940 3 :=
  Tree.join (Tree.leaf leaf191) (node187) (by decide +kernel)
noncomputable def node189 : Tree 1954 1964 2 :=
  Tree.join (Tree.leaf leaf195) (Tree.leaf leaf196) (by decide +kernel)
noncomputable def node190 : Tree 1941 1964 3 :=
  Tree.join (Tree.leaf leaf194) (node189) (by decide +kernel)
noncomputable def node191 : Tree 1908 1964 6 :=
  Tree.join (node188) (node190) (by decide +kernel)
noncomputable def node192 : Tree 1986 1997 2 :=
  Tree.join (Tree.leaf leaf198) (Tree.leaf leaf199) (by decide +kernel)
noncomputable def node193 : Tree 1971 1997 3 :=
  Tree.join (Tree.leaf leaf197) (node192) (by decide +kernel)
noncomputable def node194 : Tree 2004 2017 2 :=
  Tree.join (Tree.leaf leaf200) (Tree.leaf leaf201) (by decide +kernel)
noncomputable def node195 : Tree 2035 2040 2 :=
  Tree.join (Tree.leaf leaf202) (Tree.leaf leaf203) (by decide +kernel)
noncomputable def node196 : Tree 2004 2040 4 :=
  Tree.join (node194) (node195) (by decide +kernel)
noncomputable def node197 : Tree 1971 2040 7 :=
  Tree.join (node193) (node196) (by decide +kernel)
noncomputable def node198 : Tree 1908 2040 13 :=
  Tree.join (node191) (node197) (by decide +kernel)
noncomputable def node199 : Tree 1787 2040 26 :=
  Tree.join (node186) (node198) (by decide +kernel)
noncomputable def node200 : Tree 1538 2040 51 :=
  Tree.join (node174) (node199) (by decide +kernel)
noncomputable def node201 : Tree 1021 2040 102 :=
  Tree.join (node150) (node200) (by decide +kernel)
noncomputable def node202 : Tree 9 2040 204 :=
  Tree.join (node100) (node201) (by decide +kernel)
noncomputable def node203 : Tree 2054 2067 2 :=
  Tree.join (Tree.leaf leaf205) (Tree.leaf leaf206) (by decide +kernel)
noncomputable def node204 : Tree 2042 2067 3 :=
  Tree.join (Tree.leaf leaf204) (node203) (by decide +kernel)
noncomputable def node205 : Tree 2091 2097 2 :=
  Tree.join (Tree.leaf leaf208) (Tree.leaf leaf209) (by decide +kernel)
noncomputable def node206 : Tree 2081 2097 3 :=
  Tree.join (Tree.leaf leaf207) (node205) (by decide +kernel)
noncomputable def node207 : Tree 2042 2097 6 :=
  Tree.join (node204) (node206) (by decide +kernel)
noncomputable def node208 : Tree 2115 2122 2 :=
  Tree.join (Tree.leaf leaf211) (Tree.leaf leaf212) (by decide +kernel)
noncomputable def node209 : Tree 2111 2122 3 :=
  Tree.join (Tree.leaf leaf210) (node208) (by decide +kernel)
noncomputable def node210 : Tree 2151 2159 2 :=
  Tree.join (Tree.leaf leaf214) (Tree.leaf leaf215) (by decide +kernel)
noncomputable def node211 : Tree 2131 2159 3 :=
  Tree.join (Tree.leaf leaf213) (node210) (by decide +kernel)
noncomputable def node212 : Tree 2111 2159 6 :=
  Tree.join (node209) (node211) (by decide +kernel)
noncomputable def node213 : Tree 2042 2159 12 :=
  Tree.join (node207) (node212) (by decide +kernel)
noncomputable def node214 : Tree 2173 2191 2 :=
  Tree.join (Tree.leaf leaf217) (Tree.leaf leaf218) (by decide +kernel)
noncomputable def node215 : Tree 2168 2191 3 :=
  Tree.join (Tree.leaf leaf216) (node214) (by decide +kernel)
noncomputable def node216 : Tree 2204 2219 2 :=
  Tree.join (Tree.leaf leaf220) (Tree.leaf leaf221) (by decide +kernel)
noncomputable def node217 : Tree 2194 2219 3 :=
  Tree.join (Tree.leaf leaf219) (node216) (by decide +kernel)
noncomputable def node218 : Tree 2168 2219 6 :=
  Tree.join (node215) (node217) (by decide +kernel)
noncomputable def node219 : Tree 2236 2244 2 :=
  Tree.join (Tree.leaf leaf223) (Tree.leaf leaf224) (by decide +kernel)
noncomputable def node220 : Tree 2224 2244 3 :=
  Tree.join (Tree.leaf leaf222) (node219) (by decide +kernel)
noncomputable def node221 : Tree 2258 2269 2 :=
  Tree.join (Tree.leaf leaf225) (Tree.leaf leaf226) (by decide +kernel)
noncomputable def node222 : Tree 2275 2284 2 :=
  Tree.join (Tree.leaf leaf227) (Tree.leaf leaf228) (by decide +kernel)
noncomputable def node223 : Tree 2258 2284 4 :=
  Tree.join (node221) (node222) (by decide +kernel)
noncomputable def node224 : Tree 2224 2284 7 :=
  Tree.join (node220) (node223) (by decide +kernel)
noncomputable def node225 : Tree 2168 2284 13 :=
  Tree.join (node218) (node224) (by decide +kernel)
noncomputable def node226 : Tree 2042 2284 25 :=
  Tree.join (node213) (node225) (by decide +kernel)
noncomputable def node227 : Tree 2297 2316 2 :=
  Tree.join (Tree.leaf leaf230) (Tree.leaf leaf231) (by decide +kernel)
noncomputable def node228 : Tree 2286 2316 3 :=
  Tree.join (Tree.leaf leaf229) (node227) (by decide +kernel)
noncomputable def node229 : Tree 2340 2353 2 :=
  Tree.join (Tree.leaf leaf233) (Tree.leaf leaf234) (by decide +kernel)
noncomputable def node230 : Tree 2322 2353 3 :=
  Tree.join (Tree.leaf leaf232) (node229) (by decide +kernel)
noncomputable def node231 : Tree 2286 2353 6 :=
  Tree.join (node228) (node230) (by decide +kernel)
noncomputable def node232 : Tree 2374 2384 2 :=
  Tree.join (Tree.leaf leaf236) (Tree.leaf leaf237) (by decide +kernel)
noncomputable def node233 : Tree 2362 2384 3 :=
  Tree.join (Tree.leaf leaf235) (node232) (by decide +kernel)
noncomputable def node234 : Tree 2387 2398 2 :=
  Tree.join (Tree.leaf leaf238) (Tree.leaf leaf239) (by decide +kernel)
noncomputable def node235 : Tree 2411 2415 2 :=
  Tree.join (Tree.leaf leaf240) (Tree.leaf leaf241) (by decide +kernel)
noncomputable def node236 : Tree 2387 2415 4 :=
  Tree.join (node234) (node235) (by decide +kernel)
noncomputable def node237 : Tree 2362 2415 7 :=
  Tree.join (node233) (node236) (by decide +kernel)
noncomputable def node238 : Tree 2286 2415 13 :=
  Tree.join (node231) (node237) (by decide +kernel)
noncomputable def node239 : Tree 2437 2448 2 :=
  Tree.join (Tree.leaf leaf243) (Tree.leaf leaf244) (by decide +kernel)
noncomputable def node240 : Tree 2425 2448 3 :=
  Tree.join (Tree.leaf leaf242) (node239) (by decide +kernel)
noncomputable def node241 : Tree 2468 2478 2 :=
  Tree.join (Tree.leaf leaf246) (Tree.leaf leaf247) (by decide +kernel)
noncomputable def node242 : Tree 2452 2478 3 :=
  Tree.join (Tree.leaf leaf245) (node241) (by decide +kernel)
noncomputable def node243 : Tree 2425 2478 6 :=
  Tree.join (node240) (node242) (by decide +kernel)
noncomputable def node244 : Tree 2492 2504 2 :=
  Tree.join (Tree.leaf leaf249) (Tree.leaf leaf250) (by decide +kernel)
noncomputable def node245 : Tree 2489 2504 3 :=
  Tree.join (Tree.leaf leaf248) (node244) (by decide +kernel)
noncomputable def node246 : Tree 2513 2526 2 :=
  Tree.join (Tree.leaf leaf251) (Tree.leaf leaf252) (by decide +kernel)
noncomputable def node247 : Tree 2531 2550 2 :=
  Tree.join (Tree.leaf leaf253) (Tree.leaf leaf254) (by decide +kernel)
noncomputable def node248 : Tree 2513 2550 4 :=
  Tree.join (node246) (node247) (by decide +kernel)
noncomputable def node249 : Tree 2489 2550 7 :=
  Tree.join (node245) (node248) (by decide +kernel)
noncomputable def node250 : Tree 2425 2550 13 :=
  Tree.join (node243) (node249) (by decide +kernel)
noncomputable def node251 : Tree 2286 2550 26 :=
  Tree.join (node238) (node250) (by decide +kernel)
noncomputable def node252 : Tree 2042 2550 51 :=
  Tree.join (node226) (node251) (by decide +kernel)
noncomputable def node253 : Tree 2563 2575 2 :=
  Tree.join (Tree.leaf leaf256) (Tree.leaf leaf257) (by decide +kernel)
noncomputable def node254 : Tree 2555 2575 3 :=
  Tree.join (Tree.leaf leaf255) (node253) (by decide +kernel)
noncomputable def node255 : Tree 2596 2609 2 :=
  Tree.join (Tree.leaf leaf259) (Tree.leaf leaf260) (by decide +kernel)
noncomputable def node256 : Tree 2591 2609 3 :=
  Tree.join (Tree.leaf leaf258) (node255) (by decide +kernel)
noncomputable def node257 : Tree 2555 2609 6 :=
  Tree.join (node254) (node256) (by decide +kernel)
noncomputable def node258 : Tree 2627 2642 2 :=
  Tree.join (Tree.leaf leaf262) (Tree.leaf leaf263) (by decide +kernel)
noncomputable def node259 : Tree 2619 2642 3 :=
  Tree.join (Tree.leaf leaf261) (node258) (by decide +kernel)
noncomputable def node260 : Tree 2655 2669 2 :=
  Tree.join (Tree.leaf leaf265) (Tree.leaf leaf266) (by decide +kernel)
noncomputable def node261 : Tree 2645 2669 3 :=
  Tree.join (Tree.leaf leaf264) (node260) (by decide +kernel)
noncomputable def node262 : Tree 2619 2669 6 :=
  Tree.join (node259) (node261) (by decide +kernel)
noncomputable def node263 : Tree 2555 2669 12 :=
  Tree.join (node257) (node262) (by decide +kernel)
noncomputable def node264 : Tree 2687 2695 2 :=
  Tree.join (Tree.leaf leaf268) (Tree.leaf leaf269) (by decide +kernel)
noncomputable def node265 : Tree 2679 2695 3 :=
  Tree.join (Tree.leaf leaf267) (node264) (by decide +kernel)
noncomputable def node266 : Tree 2717 2731 2 :=
  Tree.join (Tree.leaf leaf271) (Tree.leaf leaf272) (by decide +kernel)
noncomputable def node267 : Tree 2710 2731 3 :=
  Tree.join (Tree.leaf leaf270) (node266) (by decide +kernel)
noncomputable def node268 : Tree 2679 2731 6 :=
  Tree.join (node265) (node267) (by decide +kernel)
noncomputable def node269 : Tree 2748 2758 2 :=
  Tree.join (Tree.leaf leaf274) (Tree.leaf leaf275) (by decide +kernel)
noncomputable def node270 : Tree 2742 2758 3 :=
  Tree.join (Tree.leaf leaf273) (node269) (by decide +kernel)
noncomputable def node271 : Tree 2767 2781 2 :=
  Tree.join (Tree.leaf leaf276) (Tree.leaf leaf277) (by decide +kernel)
noncomputable def node272 : Tree 2787 2799 2 :=
  Tree.join (Tree.leaf leaf278) (Tree.leaf leaf279) (by decide +kernel)
noncomputable def node273 : Tree 2767 2799 4 :=
  Tree.join (node271) (node272) (by decide +kernel)
noncomputable def node274 : Tree 2742 2799 7 :=
  Tree.join (node270) (node273) (by decide +kernel)
noncomputable def node275 : Tree 2679 2799 13 :=
  Tree.join (node268) (node274) (by decide +kernel)
noncomputable def node276 : Tree 2555 2799 25 :=
  Tree.join (node263) (node275) (by decide +kernel)
noncomputable def node277 : Tree 2812 2820 2 :=
  Tree.join (Tree.leaf leaf281) (Tree.leaf leaf282) (by decide +kernel)
noncomputable def node278 : Tree 2804 2820 3 :=
  Tree.join (Tree.leaf leaf280) (node277) (by decide +kernel)
noncomputable def node279 : Tree 2847 2852 2 :=
  Tree.join (Tree.leaf leaf284) (Tree.leaf leaf285) (by decide +kernel)
noncomputable def node280 : Tree 2832 2852 3 :=
  Tree.join (Tree.leaf leaf283) (node279) (by decide +kernel)
noncomputable def node281 : Tree 2804 2852 6 :=
  Tree.join (node278) (node280) (by decide +kernel)
noncomputable def node282 : Tree 2877 2888 2 :=
  Tree.join (Tree.leaf leaf287) (Tree.leaf leaf288) (by decide +kernel)
noncomputable def node283 : Tree 2866 2888 3 :=
  Tree.join (Tree.leaf leaf286) (node282) (by decide +kernel)
noncomputable def node284 : Tree 2895 2910 2 :=
  Tree.join (Tree.leaf leaf289) (Tree.leaf leaf290) (by decide +kernel)
noncomputable def node285 : Tree 2921 2930 2 :=
  Tree.join (Tree.leaf leaf291) (Tree.leaf leaf292) (by decide +kernel)
noncomputable def node286 : Tree 2895 2930 4 :=
  Tree.join (node284) (node285) (by decide +kernel)
noncomputable def node287 : Tree 2866 2930 7 :=
  Tree.join (node283) (node286) (by decide +kernel)
noncomputable def node288 : Tree 2804 2930 13 :=
  Tree.join (node281) (node287) (by decide +kernel)
noncomputable def node289 : Tree 2944 2967 2 :=
  Tree.join (Tree.leaf leaf294) (Tree.leaf leaf295) (by decide +kernel)
noncomputable def node290 : Tree 2941 2967 3 :=
  Tree.join (Tree.leaf leaf293) (node289) (by decide +kernel)
noncomputable def node291 : Tree 2980 2988 2 :=
  Tree.join (Tree.leaf leaf297) (Tree.leaf leaf298) (by decide +kernel)
noncomputable def node292 : Tree 2973 2988 3 :=
  Tree.join (Tree.leaf leaf296) (node291) (by decide +kernel)
noncomputable def node293 : Tree 2941 2988 6 :=
  Tree.join (node290) (node292) (by decide +kernel)
noncomputable def node294 : Tree 3007 3017 2 :=
  Tree.join (Tree.leaf leaf300) (Tree.leaf leaf301) (by decide +kernel)
noncomputable def node295 : Tree 2998 3017 3 :=
  Tree.join (Tree.leaf leaf299) (node294) (by decide +kernel)
noncomputable def node296 : Tree 3029 3035 2 :=
  Tree.join (Tree.leaf leaf302) (Tree.leaf leaf303) (by decide +kernel)
noncomputable def node297 : Tree 3050 3053 2 :=
  Tree.join (Tree.leaf leaf304) (Tree.leaf leaf305) (by decide +kernel)
noncomputable def node298 : Tree 3029 3053 4 :=
  Tree.join (node296) (node297) (by decide +kernel)
noncomputable def node299 : Tree 2998 3053 7 :=
  Tree.join (node295) (node298) (by decide +kernel)
noncomputable def node300 : Tree 2941 3053 13 :=
  Tree.join (node293) (node299) (by decide +kernel)
noncomputable def node301 : Tree 2804 3053 26 :=
  Tree.join (node288) (node300) (by decide +kernel)
noncomputable def node302 : Tree 2555 3053 51 :=
  Tree.join (node276) (node301) (by decide +kernel)
noncomputable def node303 : Tree 2042 3053 102 :=
  Tree.join (node252) (node302) (by decide +kernel)
noncomputable def node304 : Tree 3071 3100 2 :=
  Tree.join (Tree.leaf leaf307) (Tree.leaf leaf308) (by decide +kernel)
noncomputable def node305 : Tree 3057 3100 3 :=
  Tree.join (Tree.leaf leaf306) (node304) (by decide +kernel)
noncomputable def node306 : Tree 3110 3118 2 :=
  Tree.join (Tree.leaf leaf310) (Tree.leaf leaf311) (by decide +kernel)
noncomputable def node307 : Tree 3102 3118 3 :=
  Tree.join (Tree.leaf leaf309) (node306) (by decide +kernel)
noncomputable def node308 : Tree 3057 3118 6 :=
  Tree.join (node305) (node307) (by decide +kernel)
noncomputable def node309 : Tree 3136 3144 2 :=
  Tree.join (Tree.leaf leaf313) (Tree.leaf leaf314) (by decide +kernel)
noncomputable def node310 : Tree 3122 3144 3 :=
  Tree.join (Tree.leaf leaf312) (node309) (by decide +kernel)
noncomputable def node311 : Tree 3163 3177 2 :=
  Tree.join (Tree.leaf leaf316) (Tree.leaf leaf317) (by decide +kernel)
noncomputable def node312 : Tree 3154 3177 3 :=
  Tree.join (Tree.leaf leaf315) (node311) (by decide +kernel)
noncomputable def node313 : Tree 3122 3177 6 :=
  Tree.join (node310) (node312) (by decide +kernel)
noncomputable def node314 : Tree 3057 3177 12 :=
  Tree.join (node308) (node313) (by decide +kernel)
noncomputable def node315 : Tree 3199 3209 2 :=
  Tree.join (Tree.leaf leaf319) (Tree.leaf leaf320) (by decide +kernel)
noncomputable def node316 : Tree 3188 3209 3 :=
  Tree.join (Tree.leaf leaf318) (node315) (by decide +kernel)
noncomputable def node317 : Tree 3229 3238 2 :=
  Tree.join (Tree.leaf leaf322) (Tree.leaf leaf323) (by decide +kernel)
noncomputable def node318 : Tree 3217 3238 3 :=
  Tree.join (Tree.leaf leaf321) (node317) (by decide +kernel)
noncomputable def node319 : Tree 3188 3238 6 :=
  Tree.join (node316) (node318) (by decide +kernel)
noncomputable def node320 : Tree 3261 3274 2 :=
  Tree.join (Tree.leaf leaf325) (Tree.leaf leaf326) (by decide +kernel)
noncomputable def node321 : Tree 3249 3274 3 :=
  Tree.join (Tree.leaf leaf324) (node320) (by decide +kernel)
noncomputable def node322 : Tree 3280 3290 2 :=
  Tree.join (Tree.leaf leaf327) (Tree.leaf leaf328) (by decide +kernel)
noncomputable def node323 : Tree 3303 3309 2 :=
  Tree.join (Tree.leaf leaf329) (Tree.leaf leaf330) (by decide +kernel)
noncomputable def node324 : Tree 3280 3309 4 :=
  Tree.join (node322) (node323) (by decide +kernel)
noncomputable def node325 : Tree 3249 3309 7 :=
  Tree.join (node321) (node324) (by decide +kernel)
noncomputable def node326 : Tree 3188 3309 13 :=
  Tree.join (node319) (node325) (by decide +kernel)
noncomputable def node327 : Tree 3057 3309 25 :=
  Tree.join (node314) (node326) (by decide +kernel)
noncomputable def node328 : Tree 3324 3339 2 :=
  Tree.join (Tree.leaf leaf332) (Tree.leaf leaf333) (by decide +kernel)
noncomputable def node329 : Tree 3320 3339 3 :=
  Tree.join (Tree.leaf leaf331) (node328) (by decide +kernel)
noncomputable def node330 : Tree 3361 3366 2 :=
  Tree.join (Tree.leaf leaf335) (Tree.leaf leaf336) (by decide +kernel)
noncomputable def node331 : Tree 3346 3366 3 :=
  Tree.join (Tree.leaf leaf334) (node330) (by decide +kernel)
noncomputable def node332 : Tree 3320 3366 6 :=
  Tree.join (node329) (node331) (by decide +kernel)
noncomputable def node333 : Tree 3387 3399 2 :=
  Tree.join (Tree.leaf leaf338) (Tree.leaf leaf339) (by decide +kernel)
noncomputable def node334 : Tree 3377 3399 3 :=
  Tree.join (Tree.leaf leaf337) (node333) (by decide +kernel)
noncomputable def node335 : Tree 3402 3407 2 :=
  Tree.join (Tree.leaf leaf340) (Tree.leaf leaf341) (by decide +kernel)
noncomputable def node336 : Tree 3425 3440 2 :=
  Tree.join (Tree.leaf leaf342) (Tree.leaf leaf343) (by decide +kernel)
noncomputable def node337 : Tree 3402 3440 4 :=
  Tree.join (node335) (node336) (by decide +kernel)
noncomputable def node338 : Tree 3377 3440 7 :=
  Tree.join (node334) (node337) (by decide +kernel)
noncomputable def node339 : Tree 3320 3440 13 :=
  Tree.join (node332) (node338) (by decide +kernel)
noncomputable def node340 : Tree 3452 3469 2 :=
  Tree.join (Tree.leaf leaf345) (Tree.leaf leaf346) (by decide +kernel)
noncomputable def node341 : Tree 3448 3469 3 :=
  Tree.join (Tree.leaf leaf344) (node340) (by decide +kernel)
noncomputable def node342 : Tree 3490 3511 2 :=
  Tree.join (Tree.leaf leaf348) (Tree.leaf leaf349) (by decide +kernel)
noncomputable def node343 : Tree 3481 3511 3 :=
  Tree.join (Tree.leaf leaf347) (node342) (by decide +kernel)
noncomputable def node344 : Tree 3448 3511 6 :=
  Tree.join (node341) (node343) (by decide +kernel)
noncomputable def node345 : Tree 3521 3534 2 :=
  Tree.join (Tree.leaf leaf351) (Tree.leaf leaf352) (by decide +kernel)
noncomputable def node346 : Tree 3512 3534 3 :=
  Tree.join (Tree.leaf leaf350) (node345) (by decide +kernel)
noncomputable def node347 : Tree 3537 3544 2 :=
  Tree.join (Tree.leaf leaf353) (Tree.leaf leaf354) (by decide +kernel)
noncomputable def node348 : Tree 3554 3570 2 :=
  Tree.join (Tree.leaf leaf355) (Tree.leaf leaf356) (by decide +kernel)
noncomputable def node349 : Tree 3537 3570 4 :=
  Tree.join (node347) (node348) (by decide +kernel)
noncomputable def node350 : Tree 3512 3570 7 :=
  Tree.join (node346) (node349) (by decide +kernel)
noncomputable def node351 : Tree 3448 3570 13 :=
  Tree.join (node344) (node350) (by decide +kernel)
noncomputable def node352 : Tree 3320 3570 26 :=
  Tree.join (node339) (node351) (by decide +kernel)
noncomputable def node353 : Tree 3057 3570 51 :=
  Tree.join (node327) (node352) (by decide +kernel)
noncomputable def node354 : Tree 3590 3600 2 :=
  Tree.join (Tree.leaf leaf358) (Tree.leaf leaf359) (by decide +kernel)
noncomputable def node355 : Tree 3577 3600 3 :=
  Tree.join (Tree.leaf leaf357) (node354) (by decide +kernel)
noncomputable def node356 : Tree 3621 3631 2 :=
  Tree.join (Tree.leaf leaf361) (Tree.leaf leaf362) (by decide +kernel)
noncomputable def node357 : Tree 3608 3631 3 :=
  Tree.join (Tree.leaf leaf360) (node356) (by decide +kernel)
noncomputable def node358 : Tree 3577 3631 6 :=
  Tree.join (node355) (node357) (by decide +kernel)
noncomputable def node359 : Tree 3646 3656 2 :=
  Tree.join (Tree.leaf leaf364) (Tree.leaf leaf365) (by decide +kernel)
noncomputable def node360 : Tree 3640 3656 3 :=
  Tree.join (Tree.leaf leaf363) (node359) (by decide +kernel)
noncomputable def node361 : Tree 3672 3678 2 :=
  Tree.join (Tree.leaf leaf366) (Tree.leaf leaf367) (by decide +kernel)
noncomputable def node362 : Tree 3685 3694 2 :=
  Tree.join (Tree.leaf leaf368) (Tree.leaf leaf369) (by decide +kernel)
noncomputable def node363 : Tree 3672 3694 4 :=
  Tree.join (node361) (node362) (by decide +kernel)
noncomputable def node364 : Tree 3640 3694 7 :=
  Tree.join (node360) (node363) (by decide +kernel)
noncomputable def node365 : Tree 3577 3694 13 :=
  Tree.join (node358) (node364) (by decide +kernel)
noncomputable def node366 : Tree 3716 3725 2 :=
  Tree.join (Tree.leaf leaf371) (Tree.leaf leaf372) (by decide +kernel)
noncomputable def node367 : Tree 3714 3725 3 :=
  Tree.join (Tree.leaf leaf370) (node366) (by decide +kernel)
noncomputable def node368 : Tree 3746 3755 2 :=
  Tree.join (Tree.leaf leaf374) (Tree.leaf leaf375) (by decide +kernel)
noncomputable def node369 : Tree 3739 3755 3 :=
  Tree.join (Tree.leaf leaf373) (node368) (by decide +kernel)
noncomputable def node370 : Tree 3714 3755 6 :=
  Tree.join (node367) (node369) (by decide +kernel)
noncomputable def node371 : Tree 3776 3787 2 :=
  Tree.join (Tree.leaf leaf377) (Tree.leaf leaf378) (by decide +kernel)
noncomputable def node372 : Tree 3764 3787 3 :=
  Tree.join (Tree.leaf leaf376) (node371) (by decide +kernel)
noncomputable def node373 : Tree 3804 3813 2 :=
  Tree.join (Tree.leaf leaf379) (Tree.leaf leaf380) (by decide +kernel)
noncomputable def node374 : Tree 3822 3831 2 :=
  Tree.join (Tree.leaf leaf381) (Tree.leaf leaf382) (by decide +kernel)
noncomputable def node375 : Tree 3804 3831 4 :=
  Tree.join (node373) (node374) (by decide +kernel)
noncomputable def node376 : Tree 3764 3831 7 :=
  Tree.join (node372) (node375) (by decide +kernel)
noncomputable def node377 : Tree 3714 3831 13 :=
  Tree.join (node370) (node376) (by decide +kernel)
noncomputable def node378 : Tree 3577 3831 26 :=
  Tree.join (node365) (node377) (by decide +kernel)
noncomputable def node379 : Tree 3854 3865 2 :=
  Tree.join (Tree.leaf leaf384) (Tree.leaf leaf385) (by decide +kernel)
noncomputable def node380 : Tree 3840 3865 3 :=
  Tree.join (Tree.leaf leaf383) (node379) (by decide +kernel)
noncomputable def node381 : Tree 3881 3889 2 :=
  Tree.join (Tree.leaf leaf387) (Tree.leaf leaf388) (by decide +kernel)
noncomputable def node382 : Tree 3871 3889 3 :=
  Tree.join (Tree.leaf leaf386) (node381) (by decide +kernel)
noncomputable def node383 : Tree 3840 3889 6 :=
  Tree.join (node380) (node382) (by decide +kernel)
noncomputable def node384 : Tree 3908 3920 2 :=
  Tree.join (Tree.leaf leaf390) (Tree.leaf leaf391) (by decide +kernel)
noncomputable def node385 : Tree 3897 3920 3 :=
  Tree.join (Tree.leaf leaf389) (node384) (by decide +kernel)
noncomputable def node386 : Tree 3925 3936 2 :=
  Tree.join (Tree.leaf leaf392) (Tree.leaf leaf393) (by decide +kernel)
noncomputable def node387 : Tree 3946 3959 2 :=
  Tree.join (Tree.leaf leaf394) (Tree.leaf leaf395) (by decide +kernel)
noncomputable def node388 : Tree 3925 3959 4 :=
  Tree.join (node386) (node387) (by decide +kernel)
noncomputable def node389 : Tree 3897 3959 7 :=
  Tree.join (node385) (node388) (by decide +kernel)
noncomputable def node390 : Tree 3840 3959 13 :=
  Tree.join (node383) (node389) (by decide +kernel)
noncomputable def node391 : Tree 3975 3991 2 :=
  Tree.join (Tree.leaf leaf397) (Tree.leaf leaf398) (by decide +kernel)
noncomputable def node392 : Tree 3963 3991 3 :=
  Tree.join (Tree.leaf leaf396) (node391) (by decide +kernel)
noncomputable def node393 : Tree 4013 4020 2 :=
  Tree.join (Tree.leaf leaf400) (Tree.leaf leaf401) (by decide +kernel)
noncomputable def node394 : Tree 3995 4020 3 :=
  Tree.join (Tree.leaf leaf399) (node393) (by decide +kernel)
noncomputable def node395 : Tree 3963 4020 6 :=
  Tree.join (node392) (node394) (by decide +kernel)
noncomputable def node396 : Tree 4037 4050 2 :=
  Tree.join (Tree.leaf leaf403) (Tree.leaf leaf404) (by decide +kernel)
noncomputable def node397 : Tree 4028 4050 3 :=
  Tree.join (Tree.leaf leaf402) (node396) (by decide +kernel)
noncomputable def node398 : Tree 4059 4067 2 :=
  Tree.join (Tree.leaf leaf405) (Tree.leaf leaf406) (by decide +kernel)
noncomputable def node399 : Tree 4080 4090 2 :=
  Tree.join (Tree.leaf leaf407) (Tree.leaf leaf408) (by decide +kernel)
noncomputable def node400 : Tree 4059 4090 4 :=
  Tree.join (node398) (node399) (by decide +kernel)
noncomputable def node401 : Tree 4028 4090 7 :=
  Tree.join (node397) (node400) (by decide +kernel)
noncomputable def node402 : Tree 3963 4090 13 :=
  Tree.join (node395) (node401) (by decide +kernel)
noncomputable def node403 : Tree 3840 4090 26 :=
  Tree.join (node390) (node402) (by decide +kernel)
noncomputable def node404 : Tree 3577 4090 52 :=
  Tree.join (node378) (node403) (by decide +kernel)
noncomputable def node405 : Tree 3057 4090 103 :=
  Tree.join (node353) (node404) (by decide +kernel)
noncomputable def node406 : Tree 2042 4090 205 :=
  Tree.join (node303) (node405) (by decide +kernel)
noncomputable def node407 : Tree 9 4090 409 :=
  Tree.join (node202) (node406) (by decide +kernel)
noncomputable def certificate : Tree 9 4090 409 := node407
end RHBatch01HeightBracketData
noncomputable def TaoFivePrimes_RHBatch01HeightBracketTree := RHBatch01HeightBracketData.certificate


