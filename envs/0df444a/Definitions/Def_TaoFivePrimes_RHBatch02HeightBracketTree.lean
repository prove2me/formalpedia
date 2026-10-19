-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch02HeightBracketTree
-- name    : TaoFivePrimes_RHBatch02HeightBracketTree
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T18:27:46.882001+00:00
-- url     : https://prove2.me/theorems/e9a99fd3-082c-4d7f-97e9-928aa1c709be
-- title:
--   TaoFivePrimes_RHBatch02HeightBracketTree
-- statement:
--   An ordered tree of 408 proposed sign brackets from a 1/32-spaced high-height grid. Each leaf carries ordinary proofs of coordinate bounds, interval ordering and opposite strict signs of its proposed dyadic boxes. Each join carries a proof that its subtrees are ordered. These certificates assert no containment of normalized zeta values.
-- source:
--   Finite structural sign and order certificates, generated from the native FLINT 3.6.0 Platt FFT/interpolation proposal on [3289999616,3289999744]. Numeric tests are necessary constructor proof fields and use ordinary decide +kernel. No value containment, total zero count or RH conclusion is asserted. Platt method: DOI 10.1090/mcom/3198. The surrounding project preserves attribution to sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham.

/- Structural certificates for proposed high-height sign brackets.
Every finite sign/order test is a necessary proof field checked in ordinary Lean.
Containment of mathematical zeta values is NOT asserted by these records.
Numerical proposals: Platt/FLINT. Surrounding xi/theta work: sometik179 and
Gabewhigham. -/
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace RHBatch02HeightBracketData
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
  ⟨6, 7, (Int.negSucc 149740448470504117), (Int.negSucc 149740448470504103), (Int.ofNat 71863942817219602), (Int.ofNat 71863942817219608),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf1 : Bracket :=
  ⟨19, 20, (Int.ofNat 434884707024124247), (Int.ofNat 434884707024124259), (Int.negSucc 5167138594114302), (Int.negSucc 5167138594114287),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf2 : Bracket :=
  ⟨30, 31, (Int.negSucc 423596175668369371), (Int.negSucc 423596175668369351), (Int.ofNat 204204249854584727), (Int.ofNat 204204249854584734),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf3 : Bracket :=
  ⟨46, 47, (Int.ofNat 507611431006097703), (Int.ofNat 507611431006097712), (Int.negSucc 75902647146889068), (Int.negSucc 75902647146889054),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf4 : Bracket :=
  ⟨56, 57, (Int.negSucc 5654896432507288), (Int.negSucc 5654896432507284), (Int.ofNat 404086271970815294), (Int.ofNat 404086271970815313),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf5 : Bracket :=
  ⟨68, 69, (Int.ofNat 151752388676006287), (Int.ofNat 151752388676006300), (Int.negSucc 190286884033265676), (Int.negSucc 190286884033265662),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf6 : Bracket :=
  ⟨83, 84, (Int.negSucc 51790172439130286), (Int.negSucc 51790172439130274), (Int.ofNat 27356974004211795), (Int.ofNat 27356974004211802),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf7 : Bracket :=
  ⟨90, 91, (Int.ofNat 11272458832622660), (Int.ofNat 11272458832622680), (Int.negSucc 16350866561384269), (Int.negSucc 16350866561384254),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf8 : Bracket :=
  ⟨96, 97, (Int.negSucc 3633300493845510), (Int.negSucc 3633300493845498), (Int.ofNat 23709744526143888), (Int.ofNat 23709744526143907),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf9 : Bracket :=
  ⟨108, 109, (Int.ofNat 6539276764399302), (Int.ofNat 6539276764399311), (Int.negSucc 5230502274197499), (Int.negSucc 5230502274197489),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf10 : Bracket :=
  ⟨112, 113, (Int.negSucc 3548596044763498), (Int.negSucc 3548596044763482), (Int.ofNat 4698382962022346), (Int.ofNat 4698382962022366),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf11 : Bracket :=
  ⟨116, 117, (Int.ofNat 10737412798775237), (Int.ofNat 10737412798775252), (Int.negSucc 4115725674790812), (Int.negSucc 4115725674790795),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf12 : Bracket :=
  ⟨132, 133, (Int.negSucc 69175203932196056), (Int.negSucc 69175203932196043), (Int.ofNat 40930137147824751), (Int.ofNat 40930137147824766),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf13 : Bracket :=
  ⟨143, 144, (Int.ofNat 65006121253173370), (Int.ofNat 65006121253173377), (Int.negSucc 55676503598735658), (Int.negSucc 55676503598735655),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf14 : Bracket :=
  ⟨158, 159, (Int.negSucc 45015651538545095), (Int.negSucc 45015651538545080), (Int.ofNat 2998879201467570), (Int.ofNat 2998879201467588),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf15 : Bracket :=
  ⟨165, 166, (Int.ofNat 5375516887698301), (Int.ofNat 5375516887698321), (Int.negSucc 12384249898346505), (Int.negSucc 12384249898346487),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf16 : Bracket :=
  ⟨171, 172, (Int.negSucc 864065876703747), (Int.negSucc 864065876703735), (Int.ofNat 16903792364622346), (Int.ofNat 16903792364622362),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf17 : Bracket :=
  ⟨176, 177, (Int.ofNat 25288558476330800), (Int.ofNat 25288558476330816), (Int.negSucc 4840645512708775), (Int.negSucc 4840645512708766),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf18 : Bracket :=
  ⟨193, 194, (Int.negSucc 2487589163451103), (Int.negSucc 2487589163451090), (Int.ofNat 54768532417903095), (Int.ofNat 54768532417903107),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf19 : Bracket :=
  ⟨197, 198, (Int.ofNat 43370517379074286), (Int.ofNat 43370517379074301), (Int.negSucc 30187154482319312), (Int.negSucc 30187154482319296),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf20 : Bracket :=
  ⟨212, 213, (Int.negSucc 107972154129337687), (Int.negSucc 107972154129337671), (Int.ofNat 127893106851160115), (Int.ofNat 127893106851160123),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf21 : Bracket :=
  ⟨226, 227, (Int.ofNat 69456974582550865), (Int.ofNat 69456974582550883), (Int.negSucc 62157745651452168), (Int.negSucc 62157745651452157),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf22 : Bracket :=
  ⟨233, 234, (Int.negSucc 49844084688279474), (Int.negSucc 49844084688279459), (Int.ofNat 58676059783334453), (Int.ofNat 58676059783334469),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf23 : Bracket :=
  ⟨247, 248, (Int.ofNat 51611196168192366), (Int.ofNat 51611196168192378), (Int.negSucc 6535032340711126), (Int.negSucc 6535032340711118),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf24 : Bracket :=
  ⟨252, 253, (Int.negSucc 32023447884151129), (Int.negSucc 32023447884151118), (Int.ofNat 4101951645375533), (Int.ofNat 4101951645375540),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf25 : Bracket :=
  ⟨263, 264, (Int.ofNat 31067615096986006), (Int.ofNat 31067615096986015), (Int.negSucc 11402369128677432), (Int.negSucc 11402369128677428),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf26 : Bracket :=
  ⟨270, 271, (Int.negSucc 26667285257733483), (Int.negSucc 26667285257733463), (Int.ofNat 7290909359626224), (Int.ofNat 7290909359626242),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf27 : Bracket :=
  ⟨276, 277, (Int.ofNat 23499273547742122), (Int.ofNat 23499273547742130), (Int.negSucc 37618184079588894), (Int.negSucc 37618184079588876),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf28 : Bracket :=
  ⟨289, 290, (Int.negSucc 173087826132630467), (Int.negSucc 173087826132630449), (Int.ofNat 55230145621017167), (Int.ofNat 55230145621017178),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf29 : Bracket :=
  ⟨304, 305, (Int.ofNat 15292982315755837), (Int.ofNat 15292982315755841), (Int.negSucc 226743084141256951), (Int.negSucc 226743084141256931),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf30 : Bracket :=
  ⟨315, 316, (Int.negSucc 87864432909294435), (Int.negSucc 87864432909294417), (Int.ofNat 17551200721271020), (Int.ofNat 17551200721271027),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf31 : Bracket :=
  ⟨319, 320, (Int.ofNat 58827480523446921), (Int.ofNat 58827480523446940), (Int.negSucc 31930362624272494), (Int.negSucc 31930362624272491),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf32 : Bracket :=
  ⟨333, 334, (Int.negSucc 285290205399500479), (Int.negSucc 285290205399500460), (Int.ofNat 5175307743798084), (Int.ofNat 5175307743798100),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf33 : Bracket :=
  ⟨347, 348, (Int.ofNat 107246792414204316), (Int.ofNat 107246792414204331), (Int.negSucc 64792231880177271), (Int.negSucc 64792231880177265),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf34 : Bracket :=
  ⟨356, 357, (Int.negSucc 8134590191957705), (Int.negSucc 8134590191957697), (Int.ofNat 83550431414091159), (Int.ofNat 83550431414091168),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf35 : Bracket :=
  ⟨363, 364, (Int.ofNat 48280921619015394), (Int.ofNat 48280921619015415), (Int.negSucc 50131923074212605), (Int.negSucc 50131923074212596),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf36 : Bracket :=
  ⟨373, 374, (Int.negSucc 55598339180183951), (Int.negSucc 55598339180183937), (Int.ofNat 94854076695398341), (Int.ofNat 94854076695398353),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf37 : Bracket :=
  ⟨386, 387, (Int.ofNat 8984078684296934), (Int.ofNat 8984078684296953), (Int.negSucc 137915043609691622), (Int.negSucc 137915043609691611),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf38 : Bracket :=
  ⟨396, 397, (Int.negSucc 75759324868233482), (Int.negSucc 75759324868233471), (Int.ofNat 18373859573971735), (Int.ofNat 18373859573971752),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf39 : Bracket :=
  ⟨403, 404, (Int.ofNat 74768962573529327), (Int.ofNat 74768962573529339), (Int.negSucc 1661507023634726), (Int.negSucc 1661507023634718),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf40 : Bracket :=
  ⟨414, 415, (Int.negSucc 2059837900561290), (Int.negSucc 2059837900561281), (Int.ofNat 105658969841362680), (Int.ofNat 105658969841362696),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf41 : Bracket :=
  ⟨423, 424, (Int.ofNat 116594509456835380), (Int.ofNat 116594509456835395), (Int.negSucc 12131356369346244), (Int.negSucc 12131356369346234),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf42 : Bracket :=
  ⟨435, 436, (Int.negSucc 23534877746033454), (Int.negSucc 23534877746033440), (Int.ofNat 138733314471517227), (Int.ofNat 138733314471517237),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf43 : Bracket :=
  ⟨447, 448, (Int.ofNat 88839835653704034), (Int.ofNat 88839835653704051), (Int.negSucc 47742662482348699), (Int.negSucc 47742662482348695),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf44 : Bracket :=
  ⟨459, 460, (Int.negSucc 59127322915239973), (Int.negSucc 59127322915239955), (Int.ofNat 4775032988807488), (Int.ofNat 4775032988807503),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf45 : Bracket :=
  ⟨468, 469, (Int.ofNat 16485226317369170), (Int.ofNat 16485226317369177), (Int.negSucc 9928908908161388), (Int.negSucc 9928908908161378),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf46 : Bracket :=
  ⟨476, 477, (Int.negSucc 7242645605712089), (Int.negSucc 7242645605712076), (Int.ofNat 5225586727352592), (Int.ofNat 5225586727352602),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf47 : Bracket :=
  ⟨480, 481, (Int.ofNat 9334359804917093), (Int.ofNat 9334359804917097), (Int.negSucc 3179070559106633), (Int.negSucc 3179070559106621),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf48 : Bracket :=
  ⟨491, 492, (Int.negSucc 31644700727173069), (Int.negSucc 31644700727173056), (Int.ofNat 6632974835237511), (Int.ofNat 6632974835237518),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf49 : Bracket :=
  ⟨502, 503, (Int.ofNat 16702620110169080), (Int.ofNat 16702620110169090), (Int.negSucc 33287409361431344), (Int.negSucc 33287409361431333),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf50 : Bracket :=
  ⟨515, 516, (Int.negSucc 3483218146840821), (Int.negSucc 3483218146840812), (Int.ofNat 15594814411111603), (Int.ofNat 15594814411111606),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf51 : Bracket :=
  ⟨519, 520, (Int.ofNat 13695465979734288), (Int.ofNat 13695465979734298), (Int.negSucc 2726463938751694), (Int.negSucc 2726463938751691),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf52 : Bracket :=
  ⟨528, 529, (Int.negSucc 8604056332397036), (Int.negSucc 8604056332397032), (Int.ofNat 14797298645514976), (Int.ofNat 14797298645514982),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf53 : Bracket :=
  ⟨532, 533, (Int.ofNat 22765498986321971), (Int.ofNat 22765498986321987), (Int.negSucc 15332289457870932), (Int.negSucc 15332289457870922),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf54 : Bracket :=
  ⟨548, 549, (Int.negSucc 47623784165154335), (Int.negSucc 47623784165154323), (Int.ofNat 342160634866590158), (Int.ofNat 342160634866590176),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf55 : Bracket :=
  ⟨565, 566, (Int.ofNat 122780409773056274), (Int.ofNat 122780409773056285), (Int.negSucc 186560201837944513), (Int.negSucc 186560201837944501),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf56 : Bracket :=
  ⟨573, 574, (Int.negSucc 87106205361643870), (Int.negSucc 87106205361643858), (Int.ofNat 142909147786982834), (Int.ofNat 142909147786982847),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf57 : Bracket :=
  ⟨583, 584, (Int.ofNat 144783680691529498), (Int.ofNat 144783680691529505), (Int.negSucc 104668986014256721), (Int.negSucc 104668986014256717),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf58 : Bracket :=
  ⟨593, 594, (Int.negSucc 253392000369476619), (Int.negSucc 253392000369476606), (Int.ofNat 25513919336617494), (Int.ofNat 25513919336617512),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf59 : Bracket :=
  ⟨608, 609, (Int.ofNat 50024404694250027), (Int.ofNat 50024404694250040), (Int.negSucc 74820962572606461), (Int.negSucc 74820962572606447),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf60 : Bracket :=
  ⟨613, 614, (Int.negSucc 37708675485946142), (Int.negSucc 37708675485946134), (Int.ofNat 82730498942865252), (Int.ofNat 82730498942865266),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf61 : Bracket :=
  ⟨624, 625, (Int.ofNat 154878379086239530), (Int.ofNat 154878379086239544), (Int.negSucc 53176707562669626), (Int.negSucc 53176707562669606),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf62 : Bracket :=
  ⟨638, 639, (Int.negSucc 58472566715020757), (Int.negSucc 58472566715020741), (Int.ofNat 53868728744603475), (Int.ofNat 53868728744603482),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf63 : Bracket :=
  ⟨643, 644, (Int.ofNat 80623141234001828), (Int.ofNat 80623141234001836), (Int.negSucc 13425652376715104), (Int.negSucc 13425652376715087),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf64 : Bracket :=
  ⟨656, 657, (Int.negSucc 91394322302155308), (Int.negSucc 91394322302155296), (Int.ofNat 68252797743618663), (Int.ofNat 68252797743618671),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf65 : Bracket :=
  ⟨667, 668, (Int.ofNat 75329950624794749), (Int.ofNat 75329950624794766), (Int.negSucc 42666917006315099), (Int.negSucc 42666917006315087),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf66 : Bracket :=
  ⟨677, 678, (Int.negSucc 16628035971186201), (Int.negSucc 16628035971186193), (Int.ofNat 71736694398070114), (Int.ofNat 71736694398070136),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf67 : Bracket :=
  ⟨688, 689, (Int.ofNat 37986936534368216), (Int.ofNat 37986936534368222), (Int.negSucc 10125156681905926), (Int.negSucc 10125156681905906),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf68 : Bracket :=
  ⟨695, 696, (Int.negSucc 6559656481327415), (Int.negSucc 6559656481327401), (Int.ofNat 26633229867822461), (Int.ofNat 26633229867822476),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf69 : Bracket :=
  ⟨702, 703, (Int.ofNat 35309785017801122), (Int.ofNat 35309785017801141), (Int.negSucc 8197236684780234), (Int.negSucc 8197236684780218),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf70 : Bracket :=
  ⟨713, 714, (Int.negSucc 18608081012333267), (Int.negSucc 18608081012333254), (Int.ofNat 61510073437295309), (Int.ofNat 61510073437295326),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf71 : Bracket :=
  ⟨726, 727, (Int.ofNat 45921047751617200), (Int.ofNat 45921047751617219), (Int.negSucc 6892982369878441), (Int.negSucc 6892982369878425),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf72 : Bracket :=
  ⟨731, 732, (Int.negSucc 35391736094293110), (Int.negSucc 35391736094293098), (Int.ofNat 4859022010391920), (Int.ofNat 4859022010391936),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf73 : Bracket :=
  ⟨745, 746, (Int.ofNat 7921489946206960), (Int.ofNat 7921489946206980), (Int.negSucc 36909028769838052), (Int.negSucc 36909028769838044),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf74 : Bracket :=
  ⟨750, 751, (Int.negSucc 8392683444049789), (Int.negSucc 8392683444049773), (Int.ofNat 53317922472051713), (Int.ofNat 53317922472051730),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf75 : Bracket :=
  ⟨763, 764, (Int.ofNat 20978008188713579), (Int.ofNat 20978008188713589), (Int.negSucc 101185696231532638), (Int.negSucc 101185696231532626),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf76 : Bracket :=
  ⟨772, 773, (Int.negSucc 51332231858505620), (Int.negSucc 51332231858505608), (Int.ofNat 110129098742420988), (Int.ofNat 110129098742421007),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf77 : Bracket :=
  ⟨787, 788, (Int.ofNat 107730037526574631), (Int.ofNat 107730037526574649), (Int.negSucc 27972176309014347), (Int.negSucc 27972176309014341),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf78 : Bracket :=
  ⟨797, 798, (Int.negSucc 18585099075520101), (Int.negSucc 18585099075520086), (Int.ofNat 43698506017092971), (Int.ofNat 43698506017092984),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf79 : Bracket :=
  ⟨806, 807, (Int.ofNat 17984978272305000), (Int.ofNat 17984978272305009), (Int.negSucc 9738585663345166), (Int.negSucc 9738585663345151),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf80 : Bracket :=
  ⟨810, 811, (Int.negSucc 17065812263184394), (Int.negSucc 17065812263184384), (Int.ofNat 9064821101657969), (Int.ofNat 9064821101657989),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf81 : Bracket :=
  ⟨821, 822, (Int.ofNat 9237445222783484), (Int.ofNat 9237445222783501), (Int.negSucc 82795295227031604), (Int.negSucc 82795295227031585),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf82 : Bracket :=
  ⟨833, 834, (Int.negSucc 83671499439800869), (Int.negSucc 83671499439800859), (Int.ofNat 45702371192034019), (Int.ofNat 45702371192034040),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf83 : Bracket :=
  ⟨845, 846, (Int.ofNat 84620487438046903), (Int.ofNat 84620487438046922), (Int.negSucc 5213167988024199), (Int.negSucc 5213167988024185),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf84 : Bracket :=
  ⟨853, 854, (Int.negSucc 53791603386066829), (Int.negSucc 53791603386066812), (Int.ofNat 7356751251210933), (Int.ofNat 7356751251210944),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf85 : Bracket :=
  ⟨862, 863, (Int.ofNat 34088773769645324), (Int.ofNat 34088773769645333), (Int.negSucc 32199876684599926), (Int.negSucc 32199876684599918),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf86 : Bracket :=
  ⟨871, 872, (Int.negSucc 66065658572277634), (Int.negSucc 66065658572277619), (Int.ofNat 14828118392067541), (Int.ofNat 14828118392067556),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf87 : Bracket :=
  ⟨884, 885, (Int.ofNat 16311944474058086), (Int.ofNat 16311944474058092), (Int.negSucc 2294487728361725), (Int.negSucc 2294487728361711),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf88 : Bracket :=
  ⟨885, 886, (Int.negSucc 2294487728361725), (Int.negSucc 2294487728361711), (Int.ofNat 9890822701727500), (Int.ofNat 9890822701727517),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf89 : Bracket :=
  ⟨898, 899, (Int.ofNat 249424699302661464), (Int.ofNat 249424699302661478), (Int.negSucc 71945539628736070), (Int.negSucc 71945539628736062),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf90 : Bracket :=
  ⟨917, 918, (Int.negSucc 131697226333778975), (Int.negSucc 131697226333778955), (Int.ofNat 210875023341208719), (Int.ofNat 210875023341208730),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf91 : Bracket :=
  ⟨925, 926, (Int.ofNat 62376220645008369), (Int.ofNat 62376220645008377), (Int.negSucc 187666563156982010), (Int.negSucc 187666563156981994),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf92 : Bracket :=
  ⟨935, 936, (Int.negSucc 234330072810743938), (Int.negSucc 234330072810743919), (Int.ofNat 5681513136731401), (Int.ofNat 5681513136731417),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf93 : Bracket :=
  ⟨944, 945, (Int.ofNat 194355131660239584), (Int.ofNat 194355131660239587), (Int.negSucc 68919427059363394), (Int.negSucc 68919427059363381),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf94 : Bracket :=
  ⟨958, 959, (Int.negSucc 117673512793991407), (Int.negSucc 117673512793991396), (Int.ofNat 162361786676290513), (Int.ofNat 162361786676290526),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf95 : Bracket :=
  ⟨969, 970, (Int.ofNat 14492614082650236), (Int.ofNat 14492614082650244), (Int.negSucc 181514026215008221), (Int.negSucc 181514026215008205),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf96 : Bracket :=
  ⟨981, 982, (Int.negSucc 81686690479033830), (Int.negSucc 81686690479033816), (Int.ofNat 12654963538463963), (Int.ofNat 12654963538463980),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf97 : Bracket :=
  ⟨989, 990, (Int.ofNat 29803173580193934), (Int.ofNat 29803173580193943), (Int.negSucc 19034786425371922), (Int.negSucc 19034786425371909),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf98 : Bracket :=
  ⟨998, 999, (Int.negSucc 15344666227366990), (Int.negSucc 15344666227366978), (Int.ofNat 19987060271895443), (Int.ofNat 19987060271895453),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf99 : Bracket :=
  ⟨1005, 1006, (Int.ofNat 29675911834407820), (Int.ofNat 29675911834407832), (Int.negSucc 6407813927787629), (Int.negSucc 6407813927787615),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf100 : Bracket :=
  ⟨1019, 1020, (Int.negSucc 18289898998351853), (Int.negSucc 18289898998351840), (Int.ofNat 1031565521216206), (Int.ofNat 1031565521216209),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf101 : Bracket :=
  ⟨1025, 1026, (Int.ofNat 914547108832974), (Int.ofNat 914547108832978), (Int.negSucc 6295044658381795), (Int.negSucc 6295044658381779),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf102 : Bracket :=
  ⟨1028, 1029, (Int.negSucc 7457100364826578), (Int.negSucc 7457100364826576), (Int.ofNat 2066458611379877), (Int.ofNat 2066458611379892),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf103 : Bracket :=
  ⟨1041, 1042, (Int.ofNat 2749349830986509), (Int.ofNat 2749349830986523), (Int.negSucc 57043248149543786), (Int.negSucc 57043248149543771),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf104 : Bracket :=
  ⟨1050, 1051, (Int.negSucc 26030735592006042), (Int.negSucc 26030735592006030), (Int.ofNat 87258583256665551), (Int.ofNat 87258583256665557),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf105 : Bracket :=
  ⟨1068, 1069, (Int.ofNat 2288166592335617), (Int.ofNat 2288166592335634), (Int.negSucc 64679513090543927), (Int.negSucc 64679513090543913),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf106 : Bracket :=
  ⟨1074, 1075, (Int.negSucc 6496348090679053), (Int.negSucc 6496348090679038), (Int.ofNat 51313609266477904), (Int.ofNat 51313609266477922),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf107 : Bracket :=
  ⟨1083, 1084, (Int.ofNat 14723666865956178), (Int.ofNat 14723666865956187), (Int.negSucc 65424118561815840), (Int.negSucc 65424118561815836),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf108 : Bracket :=
  ⟨1096, 1097, (Int.negSucc 8784856583208820), (Int.negSucc 8784856583208805), (Int.ofNat 45750482320427996), (Int.ofNat 45750482320428014),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf109 : Bracket :=
  ⟨1102, 1103, (Int.ofNat 37800438152685122), (Int.ofNat 37800438152685141), (Int.negSucc 12175142349797648), (Int.negSucc 12175142349797635),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf110 : Bracket :=
  ⟨1114, 1115, (Int.negSucc 15386124200385191), (Int.negSucc 15386124200385180), (Int.ofNat 28094796431023394), (Int.ofNat 28094796431023402),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf111 : Bracket :=
  ⟨1120, 1121, (Int.ofNat 10380671509762679), (Int.ofNat 10380671509762682), (Int.negSucc 37699930005192168), (Int.negSucc 37699930005192154),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf112 : Bracket :=
  ⟨1129, 1130, (Int.negSucc 54469433658873292), (Int.negSucc 54469433658873282), (Int.ofNat 29792454758933041), (Int.ofNat 29792454758933056),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf113 : Bracket :=
  ⟨1138, 1139, (Int.ofNat 13395448822148494), (Int.ofNat 13395448822148504), (Int.negSucc 170361923734194501), (Int.negSucc 170361923734194487),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf114 : Bracket :=
  ⟨1150, 1151, (Int.negSucc 203899614017252934), (Int.negSucc 203899614017252917), (Int.ofNat 271814946982361169), (Int.ofNat 271814946982361178),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf115 : Bracket :=
  ⟨1168, 1169, (Int.ofNat 362717565885903498), (Int.ofNat 362717565885903506), (Int.negSucc 40583548002194106), (Int.negSucc 40583548002194089),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf116 : Bracket :=
  ⟨1179, 1180, (Int.negSucc 81764185500628541), (Int.negSucc 81764185500628534), (Int.ofNat 27854919436375359), (Int.ofNat 27854919436375376),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf117 : Bracket :=
  ⟨1184, 1185, (Int.ofNat 53037209354484827), (Int.ofNat 53037209354484842), (Int.negSucc 21368987764094623), (Int.negSucc 21368987764094608),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf118 : Bracket :=
  ⟨1191, 1192, (Int.negSucc 94454342368778327), (Int.negSucc 94454342368778314), (Int.ofNat 60921730038104474), (Int.ofNat 60921730038104489),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf119 : Bracket :=
  ⟨1212, 1213, (Int.ofNat 41125774458688803), (Int.ofNat 41125774458688807), (Int.negSucc 79252945439241891), (Int.negSucc 79252945439241879),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf120 : Bracket :=
  ⟨1219, 1220, (Int.negSucc 2412326873102628), (Int.negSucc 2412326873102615), (Int.ofNat 54371187895729970), (Int.ofNat 54371187895729986),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf121 : Bracket :=
  ⟨1225, 1226, (Int.ofNat 37093662919422190), (Int.ofNat 37093662919422198), (Int.negSucc 27788330572253311), (Int.negSucc 27788330572253291),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf122 : Bracket :=
  ⟨1238, 1239, (Int.negSucc 16196496495797208), (Int.negSucc 16196496495797201), (Int.ofNat 38348553335452242), (Int.ofNat 38348553335452250),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf123 : Bracket :=
  ⟨1244, 1245, (Int.ofNat 3214001373594638), (Int.ofNat 3214001373594653), (Int.negSucc 60935753054513699), (Int.negSucc 60935753054513682),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf124 : Bracket :=
  ⟨1257, 1258, (Int.negSucc 57026157856257701), (Int.negSucc 57026157856257686), (Int.ofNat 6821568878523852), (Int.ofNat 6821568878523863),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf125 : Bracket :=
  ⟨1265, 1266, (Int.ofNat 19790970447458302), (Int.ofNat 19790970447458311), (Int.negSucc 15369219486845804), (Int.negSucc 15369219486845793),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf126 : Bracket :=
  ⟨1270, 1271, (Int.negSucc 33796803647096903), (Int.negSucc 33796803647096896), (Int.ofNat 7269609514368924), (Int.ofNat 7269609514368932),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf127 : Bracket :=
  ⟨1283, 1284, (Int.ofNat 45095852095839087), (Int.ofNat 45095852095839105), (Int.negSucc 82039048562040345), (Int.negSucc 82039048562040341),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf128 : Bracket :=
  ⟨1294, 1295, (Int.negSucc 20898612890006691), (Int.negSucc 20898612890006676), (Int.ofNat 124240368795370162), (Int.ofNat 124240368795370176),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf129 : Bracket :=
  ⟨1302, 1303, (Int.ofNat 154184220557949405), (Int.ofNat 154184220557949420), (Int.negSucc 49501696721083577), (Int.negSucc 49501696721083559),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf130 : Bracket :=
  ⟨1322, 1323, (Int.negSucc 82989579210616014), (Int.negSucc 82989579210616003), (Int.ofNat 10280335131315396), (Int.ofNat 10280335131315412),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf131 : Bracket :=
  ⟨1326, 1327, (Int.ofNat 48237153720919622), (Int.ofNat 48237153720919634), (Int.negSucc 379111205649751), (Int.negSucc 379111205649743),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf132 : Bracket :=
  ⟨1340, 1341, (Int.negSucc 20636168840088906), (Int.negSucc 20636168840088895), (Int.ofNat 20644991955126350), (Int.ofNat 20644991955126357),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf133 : Bracket :=
  ⟨1346, 1347, (Int.ofNat 18655488146079271), (Int.ofNat 18655488146079284), (Int.negSucc 10231313424154331), (Int.negSucc 10231313424154313),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf134 : Bracket :=
  ⟨1356, 1357, (Int.negSucc 12187480071111567), (Int.negSucc 12187480071111556), (Int.ofNat 6425576186952072), (Int.ofNat 6425576186952086),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf135 : Bracket :=
  ⟨1360, 1361, (Int.ofNat 1337359728705851), (Int.ofNat 1337359728705856), (Int.negSucc 26686970361998202), (Int.negSucc 26686970361998186),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf136 : Bracket :=
  ⟨1375, 1376, (Int.negSucc 59044348623359660), (Int.negSucc 59044348623359652), (Int.ofNat 5093695444537178), (Int.ofNat 5093695444537185),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf137 : Bracket :=
  ⟨1382, 1383, (Int.ofNat 274573171650152), (Int.ofNat 274573171650165), (Int.negSucc 73570988226613159), (Int.negSucc 73570988226613149),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf138 : Bracket :=
  ⟨1399, 1400, (Int.negSucc 31927751550159210), (Int.negSucc 31927751550159192), (Int.ofNat 1594926578135012), (Int.ofNat 1594926578135016),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf139 : Bracket :=
  ⟨1403, 1404, (Int.ofNat 11616460672044523), (Int.ofNat 11616460672044538), (Int.negSucc 5416086948639664), (Int.negSucc 5416086948639659),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf140 : Bracket :=
  ⟨1410, 1411, (Int.negSucc 17210601369991353), (Int.negSucc 17210601369991338), (Int.ofNat 17003201570331944), (Int.ofNat 17003201570331962),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf141 : Bracket :=
  ⟨1421, 1422, (Int.ofNat 49420913403568768), (Int.ofNat 49420913403568776), (Int.negSucc 10830846207844834), (Int.negSucc 10830846207844823),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf142 : Bracket :=
  ⟨1428, 1429, (Int.negSucc 35617248202479101), (Int.negSucc 35617248202479096), (Int.ofNat 59601890888067539), (Int.ofNat 59601890888067553),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf143 : Bracket :=
  ⟨1444, 1445, (Int.ofNat 5501821167417846), (Int.ofNat 5501821167417857), (Int.negSucc 174150441854046944), (Int.negSucc 174150441854046935),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf144 : Bracket :=
  ⟨1455, 1456, (Int.negSucc 45950794200407188), (Int.negSucc 45950794200407175), (Int.ofNat 33912317165695817), (Int.ofNat 33912317165695822),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf145 : Bracket :=
  ⟨1460, 1461, (Int.ofNat 49277406524513540), (Int.ofNat 49277406524513553), (Int.negSucc 3095797821419764), (Int.negSucc 3095797821419756),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf146 : Bracket :=
  ⟨1464, 1465, (Int.negSucc 63737894322921877), (Int.negSucc 63737894322921874), (Int.ofNat 15523131667789370), (Int.ofNat 15523131667789383),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf147 : Bracket :=
  ⟨1488, 1489, (Int.ofNat 328485203855688001), (Int.ofNat 328485203855688004), (Int.negSucc 465722125643002428), (Int.negSucc 465722125643002418),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf148 : Bracket :=
  ⟨1502, 1503, (Int.negSucc 16975665563383736), (Int.negSucc 16975665563383724), (Int.ofNat 207040607623875515), (Int.ofNat 207040607623875522),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf149 : Bracket :=
  ⟨1509, 1510, (Int.ofNat 131850295842548224), (Int.ofNat 131850295842548230), (Int.negSucc 7030526005875915), (Int.negSucc 7030526005875904),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf150 : Bracket :=
  ⟨1520, 1521, (Int.negSucc 21485227142306045), (Int.negSucc 21485227142306043), (Int.ofNat 47478995754918890), (Int.ofNat 47478995754918908),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf151 : Bracket :=
  ⟨1526, 1527, (Int.ofNat 37014852669184088), (Int.ofNat 37014852669184098), (Int.negSucc 21827141601868598), (Int.negSucc 21827141601868591),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf152 : Bracket :=
  ⟨1534, 1535, (Int.negSucc 62667961306199590), (Int.negSucc 62667961306199578), (Int.ofNat 28393219043788108), (Int.ofNat 28393219043788114),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf153 : Bracket :=
  ⟨1546, 1547, (Int.ofNat 100410592905786109), (Int.ofNat 100410592905786125), (Int.negSucc 50755777760619373), (Int.negSucc 50755777760619355),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf154 : Bracket :=
  ⟨1558, 1559, (Int.negSucc 34372062696274278), (Int.negSucc 34372062696274266), (Int.ofNat 102535517633475760), (Int.ofNat 102535517633475778),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf155 : Bracket :=
  ⟨1568, 1569, (Int.ofNat 34255607730025534), (Int.ofNat 34255607730025536), (Int.negSucc 90438319838377118), (Int.negSucc 90438319838377111),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf156 : Bracket :=
  ⟨1582, 1583, (Int.negSucc 36413865351441847), (Int.negSucc 36413865351441838), (Int.ofNat 8315142109543862), (Int.ofNat 8315142109543872),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf157 : Bracket :=
  ⟨1588, 1589, (Int.ofNat 4394374922467461), (Int.ofNat 4394374922467464), (Int.negSucc 21071363708406028), (Int.negSucc 21071363708406022),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf158 : Bracket :=
  ⟨1596, 1597, (Int.negSucc 3072071124090159), (Int.negSucc 3072071124090144), (Int.ofNat 29211950813728644), (Int.ofNat 29211950813728651),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf159 : Bracket :=
  ⟨1606, 1607, (Int.ofNat 7466484862994951), (Int.ofNat 7466484862994963), (Int.negSucc 29441754807436176), (Int.negSucc 29441754807436161),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf160 : Bracket :=
  ⟨1616, 1617, (Int.negSucc 10587268547093741), (Int.negSucc 10587268547093726), (Int.ofNat 17608401723189675), (Int.ofNat 17608401723189694),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf161 : Bracket :=
  ⟨1623, 1624, (Int.ofNat 10304792343719100), (Int.ofNat 10304792343719117), (Int.negSucc 18998510217220927), (Int.negSucc 18998510217220922),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf162 : Bracket :=
  ⟨1633, 1634, (Int.negSucc 19687088973869756), (Int.negSucc 19687088973869739), (Int.ofNat 13318293166333647), (Int.ofNat 13318293166333656),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf163 : Bracket :=
  ⟨1639, 1640, (Int.ofNat 27508945117847276), (Int.ofNat 27508945117847287), (Int.negSucc 16067428840470996), (Int.negSucc 16067428840470993),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf164 : Bracket :=
  ⟨1653, 1654, (Int.negSucc 48988312517520787), (Int.negSucc 48988312517520779), (Int.ofNat 39163041431974654), (Int.ofNat 39163041431974670),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf165 : Bracket :=
  ⟨1661, 1662, (Int.ofNat 12520357003908159), (Int.ofNat 12520357003908169), (Int.negSucc 91019671375109690), (Int.negSucc 91019671375109676),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf166 : Bracket :=
  ⟨1671, 1672, (Int.negSucc 27600429806336886), (Int.negSucc 27600429806336868), (Int.ofNat 180058436283605846), (Int.ofNat 180058436283605856),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf167 : Bracket :=
  ⟨1685, 1686, (Int.ofNat 262670072784476829), (Int.ofNat 262670072784476840), (Int.negSucc 4824345273971541), (Int.negSucc 4824345273971522),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf168 : Bracket :=
  ⟨1696, 1697, (Int.negSucc 125474688289987800), (Int.negSucc 125474688289987788), (Int.ofNat 69934974865986478), (Int.ofNat 69934974865986491),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf169 : Bracket :=
  ⟨1707, 1708, (Int.ofNat 64149572118595814), (Int.ofNat 64149572118595832), (Int.negSucc 80654309582460111), (Int.negSucc 80654309582460097),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf170 : Bracket :=
  ⟨1717, 1718, (Int.negSucc 88242780780150616), (Int.negSucc 88242780780150602), (Int.ofNat 7984358595770457), (Int.ofNat 7984358595770476),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf171 : Bracket :=
  ⟨1726, 1727, (Int.ofNat 25967204936419227), (Int.ofNat 25967204936419236), (Int.negSucc 38934922594718073), (Int.negSucc 38934922594718061),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf172 : Bracket :=
  ⟨1733, 1734, (Int.negSucc 38892122587912576), (Int.negSucc 38892122587912565), (Int.ofNat 42106941993369709), (Int.ofNat 42106941993369724),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf173 : Bracket :=
  ⟨1747, 1748, (Int.ofNat 9252326730833302), (Int.ofNat 9252326730833316), (Int.negSucc 73226044250949818), (Int.negSucc 73226044250949815),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf174 : Bracket :=
  ⟨1756, 1757, (Int.negSucc 10200115128038859), (Int.negSucc 10200115128038856), (Int.ofNat 30578372259521907), (Int.ofNat 30578372259521924),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf175 : Bracket :=
  ⟨1761, 1762, (Int.ofNat 21975997760000766), (Int.ofNat 21975997760000775), (Int.negSucc 20344281639523298), (Int.negSucc 20344281639523288),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf176 : Bracket :=
  ⟨1768, 1769, (Int.negSucc 8852746190130898), (Int.negSucc 8852746190130894), (Int.ofNat 121328211414588276), (Int.ofNat 121328211414588294),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf177 : Bracket :=
  ⟨1785, 1786, (Int.ofNat 121303885317525040), (Int.ofNat 121303885317525052), (Int.negSucc 315772406305304561), (Int.negSucc 315772406305304555),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf178 : Bracket :=
  ⟨1798, 1799, (Int.negSucc 51375851378122844), (Int.negSucc 51375851378122837), (Int.ofNat 291712243191690143), (Int.ofNat 291712243191690160),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf179 : Bracket :=
  ⟨1810, 1811, (Int.ofNat 102003406485398884), (Int.ofNat 102003406485398895), (Int.negSucc 83602099759367332), (Int.negSucc 83602099759367321),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf180 : Bracket :=
  ⟨1820, 1821, (Int.negSucc 46553727170607433), (Int.negSucc 46553727170607428), (Int.ofNat 32899450641959824), (Int.ofNat 32899450641959829),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf181 : Bracket :=
  ⟨1827, 1828, (Int.ofNat 7073316232110267), (Int.ofNat 7073316232110280), (Int.negSucc 56876663401892544), (Int.negSucc 56876663401892531),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf182 : Bracket :=
  ⟨1837, 1838, (Int.negSucc 19681864302737331), (Int.negSucc 19681864302737317), (Int.ofNat 28330441272493749), (Int.ofNat 28330441272493760),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf183 : Bracket :=
  ⟨1841, 1842, (Int.ofNat 41809630517859080), (Int.ofNat 41809630517859087), (Int.negSucc 14110738170861828), (Int.negSucc 14110738170861817),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf184 : Bracket :=
  ⟨1857, 1858, (Int.negSucc 191692381076230555), (Int.negSucc 191692381076230550), (Int.ofNat 16757105391316072), (Int.ofNat 16757105391316078),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf185 : Bracket :=
  ⟨1871, 1872, (Int.ofNat 67525651397427726), (Int.ofNat 67525651397427732), (Int.negSucc 15534372906132336), (Int.negSucc 15534372906132332),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf186 : Bracket :=
  ⟨1878, 1879, (Int.negSucc 11088825109671126), (Int.negSucc 11088825109671111), (Int.ofNat 36957406793464035), (Int.ofNat 36957406793464051),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf187 : Bracket :=
  ⟨1887, 1888, (Int.ofNat 6295756991351743), (Int.ofNat 6295756991351752), (Int.negSucc 36592805331967108), (Int.negSucc 36592805331967106),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf188 : Bracket :=
  ⟨1893, 1894, (Int.negSucc 47668178608949870), (Int.negSucc 47668178608949864), (Int.ofNat 3923234497311192), (Int.ofNat 3923234497311206),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf189 : Bracket :=
  ⟨1905, 1906, (Int.ofNat 11248352961924185), (Int.ofNat 11248352961924193), (Int.negSucc 115316036706431134), (Int.negSucc 115316036706431116),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf190 : Bracket :=
  ⟨1920, 1921, (Int.negSucc 74093722320767441), (Int.negSucc 74093722320767438), (Int.ofNat 3429896693205235), (Int.ofNat 3429896693205250),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf191 : Bracket :=
  ⟨1927, 1928, (Int.ofNat 20332369600843422), (Int.ofNat 20332369600843432), (Int.negSucc 25225601789862869), (Int.negSucc 25225601789862866),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf192 : Bracket :=
  ⟨1936, 1937, (Int.negSucc 19003578159964591), (Int.negSucc 19003578159964587), (Int.ofNat 35214848015543135), (Int.ofNat 35214848015543149),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf193 : Bracket :=
  ⟨1947, 1948, (Int.ofNat 45466584457504809), (Int.ofNat 45466584457504825), (Int.negSucc 4090472148578685), (Int.negSucc 4090472148578682),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf194 : Bracket :=
  ⟨1958, 1959, (Int.negSucc 4636995347997720), (Int.negSucc 4636995347997713), (Int.ofNat 17086208313497637), (Int.ofNat 17086208313497650),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf195 : Bracket :=
  ⟨1965, 1966, (Int.ofNat 7944482338505037), (Int.ofNat 7944482338505043), (Int.negSucc 1100304478423736), (Int.negSucc 1100304478423720),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf196 : Bracket :=
  ⟨1967, 1968, (Int.negSucc 4483810384107550), (Int.negSucc 4483810384107543), (Int.ofNat 143957123615198), (Int.ofNat 143957123615202),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf197 : Bracket :=
  ⟨1980, 1981, (Int.ofNat 28488491312115947), (Int.ofNat 28488491312115950), (Int.negSucc 61184774585882578), (Int.negSucc 61184774585882564),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf198 : Bracket :=
  ⟨1993, 1994, (Int.negSucc 121522367257170774), (Int.negSucc 121522367257170759), (Int.ofNat 14223679783444851), (Int.ofNat 14223679783444859),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf199 : Bracket :=
  ⟨2005, 2006, (Int.ofNat 14381501521968818), (Int.ofNat 14381501521968823), (Int.negSucc 64112590807532409), (Int.negSucc 64112590807532399),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf200 : Bracket :=
  ⟨2010, 2011, (Int.negSucc 72957340821336940), (Int.negSucc 72957340821336931), (Int.ofNat 12400203389544022), (Int.ofNat 12400203389544033),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf201 : Bracket :=
  ⟨2025, 2026, (Int.ofNat 66161542483475595), (Int.ofNat 66161542483475605), (Int.negSucc 50299360984878396), (Int.negSucc 50299360984878384),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf202 : Bracket :=
  ⟨2031, 2032, (Int.negSucc 12175031153358804), (Int.negSucc 12175031153358792), (Int.ofNat 116888766444789382), (Int.ofNat 116888766444789385),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf203 : Bracket :=
  ⟨2042, 2043, (Int.ofNat 50450731884917403), (Int.ofNat 50450731884917413), (Int.negSucc 184946589982717875), (Int.negSucc 184946589982717871),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf204 : Bracket :=
  ⟨2049, 2050, (Int.negSucc 286757301051564743), (Int.negSucc 286757301051564740), (Int.ofNat 129236427137384474), (Int.ofNat 129236427137384491),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf205 : Bracket :=
  ⟨2072, 2073, (Int.ofNat 486096249479728043), (Int.ofNat 486096249479728046), (Int.negSucc 96590838199357926), (Int.negSucc 96590838199357911),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf206 : Bracket :=
  ⟨2081, 2082, (Int.negSucc 86610939197302158), (Int.negSucc 86610939197302143), (Int.ofNat 188146988774300349), (Int.ofNat 188146988774300364),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf207 : Bracket :=
  ⟨2093, 2094, (Int.ofNat 51665159991596789), (Int.ofNat 51665159991596794), (Int.negSucc 73588697811618665), (Int.negSucc 73588697811618654),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf208 : Bracket :=
  ⟨2102, 2103, (Int.negSucc 10939858793555212), (Int.negSucc 10939858793555193), (Int.ofNat 39490258173676701), (Int.ofNat 39490258173676711),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf209 : Bracket :=
  ⟨2108, 2109, (Int.ofNat 11220962963780328), (Int.ofNat 11220962963780331), (Int.negSucc 38502813053141720), (Int.negSucc 38502813053141703),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf210 : Bracket :=
  ⟨2117, 2118, (Int.negSucc 25955937944070335), (Int.negSucc 25955937944070327), (Int.ofNat 53082278254476545), (Int.ofNat 53082278254476552),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf211 : Bracket :=
  ⟨2132, 2133, (Int.ofNat 16602677408465763), (Int.ofNat 16602677408465766), (Int.negSucc 21703497117212086), (Int.negSucc 21703497117212077),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf212 : Bracket :=
  ⟨2138, 2139, (Int.negSucc 14005760394050342), (Int.negSucc 14005760394050330), (Int.ofNat 8057317816715503), (Int.ofNat 8057317816715519),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf213 : Bracket :=
  ⟨2144, 2145, (Int.ofNat 20186101072706870), (Int.ofNat 20186101072706873), (Int.negSucc 4750939263268830), (Int.negSucc 4750939263268814),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf214 : Bracket :=
  ⟨2155, 2156, (Int.negSucc 3024775653477259), (Int.negSucc 3024775653477247), (Int.ofNat 41248883579382465), (Int.ofNat 41248883579382475),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf215 : Bracket :=
  ⟨2162, 2163, (Int.ofNat 47509082599112248), (Int.ofNat 47509082599112258), (Int.negSucc 18022313686364836), (Int.negSucc 18022313686364826),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf216 : Bracket :=
  ⟨2179, 2180, (Int.negSucc 17584804291538146), (Int.negSucc 17584804291538135), (Int.ofNat 25547960897350904), (Int.ofNat 25547960897350908),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf217 : Bracket :=
  ⟨2183, 2184, (Int.ofNat 17009025379779288), (Int.ofNat 17009025379779304), (Int.negSucc 24728025955570201), (Int.negSucc 24728025955570198),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf218 : Bracket :=
  ⟨2192, 2193, (Int.negSucc 83189959259562064), (Int.negSucc 83189959259562061), (Int.ofNat 19582843327961070), (Int.ofNat 19582843327961079),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf219 : Bracket :=
  ⟨2207, 2208, (Int.ofNat 76435290696872272), (Int.ofNat 76435290696872280), (Int.negSucc 88439121628854820), (Int.negSucc 88439121628854818),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf220 : Bracket :=
  ⟨2220, 2221, (Int.negSucc 42148697240059530), (Int.negSucc 42148697240059518), (Int.ofNat 3679156220361120), (Int.ofNat 3679156220361138),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf221 : Bracket :=
  ⟨2223, 2224, (Int.ofNat 14125139767321522), (Int.ofNat 14125139767321532), (Int.negSucc 21053166447494715), (Int.negSucc 21053166447494712),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf222 : Bracket :=
  ⟨2238, 2239, (Int.negSucc 13518535357444017), (Int.negSucc 13518535357443999), (Int.ofNat 77453854933449160), (Int.ofNat 77453854933449172),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf223 : Bracket :=
  ⟨2248, 2249, (Int.ofNat 38435517849755326), (Int.ofNat 38435517849755329), (Int.negSucc 8359946094848434), (Int.negSucc 8359946094848429),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf224 : Bracket :=
  ⟨2253, 2254, (Int.negSucc 33669106765941642), (Int.negSucc 33669106765941626), (Int.ofNat 4508233193225491), (Int.ofNat 4508233193225509),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf225 : Bracket :=
  ⟨2265, 2266, (Int.ofNat 35392064618843318), (Int.ofNat 35392064618843331), (Int.negSucc 46365811494474777), (Int.negSucc 46365811494474771),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf226 : Bracket :=
  ⟨2275, 2276, (Int.negSucc 79452647631138054), (Int.negSucc 79452647631138040), (Int.ofNat 325317366224923), (Int.ofNat 325317366224930),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf227 : Bracket :=
  ⟨2286, 2287, (Int.ofNat 12946084968615565), (Int.ofNat 12946084968615575), (Int.negSucc 46034452192442576), (Int.negSucc 46034452192442567),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf228 : Bracket :=
  ⟨2295, 2296, (Int.negSucc 255146204168536), (Int.negSucc 255146204168522), (Int.ofNat 25630462735192861), (Int.ofNat 25630462735192863),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf229 : Bracket :=
  ⟨2298, 2299, (Int.ofNat 11817199644741515), (Int.ofNat 11817199644741527), (Int.negSucc 39263861627779362), (Int.negSucc 39263861627779346),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf230 : Bracket :=
  ⟨2316, 2317, (Int.negSucc 90025136695296308), (Int.negSucc 90025136695296305), (Int.ofNat 96301193404803336), (Int.ofNat 96301193404803346),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf231 : Bracket :=
  ⟨2323, 2324, (Int.ofNat 34217816781934322), (Int.ofNat 34217816781934340), (Int.negSucc 186701965829755816), (Int.negSucc 186701965829755813),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf232 : Bracket :=
  ⟨2339, 2340, (Int.negSucc 41774798969864116), (Int.negSucc 41774798969864105), (Int.ofNat 209938979334144342), (Int.ofNat 209938979334144355),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf233 : Bracket :=
  ⟨2352, 2353, (Int.ofNat 42128338365873179), (Int.ofNat 42128338365873194), (Int.negSucc 6628775620386872), (Int.negSucc 6628775620386859),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf234 : Bracket :=
  ⟨2355, 2356, (Int.negSucc 21922530093185102), (Int.negSucc 21922530093185093), (Int.ofNat 3507406596371782), (Int.ofNat 3507406596371785),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf235 : Bracket :=
  ⟨2365, 2366, (Int.ofNat 19220994501692669), (Int.ofNat 19220994501692675), (Int.negSucc 39491321628589862), (Int.negSucc 39491321628589852),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf236 : Bracket :=
  ⟨2372, 2373, (Int.negSucc 47664938583313620), (Int.negSucc 47664938583313617), (Int.ofNat 33462612176099990), (Int.ofNat 33462612176100001),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf237 : Bracket :=
  ⟨2381, 2382, (Int.ofNat 96508300120899331), (Int.ofNat 96508300120899343), (Int.negSucc 107692530270968559), (Int.negSucc 107692530270968545),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf238 : Bracket :=
  ⟨2397, 2398, (Int.negSucc 357087315559902650), (Int.negSucc 357087315559902632), (Int.ofNat 26974295120409983), (Int.ofNat 26974295120409991),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf239 : Bracket :=
  ⟨2408, 2409, (Int.ofNat 48214179061236069), (Int.ofNat 48214179061236073), (Int.negSucc 242666066229335747), (Int.negSucc 242666066229335736),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf240 : Bracket :=
  ⟨2417, 2418, (Int.negSucc 195846182353396653), (Int.negSucc 195846182353396647), (Int.ofNat 157758179604486313), (Int.ofNat 157758179604486325),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf241 : Bracket :=
  ⟨2438, 2439, (Int.ofNat 4352200104062541), (Int.ofNat 4352200104062554), (Int.negSucc 48192185560164677), (Int.negSucc 48192185560164672),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf242 : Bracket :=
  ⟨2443, 2444, (Int.negSucc 21422236921262073), (Int.negSucc 21422236921262058), (Int.ofNat 2580258281824003), (Int.ofNat 2580258281824006),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf243 : Bracket :=
  ⟨2448, 2449, (Int.ofNat 4246880613993822), (Int.ofNat 4246880613993824), (Int.negSucc 20954335659633478), (Int.negSucc 20954335659633465),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf244 : Bracket :=
  ⟨2458, 2459, (Int.negSucc 35390159205179446), (Int.negSucc 35390159205179436), (Int.ofNat 6197630786337823), (Int.ofNat 6197630786337838),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf245 : Bracket :=
  ⟨2469, 2470, (Int.ofNat 732676206333635), (Int.ofNat 732676206333643), (Int.negSucc 25139002338203379), (Int.negSucc 25139002338203368),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf246 : Bracket :=
  ⟨2474, 2475, (Int.negSucc 2755950575683347), (Int.negSucc 2755950575683331), (Int.ofNat 39399356618603754), (Int.ofNat 39399356618603769),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf247 : Bracket :=
  ⟨2491, 2492, (Int.ofNat 17567130065762962), (Int.ofNat 17567130065762968), (Int.negSucc 10906001116574642), (Int.negSucc 10906001116574638),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf248 : Bracket :=
  ⟨2495, 2496, (Int.negSucc 7168890865038383), (Int.negSucc 7168890865038376), (Int.ofNat 18434926559778419), (Int.ofNat 18434926559778422),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf249 : Bracket :=
  ⟨2506, 2507, (Int.ofNat 15208616640517051), (Int.ofNat 15208616640517062), (Int.negSucc 35159565210880738), (Int.negSucc 35159565210880720),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf250 : Bracket :=
  ⟨2518, 2519, (Int.negSucc 17609845673825308), (Int.negSucc 17609845673825297), (Int.ofNat 12712821037005589), (Int.ofNat 12712821037005601),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf251 : Bracket :=
  ⟨2524, 2525, (Int.ofNat 9905653676978789), (Int.ofNat 9905653676978792), (Int.negSucc 15413327946550144), (Int.negSucc 15413327946550134),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf252 : Bracket :=
  ⟨2532, 2533, (Int.negSucc 33306783264433228), (Int.negSucc 33306783264433225), (Int.ofNat 3854673865717270), (Int.ofNat 3854673865717283),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf253 : Bracket :=
  ⟨2542, 2543, (Int.ofNat 23760260706284536), (Int.ofNat 23760260706284543), (Int.negSucc 38038305447620693), (Int.negSucc 38038305447620684),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf254 : Bracket :=
  ⟨2551, 2552, (Int.negSucc 27253382466274938), (Int.negSucc 27253382466274932), (Int.ofNat 82329928708445840), (Int.ofNat 82329928708445844),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf255 : Bracket :=
  ⟨2563, 2564, (Int.ofNat 45020537821030486), (Int.ofNat 45020537821030489), (Int.negSucc 166351654088503043), (Int.negSucc 166351654088503040),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf256 : Bracket :=
  ⟨2576, 2577, (Int.negSucc 68335670371433935), (Int.negSucc 68335670371433932), (Int.ofNat 161634762438622341), (Int.ofNat 161634762438622356),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf257 : Bracket :=
  ⟨2588, 2589, (Int.ofNat 99575317031484929), (Int.ofNat 99575317031484932), (Int.negSucc 26333232191980645), (Int.negSucc 26333232191980634),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf258 : Bracket :=
  ⟨2597, 2598, (Int.negSucc 13696413094995845), (Int.negSucc 13696413094995837), (Int.ofNat 17076281166384088), (Int.ofNat 17076281166384106),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf259 : Bracket :=
  ⟨2599, 2600, (Int.ofNat 16946682968968650), (Int.ofNat 16946682968968660), (Int.negSucc 21899474911406003), (Int.negSucc 21899474911405991),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf260 : Bracket :=
  ⟨2615, 2616, (Int.negSucc 317361901412304776), (Int.negSucc 317361901412304762), (Int.ofNat 19181450092917145), (Int.ofNat 19181450092917148),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf261 : Bracket :=
  ⟨2629, 2630, (Int.ofNat 169973806331221947), (Int.ofNat 169973806331221954), (Int.negSucc 8334527830559050), (Int.negSucc 8334527830559041),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf262 : Bracket :=
  ⟨2634, 2635, (Int.negSucc 47338103585486397), (Int.negSucc 47338103585486379), (Int.ofNat 124808662337842604), (Int.ofNat 124808662337842620),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf263 : Bracket :=
  ⟨2652, 2653, (Int.ofNat 87737644743394713), (Int.ofNat 87737644743394716), (Int.negSucc 87407588581371265), (Int.negSucc 87407588581371261),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf264 : Bracket :=
  ⟨2659, 2660, (Int.negSucc 91617288882102788), (Int.negSucc 91617288882102777), (Int.ofNat 3030358850160631), (Int.ofNat 3030358850160634),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf265 : Bracket :=
  ⟨2666, 2667, (Int.ofNat 35433127747423401), (Int.ofNat 35433127747423412), (Int.negSucc 84122927541471733), (Int.negSucc 84122927541471726),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf266 : Bracket :=
  ⟨2682, 2683, (Int.negSucc 58896897195202370), (Int.negSucc 58896897195202357), (Int.ofNat 31990910942809202), (Int.ofNat 31990910942809216),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf267 : Bracket :=
  ⟨2688, 2689, (Int.ofNat 37572357533950303), (Int.ofNat 37572357533950305), (Int.negSucc 23691394767013510), (Int.negSucc 23691394767013503),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf268 : Bracket :=
  ⟨2697, 2698, (Int.negSucc 58888890760916679), (Int.negSucc 58888890760916662), (Int.ofNat 17241649136407840), (Int.ofNat 17241649136407856),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf269 : Bracket :=
  ⟨2707, 2708, (Int.ofNat 174072067674816), (Int.ofNat 174072067674822), (Int.negSucc 107697526094173023), (Int.negSucc 107697526094173019),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf270 : Bracket :=
  ⟨2720, 2721, (Int.negSucc 6975850689879571), (Int.negSucc 6975850689879567), (Int.ofNat 85784251514257399), (Int.ofNat 85784251514257407),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf271 : Bracket :=
  ⟨2730, 2731, (Int.ofNat 18382514347694303), (Int.ofNat 18382514347694315), (Int.negSucc 22607826979470728), (Int.negSucc 22607826979470710),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf272 : Bracket :=
  ⟨2734, 2735, (Int.negSucc 30029188830577518), (Int.negSucc 30029188830577512), (Int.ofNat 11788946127361228), (Int.ofNat 11788946127361245),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf273 : Bracket :=
  ⟨2754, 2755, (Int.ofNat 6060302280252169), (Int.ofNat 6060302280252176), (Int.negSucc 2212592303035394), (Int.negSucc 2212592303035382),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf274 : Bracket :=
  ⟨2756, 2757, (Int.negSucc 1331130206253622), (Int.negSucc 1331130206253619), (Int.ofNat 3846048597093854), (Int.ofNat 3846048597093861),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf275 : Bracket :=
  ⟨2759, 2760, (Int.ofNat 4791815860783237), (Int.ofNat 4791815860783248), (Int.negSucc 9957982653441988), (Int.negSucc 9957982653441984),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf276 : Bracket :=
  ⟨2777, 2778, (Int.negSucc 23966877503733880), (Int.negSucc 23966877503733864), (Int.ofNat 119118580093411835), (Int.ofNat 119118580093411851),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf277 : Bracket :=
  ⟨2789, 2790, (Int.ofNat 6814626225529919), (Int.ofNat 6814626225529932), (Int.negSucc 73571415613782678), (Int.negSucc 73571415613782671),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf278 : Bracket :=
  ⟨2796, 2797, (Int.negSucc 20027037435205161), (Int.negSucc 20027037435205158), (Int.ofNat 55346006078107462), (Int.ofNat 55346006078107469),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf279 : Bracket :=
  ⟨2804, 2805, (Int.ofNat 97394170384050794), (Int.ofNat 97394170384050796), (Int.negSucc 11101613657480079), (Int.negSucc 11101613657480063),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf280 : Bracket :=
  ⟨2817, 2818, (Int.negSucc 95626902942144844), (Int.negSucc 95626902942144829), (Int.ofNat 96340975424918002), (Int.ofNat 96340975424918014),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf281 : Bracket :=
  ⟨2831, 2832, (Int.ofNat 70442655903785384), (Int.ofNat 70442655903785398), (Int.negSucc 63354098387260711), (Int.negSucc 63354098387260708),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf282 : Bracket :=
  ⟨2845, 2846, (Int.negSucc 9452192563316575), (Int.negSucc 9452192563316558), (Int.ofNat 2909298301831772), (Int.ofNat 2909298301831784),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf283 : Bracket :=
  ⟨2847, 2848, (Int.ofNat 4759574837412794), (Int.ofNat 4759574837412804), (Int.negSucc 1330670025301251), (Int.negSucc 1330670025301248),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf284 : Bracket :=
  ⟨2857, 2858, (Int.negSucc 3235340185001783), (Int.negSucc 3235340185001778), (Int.ofNat 5390062845054475), (Int.ofNat 5390062845054486),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf285 : Bracket :=
  ⟨2860, 2861, (Int.ofNat 2074728312527813), (Int.ofNat 2074728312527817), (Int.negSucc 13548286094362148), (Int.negSucc 13548286094362143),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf286 : Bracket :=
  ⟨2877, 2878, (Int.negSucc 12916139252233977), (Int.negSucc 12916139252233971), (Int.ofNat 11583922058700746), (Int.ofNat 11583922058700758),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf287 : Bracket :=
  ⟨2880, 2881, (Int.ofNat 7889177280606297), (Int.ofNat 7889177280606300), (Int.negSucc 21387065087046115), (Int.negSucc 21387065087046106),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf288 : Bracket :=
  ⟨2893, 2894, (Int.negSucc 25771501947998345), (Int.negSucc 25771501947998340), (Int.ofNat 71491206875123061), (Int.ofNat 71491206875123071),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf289 : Bracket :=
  ⟨2901, 2902, (Int.ofNat 84389950859105212), (Int.ofNat 84389950859105220), (Int.negSucc 39119285095635864), (Int.negSucc 39119285095635853),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf290 : Bracket :=
  ⟨2910, 2911, (Int.negSucc 126336290708385274), (Int.negSucc 126336290708385268), (Int.ofNat 147278865057187890), (Int.ofNat 147278865057187900),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf291 : Bracket :=
  ⟨2928, 2929, (Int.ofNat 147910989839912922), (Int.ofNat 147910989839912925), (Int.negSucc 152412139558607173), (Int.negSucc 152412139558607160),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf292 : Bracket :=
  ⟨2933, 2934, (Int.negSucc 105256109040128786), (Int.negSucc 105256109040128774), (Int.ofNat 243026673595405580), (Int.ofNat 243026673595405589),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf293 : Bracket :=
  ⟨2951, 2952, (Int.ofNat 514083159668363906), (Int.ofNat 514083159668363920), (Int.negSucc 29011269141840579), (Int.negSucc 29011269141840576),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf294 : Bracket :=
  ⟨2961, 2962, (Int.negSucc 92823427632985941), (Int.negSucc 92823427632985928), (Int.ofNat 237765676093939740), (Int.ofNat 237765676093939754),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf295 : Bracket :=
  ⟨2975, 2976, (Int.ofNat 69126014967767830), (Int.ofNat 69126014967767835), (Int.negSucc 51234770927792520), (Int.negSucc 51234770927792517),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf296 : Bracket :=
  ⟨2983, 2984, (Int.negSucc 32193313730210750), (Int.negSucc 32193313730210733), (Int.ofNat 3538488838709498), (Int.ofNat 3538488838709500),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf297 : Bracket :=
  ⟨2986, 2987, (Int.ofNat 21397437775941048), (Int.ofNat 21397437775941058), (Int.negSucc 1124983156476337), (Int.negSucc 1124983156476321),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf298 : Bracket :=
  ⟨3000, 3001, (Int.negSucc 63801647843051085), (Int.negSucc 63801647843051083), (Int.ofNat 11950429918621178), (Int.ofNat 11950429918621185),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf299 : Bracket :=
  ⟨3008, 3009, (Int.ofNat 10313800604997531), (Int.ofNat 10313800604997533), (Int.negSucc 64383852488372925), (Int.negSucc 64383852488372912),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf300 : Bracket :=
  ⟨3019, 3020, (Int.negSucc 84743470732557425), (Int.negSucc 84743470732557418), (Int.ofNat 860703085923499), (Int.ofNat 860703085923503),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf301 : Bracket :=
  ⟨3030, 3031, (Int.ofNat 39273064174580465), (Int.ofNat 39273064174580472), (Int.negSucc 16345965565857175), (Int.negSucc 16345965565857159),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf302 : Bracket :=
  ⟨3037, 3038, (Int.negSucc 42419806089764520), (Int.negSucc 42419806089764516), (Int.ofNat 4452299647549878), (Int.ofNat 4452299647549890),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf303 : Bracket :=
  ⟨3047, 3048, (Int.ofNat 55996878430575629), (Int.ofNat 55996878430575634), (Int.negSucc 6393513946831159), (Int.negSucc 6393513946831157),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf304 : Bracket :=
  ⟨3058, 3059, (Int.negSucc 1504576821017979), (Int.negSucc 1504576821017963), (Int.ofNat 69951012875317679), (Int.ofNat 69951012875317683),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf305 : Bracket :=
  ⟨3068, 3069, (Int.ofNat 49702573074399207), (Int.ofNat 49702573074399210), (Int.negSucc 23304398542591035), (Int.negSucc 23304398542591032),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf306 : Bracket :=
  ⟨3081, 3082, (Int.negSucc 19912833819730656), (Int.negSucc 19912833819730648), (Int.ofNat 10982797903472850), (Int.ofNat 10982797903472853),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf307 : Bracket :=
  ⟨3086, 3087, (Int.ofNat 18912066625487986), (Int.ofNat 18912066625488003), (Int.negSucc 1738779535812317), (Int.negSucc 1738779535812307),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf308 : Bracket :=
  ⟨3096, 3097, (Int.negSucc 11584835692634218), (Int.negSucc 11584835692634216), (Int.ofNat 8218136570728620), (Int.ofNat 8218136570728629),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf309 : Bracket :=
  ⟨3100, 3101, (Int.ofNat 11500113399573407), (Int.ofNat 11500113399573410), (Int.negSucc 15651833008876067), (Int.negSucc 15651833008876052),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf310 : Bracket :=
  ⟨3116, 3117, (Int.negSucc 84900971304750700), (Int.negSucc 84900971304750697), (Int.ofNat 2965226539947428), (Int.ofNat 2965226539947442),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf311 : Bracket :=
  ⟨3124, 3125, (Int.ofNat 19224092688019913), (Int.ofNat 19224092688019916), (Int.negSucc 59528537919182849), (Int.negSucc 59528537919182845),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf312 : Bracket :=
  ⟨3133, 3134, (Int.negSucc 80003531096009408), (Int.negSucc 80003531096009393), (Int.ofNat 43671779778641333), (Int.ofNat 43671779778641341),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf313 : Bracket :=
  ⟨3145, 3146, (Int.ofNat 99108762710141254), (Int.ofNat 99108762710141264), (Int.negSucc 90765651451780696), (Int.negSucc 90765651451780680),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf314 : Bracket :=
  ⟨3156, 3157, (Int.negSucc 117436491454864386), (Int.negSucc 117436491454864383), (Int.ofNat 90374275881018130), (Int.ofNat 90374275881018138),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf315 : Bracket :=
  ⟨3168, 3169, (Int.ofNat 14934367381660326), (Int.ofNat 14934367381660329), (Int.negSucc 162732696164449089), (Int.negSucc 162732696164449074),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf316 : Bracket :=
  ⟨3177, 3178, (Int.negSucc 116428572152317839), (Int.negSucc 116428572152317835), (Int.ofNat 41637877403021444), (Int.ofNat 41637877403021451),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf317 : Bracket :=
  ⟨3187, 3188, (Int.ofNat 75030335282345887), (Int.ofNat 75030335282345893), (Int.negSucc 92628026390139915), (Int.negSucc 92628026390139912),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf318 : Bracket :=
  ⟨3200, 3201, (Int.negSucc 72787540080340873), (Int.negSucc 72787540080340871), (Int.ofNat 7019531371632085), (Int.ofNat 7019531371632089),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf319 : Bracket :=
  ⟨3204, 3205, (Int.ofNat 32749845311595100), (Int.ofNat 32749845311595102), (Int.negSucc 29539635762903621), (Int.negSucc 29539635762903607),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf320 : Bracket :=
  ⟨3214, 3215, (Int.negSucc 90171007179136127), (Int.negSucc 90171007179136118), (Int.ofNat 141194570549350821), (Int.ofNat 141194570549350831),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf321 : Bracket :=
  ⟨3236, 3237, (Int.ofNat 192516109874973), (Int.ofNat 192516109874976), (Int.negSucc 45062744805143140), (Int.negSucc 45062744805143126),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf322 : Bracket :=
  ⟨3239, 3240, (Int.negSucc 30260895408008204), (Int.negSucc 30260895408008189), (Int.ofNat 8821289825197640), (Int.ofNat 8821289825197644),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf323 : Bracket :=
  ⟨3246, 3247, (Int.ofNat 58785207572261022), (Int.ofNat 58785207572261029), (Int.negSucc 3458110767363891), (Int.negSucc 3458110767363874),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf324 : Bracket :=
  ⟨3256, 3257, (Int.negSucc 116294912215375777), (Int.negSucc 116294912215375774), (Int.ofNat 10181105847567844), (Int.ofNat 10181105847567848),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf325 : Bracket :=
  ⟨3273, 3274, (Int.ofNat 17714101194536465), (Int.ofNat 17714101194536473), (Int.negSucc 31172905488253212), (Int.negSucc 31172905488253194),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf326 : Bracket :=
  ⟨3277, 3278, (Int.negSucc 11014744621026691), (Int.negSucc 11014744621026682), (Int.ofNat 37441112607022277), (Int.ofNat 37441112607022292),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf327 : Bracket :=
  ⟨3287, 3288, (Int.ofNat 68618003899814272), (Int.ofNat 68618003899814283), (Int.negSucc 8410932327733909), (Int.negSucc 8410932327733906),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf328 : Bracket :=
  ⟨3295, 3296, (Int.negSucc 80039203676810489), (Int.negSucc 80039203676810480), (Int.ofNat 17128270462451933), (Int.ofNat 17128270462451935),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf329 : Bracket :=
  ⟨3309, 3310, (Int.ofNat 1573296409703857), (Int.ofNat 1573296409703871), (Int.negSucc 117901992153669191), (Int.negSucc 117901992153669178),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf330 : Bracket :=
  ⟨3316, 3317, (Int.negSucc 110993626168382242), (Int.negSucc 110993626168382239), (Int.ofNat 11926325258081425), (Int.ofNat 11926325258081440),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf331 : Bracket :=
  ⟨3326, 3327, (Int.ofNat 199105407834174227), (Int.ofNat 199105407834174234), (Int.negSucc 8618378368230319), (Int.negSucc 8618378368230310),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf332 : Bracket :=
  ⟨3343, 3344, (Int.negSucc 77885114657649968), (Int.negSucc 77885114657649955), (Int.ofNat 107911782040178855), (Int.ofNat 107911782040178858),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf333 : Bracket :=
  ⟨3353, 3354, (Int.ofNat 35018412054951933), (Int.ofNat 35018412054951948), (Int.negSucc 61500946041936644), (Int.negSucc 61500946041936634),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf334 : Bracket :=
  ⟨3364, 3365, (Int.negSucc 29404661895203047), (Int.negSucc 29404661895203044), (Int.ofNat 11199584149288181), (Int.ofNat 11199584149288186),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf335 : Bracket :=
  ⟨3372, 3373, (Int.ofNat 14157694104238768), (Int.ofNat 14157694104238778), (Int.negSucc 1823116256605168), (Int.negSucc 1823116256605164),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf336 : Bracket :=
  ⟨3377, 3378, (Int.negSucc 10150154892433486), (Int.negSucc 10150154892433471), (Int.ofNat 1921174119876895), (Int.ofNat 1921174119876909),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf337 : Bracket :=
  ⟨3387, 3388, (Int.ofNat 3270946732794937), (Int.ofNat 3270946732794940), (Int.negSucc 15806989273834327), (Int.negSucc 15806989273834324),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf338 : Bracket :=
  ⟨3395, 3396, (Int.negSucc 5101652980691603), (Int.negSucc 5101652980691590), (Int.ofNat 13851336434716145), (Int.ofNat 13851336434716149),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf339 : Bracket :=
  ⟨3400, 3401, (Int.ofNat 17902162749136143), (Int.ofNat 17902162749136146), (Int.negSucc 13181588549307965), (Int.negSucc 13181588549307957),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf340 : Bracket :=
  ⟨3414, 3415, (Int.negSucc 61584574161078286), (Int.negSucc 61584574161078280), (Int.ofNat 83250135189413150), (Int.ofNat 83250135189413155),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf341 : Bracket :=
  ⟨3429, 3430, (Int.ofNat 79332304375339760), (Int.ofNat 79332304375339771), (Int.negSucc 32593394668032019), (Int.negSucc 32593394668032008),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf342 : Bracket :=
  ⟨3436, 3437, (Int.negSucc 79816739121530614), (Int.negSucc 79816739121530611), (Int.ofNat 399537278339263), (Int.ofNat 399537278339279),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf343 : Bracket :=
  ⟨3448, 3449, (Int.ofNat 54804033324682050), (Int.ofNat 54804033324682053), (Int.negSucc 17324320392168390), (Int.negSucc 17324320392168385),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf344 : Bracket :=
  ⟨3457, 3458, (Int.negSucc 9482701720416040), (Int.negSucc 9482701720416036), (Int.ofNat 30994265379584550), (Int.ofNat 30994265379584559),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf345 : Bracket :=
  ⟨3462, 3463, (Int.ofNat 34498845979418151), (Int.ofNat 34498845979418157), (Int.negSucc 13822841089982385), (Int.negSucc 13822841089982374),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf346 : Bracket :=
  ⟨3473, 3474, (Int.negSucc 17755384385187431), (Int.negSucc 17755384385187419), (Int.ofNat 127742355420892218), (Int.ofNat 127742355420892230),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf347 : Bracket :=
  ⟨3485, 3486, (Int.ofNat 70299759143465659), (Int.ofNat 70299759143465675), (Int.negSucc 137841302355332383), (Int.negSucc 137841302355332370),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf348 : Bracket :=
  ⟨3493, 3494, (Int.negSucc 189482410171602144), (Int.negSucc 189482410171602137), (Int.ofNat 102871105647533329), (Int.ofNat 102871105647533334),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf349 : Bracket :=
  ⟨3509, 3510, (Int.ofNat 149239767801677190), (Int.ofNat 149239767801677195), (Int.negSucc 280365674173119053), (Int.negSucc 280365674173119043),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf350 : Bracket :=
  ⟨3521, 3522, (Int.negSucc 160253969633545717), (Int.negSucc 160253969633545709), (Int.ofNat 5465063910876596), (Int.ofNat 5465063910876613),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf351 : Bracket :=
  ⟨3525, 3526, (Int.ofNat 67372937118908843), (Int.ofNat 67372937118908846), (Int.negSucc 70651589741355174), (Int.negSucc 70651589741355169),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf352 : Bracket :=
  ⟨3540, 3541, (Int.negSucc 301916997809795108), (Int.negSucc 301916997809795105), (Int.ofNat 92138669231547361), (Int.ofNat 92138669231547375),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf353 : Bracket :=
  ⟨3553, 3554, (Int.ofNat 98508406951269729), (Int.ofNat 98508406951269738), (Int.negSucc 133880332136225959), (Int.negSucc 133880332136225946),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf354 : Bracket :=
  ⟨3562, 3563, (Int.negSucc 40458742464935151), (Int.negSucc 40458742464935142), (Int.ofNat 136489928798269560), (Int.ofNat 136489928798269566),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf355 : Bracket :=
  ⟨3574, 3575, (Int.ofNat 105598480947011084), (Int.ofNat 105598480947011087), (Int.negSucc 9847038841307996), (Int.negSucc 9847038841307992),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf356 : Bracket :=
  ⟨3584, 3585, (Int.negSucc 32307812566246127), (Int.negSucc 32307812566246125), (Int.ofNat 19448921703316498), (Int.ofNat 19448921703316502),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf357 : Bracket :=
  ⟨3594, 3595, (Int.ofNat 190295114209856), (Int.ofNat 190295114209869), (Int.negSucc 10396837044236948), (Int.negSucc 10396837044236944),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf358 : Bracket :=
  ⟨3596, 3597, (Int.negSucc 10286964726786989), (Int.negSucc 10286964726786986), (Int.ofNat 1288585031299299), (Int.ofNat 1288585031299306),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf359 : Bracket :=
  ⟨3612, 3613, (Int.ofNat 12736221891133225), (Int.ofNat 12736221891133227), (Int.negSucc 18292097096022766), (Int.negSucc 18292097096022755),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf360 : Bracket :=
  ⟨3619, 3620, (Int.negSucc 15035788925520046), (Int.negSucc 15035788925520042), (Int.ofNat 4388908991950758), (Int.ofNat 4388908991950761),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf361 : Bracket :=
  ⟨3627, 3628, (Int.ofNat 10224270487251972), (Int.ofNat 10224270487251976), (Int.negSucc 4096615565818545), (Int.negSucc 4096615565818542),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf362 : Bracket :=
  ⟨3632, 3633, (Int.negSucc 10812252832511259), (Int.negSucc 10812252832511257), (Int.ofNat 6029588809242658), (Int.ofNat 6029588809242669),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf363 : Bracket :=
  ⟨3640, 3641, (Int.ofNat 27059447902429933), (Int.ofNat 27059447902429935), (Int.negSucc 39671562922177615), (Int.negSucc 39671562922177610),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf364 : Bracket :=
  ⟨3660, 3661, (Int.negSucc 94421091386475331), (Int.negSucc 94421091386475329), (Int.ofNat 30395785843751101), (Int.ofNat 30395785843751112),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf365 : Bracket :=
  ⟨3667, 3668, (Int.ofNat 6470892876409549), (Int.ofNat 6470892876409556), (Int.negSucc 87907426865664850), (Int.negSucc 87907426865664847),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf366 : Bracket :=
  ⟨3676, 3677, (Int.negSucc 118123294958011164), (Int.negSucc 118123294958011161), (Int.ofNat 13715471329692752), (Int.ofNat 13715471329692762),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf367 : Bracket :=
  ⟨3689, 3690, (Int.ofNat 111228363990472049), (Int.ofNat 111228363990472063), (Int.negSucc 36867166609793920), (Int.negSucc 36867166609793914),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf368 : Bracket :=
  ⟨3701, 3702, (Int.negSucc 21362980839751704), (Int.negSucc 21362980839751696), (Int.ofNat 45745536631083543), (Int.ofNat 45745536631083558),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf369 : Bracket :=
  ⟨3707, 3708, (Int.ofNat 8216049926154259), (Int.ofNat 8216049926154274), (Int.negSucc 63914291681908838), (Int.negSucc 63914291681908836),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf370 : Bracket :=
  ⟨3722, 3723, (Int.negSucc 1694413511614524), (Int.negSucc 1694413511614506), (Int.ofNat 2585776358649838), (Int.ofNat 2585776358649841),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf371 : Bracket :=
  ⟨3723, 3724, (Int.ofNat 2585776358649838), (Int.ofNat 2585776358649841), (Int.negSucc 18551682951118294), (Int.negSucc 18551682951118291),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf372 : Bracket :=
  ⟨3739, 3740, (Int.negSucc 66907066617419782), (Int.negSucc 66907066617419777), (Int.ofNat 31191222595510203), (Int.ofNat 31191222595510205),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf373 : Bracket :=
  ⟨3747, 3748, (Int.ofNat 40853226765825923), (Int.ofNat 40853226765825927), (Int.negSucc 38873140226073146), (Int.negSucc 38873140226073142),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf374 : Bracket :=
  ⟨3758, 3759, (Int.negSucc 43391358498685172), (Int.negSucc 43391358498685157), (Int.ofNat 11378964079467925), (Int.ofNat 11378964079467941),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf375 : Bracket :=
  ⟨3762, 3763, (Int.ofNat 31592428482495390), (Int.ofNat 31592428482495398), (Int.negSucc 26741863057531462), (Int.negSucc 26741863057531448),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf376 : Bracket :=
  ⟨3780, 3781, (Int.negSucc 47428573396245568), (Int.negSucc 47428573396245565), (Int.ofNat 90435420429949452), (Int.ofNat 90435420429949460),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf377 : Bracket :=
  ⟨3788, 3789, (Int.ofNat 39144738011208307), (Int.ofNat 39144738011208310), (Int.negSucc 50187287839500495), (Int.negSucc 50187287839500491),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf378 : Bracket :=
  ⟨3795, 3796, (Int.negSucc 40865898086986173), (Int.negSucc 40865898086986166), (Int.ofNat 75352562883717642), (Int.ofNat 75352562883717645),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf379 : Bracket :=
  ⟨3807, 3808, (Int.ofNat 108544512057974501), (Int.ofNat 108544512057974504), (Int.negSucc 76136017014976605), (Int.negSucc 76136017014976602),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf380 : Bracket :=
  ⟨3816, 3817, (Int.negSucc 179386293537649827), (Int.negSucc 179386293537649824), (Int.ofNat 25003694941173080), (Int.ofNat 25003694941173084),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf381 : Bracket :=
  ⟨3826, 3827, (Int.ofNat 184023552539151387), (Int.ofNat 184023552539151395), (Int.negSucc 169950233706113959), (Int.negSucc 169950233706113956),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf382 : Bracket :=
  ⟨3846, 3847, (Int.negSucc 117999039528386073), (Int.negSucc 117999039528386058), (Int.ofNat 30038305007603278), (Int.ofNat 30038305007603282),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf383 : Bracket :=
  ⟨3852, 3853, (Int.ofNat 23415259256025915), (Int.ofNat 23415259256025918), (Int.negSucc 47157046512087731), (Int.negSucc 47157046512087728),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf384 : Bracket :=
  ⟨3859, 3860, (Int.negSucc 62096950715818963), (Int.negSucc 62096950715818960), (Int.ofNat 17594110500607600), (Int.ofNat 17594110500607603),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf385 : Bracket :=
  ⟨3871, 3872, (Int.ofNat 13870434868107137), (Int.ofNat 13870434868107140), (Int.negSucc 69580642029333306), (Int.negSucc 69580642029333305),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf386 : Bracket :=
  ⟨3878, 3879, (Int.negSucc 77884510344807525), (Int.negSucc 77884510344807512), (Int.ofNat 4693374799548499), (Int.ofNat 4693374799548502),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf387 : Bracket :=
  ⟨3888, 3889, (Int.ofNat 110220892855023366), (Int.ofNat 110220892855023368), (Int.negSucc 13555049754984085), (Int.negSucc 13555049754984077),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf388 : Bracket :=
  ⟨3901, 3902, (Int.negSucc 115327407369748163), (Int.negSucc 115327407369748154), (Int.ofNat 10022501302039186), (Int.ofNat 10022501302039202),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf389 : Bracket :=
  ⟨3910, 3911, (Int.ofNat 44648562881967814), (Int.ofNat 44648562881967830), (Int.negSucc 63863084870466241), (Int.negSucc 63863084870466238),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf390 : Bracket :=
  ⟨3924, 3925, (Int.negSucc 11995559349163694), (Int.negSucc 11995559349163690), (Int.ofNat 43613573160401416), (Int.ofNat 43613573160401420),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf391 : Bracket :=
  ⟨3931, 3932, (Int.ofNat 13850789849644236), (Int.ofNat 13850789849644239), (Int.negSucc 22286550868498322), (Int.negSucc 22286550868498320),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf392 : Bracket :=
  ⟨3938, 3939, (Int.negSucc 29545086788710383), (Int.negSucc 29545086788710370), (Int.ofNat 9068966458235058), (Int.ofNat 9068966458235073),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf393 : Bracket :=
  ⟨3948, 3949, (Int.ofNat 129882752601609), (Int.ofNat 129882752601612), (Int.negSucc 67171897829142035), (Int.negSucc 67171897829142023),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf394 : Bracket :=
  ⟨3963, 3964, (Int.negSucc 10524308016082779), (Int.negSucc 10524308016082769), (Int.ofNat 13195925537491037), (Int.ofNat 13195925537491040),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf395 : Bracket :=
  ⟨3966, 3967, (Int.ofNat 15962197765927158), (Int.ofNat 15962197765927166), (Int.negSucc 2519273061608633), (Int.negSucc 2519273061608630),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf396 : Bracket :=
  ⟨3977, 3978, (Int.negSucc 6127043051618966), (Int.negSucc 6127043051618956), (Int.ofNat 52827855993872405), (Int.ofNat 52827855993872415),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf397 : Bracket :=
  ⟨3989, 3990, (Int.ofNat 36480931940552547), (Int.ofNat 36480931940552552), (Int.negSucc 22898809732098864), (Int.negSucc 22898809732098851),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf398 : Bracket :=
  ⟨3999, 4000, (Int.negSucc 3832297740180104), (Int.negSucc 3832297740180101), (Int.ofNat 34940914224467856), (Int.ofNat 34940914224467858),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf399 : Bracket :=
  ⟨4007, 4008, (Int.ofNat 22105545464577391), (Int.ofNat 22105545464577398), (Int.negSucc 9939151533105058), (Int.negSucc 9939151533105057),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf400 : Bracket :=
  ⟨4016, 4017, (Int.negSucc 5016497995824449), (Int.negSucc 5016497995824446), (Int.ofNat 20074633987431471), (Int.ofNat 20074633987431475),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf401 : Bracket :=
  ⟨4022, 4023, (Int.ofNat 12338688898870945), (Int.ofNat 12338688898870949), (Int.negSucc 19117528378403762), (Int.negSucc 19117528378403760),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf402 : Bracket :=
  ⟨4030, 4031, (Int.negSucc 6097155502813068), (Int.negSucc 6097155502813065), (Int.ofNat 70130158408736821), (Int.ofNat 70130158408736824),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf403 : Bracket :=
  ⟨4038, 4039, (Int.ofNat 123194390735779138), (Int.ofNat 123194390735779140), (Int.negSucc 117222830531846958), (Int.negSucc 117222830531846955),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf404 : Bracket :=
  ⟨4059, 4060, (Int.negSucc 381280825788312416), (Int.negSucc 381280825788312413), (Int.ofNat 506013085993840383), (Int.ofNat 506013085993840385),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf405 : Bracket :=
  ⟨4075, 4076, (Int.ofNat 86087520671889071), (Int.ofNat 86087520671889074), (Int.negSucc 35871940977776236), (Int.negSucc 35871940977776234),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf406 : Bracket :=
  ⟨4077, 4078, (Int.negSucc 52697254521833084), (Int.negSucc 52697254521833081), (Int.ofNat 28010764318360076), (Int.ofNat 28010764318360079),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf407 : Bracket :=
  ⟨4093, 4094, (Int.ofNat 256034637795309096), (Int.ofNat 256034637795309099), (Int.negSucc 5620520525646034), (Int.negSucc 5620520525646032),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def node0 : Tree 19 31 2 :=
  Tree.join (Tree.leaf leaf1) (Tree.leaf leaf2) (by decide +kernel)
noncomputable def node1 : Tree 6 31 3 :=
  Tree.join (Tree.leaf leaf0) (node0) (by decide +kernel)
noncomputable def node2 : Tree 56 69 2 :=
  Tree.join (Tree.leaf leaf4) (Tree.leaf leaf5) (by decide +kernel)
noncomputable def node3 : Tree 46 69 3 :=
  Tree.join (Tree.leaf leaf3) (node2) (by decide +kernel)
noncomputable def node4 : Tree 6 69 6 :=
  Tree.join (node1) (node3) (by decide +kernel)
noncomputable def node5 : Tree 90 97 2 :=
  Tree.join (Tree.leaf leaf7) (Tree.leaf leaf8) (by decide +kernel)
noncomputable def node6 : Tree 83 97 3 :=
  Tree.join (Tree.leaf leaf6) (node5) (by decide +kernel)
noncomputable def node7 : Tree 112 117 2 :=
  Tree.join (Tree.leaf leaf10) (Tree.leaf leaf11) (by decide +kernel)
noncomputable def node8 : Tree 108 117 3 :=
  Tree.join (Tree.leaf leaf9) (node7) (by decide +kernel)
noncomputable def node9 : Tree 83 117 6 :=
  Tree.join (node6) (node8) (by decide +kernel)
noncomputable def node10 : Tree 6 117 12 :=
  Tree.join (node4) (node9) (by decide +kernel)
noncomputable def node11 : Tree 143 159 2 :=
  Tree.join (Tree.leaf leaf13) (Tree.leaf leaf14) (by decide +kernel)
noncomputable def node12 : Tree 132 159 3 :=
  Tree.join (Tree.leaf leaf12) (node11) (by decide +kernel)
noncomputable def node13 : Tree 171 177 2 :=
  Tree.join (Tree.leaf leaf16) (Tree.leaf leaf17) (by decide +kernel)
noncomputable def node14 : Tree 165 177 3 :=
  Tree.join (Tree.leaf leaf15) (node13) (by decide +kernel)
noncomputable def node15 : Tree 132 177 6 :=
  Tree.join (node12) (node14) (by decide +kernel)
noncomputable def node16 : Tree 197 213 2 :=
  Tree.join (Tree.leaf leaf19) (Tree.leaf leaf20) (by decide +kernel)
noncomputable def node17 : Tree 193 213 3 :=
  Tree.join (Tree.leaf leaf18) (node16) (by decide +kernel)
noncomputable def node18 : Tree 226 234 2 :=
  Tree.join (Tree.leaf leaf21) (Tree.leaf leaf22) (by decide +kernel)
noncomputable def node19 : Tree 247 253 2 :=
  Tree.join (Tree.leaf leaf23) (Tree.leaf leaf24) (by decide +kernel)
noncomputable def node20 : Tree 226 253 4 :=
  Tree.join (node18) (node19) (by decide +kernel)
noncomputable def node21 : Tree 193 253 7 :=
  Tree.join (node17) (node20) (by decide +kernel)
noncomputable def node22 : Tree 132 253 13 :=
  Tree.join (node15) (node21) (by decide +kernel)
noncomputable def node23 : Tree 6 253 25 :=
  Tree.join (node10) (node22) (by decide +kernel)
noncomputable def node24 : Tree 270 277 2 :=
  Tree.join (Tree.leaf leaf26) (Tree.leaf leaf27) (by decide +kernel)
noncomputable def node25 : Tree 263 277 3 :=
  Tree.join (Tree.leaf leaf25) (node24) (by decide +kernel)
noncomputable def node26 : Tree 304 316 2 :=
  Tree.join (Tree.leaf leaf29) (Tree.leaf leaf30) (by decide +kernel)
noncomputable def node27 : Tree 289 316 3 :=
  Tree.join (Tree.leaf leaf28) (node26) (by decide +kernel)
noncomputable def node28 : Tree 263 316 6 :=
  Tree.join (node25) (node27) (by decide +kernel)
noncomputable def node29 : Tree 333 348 2 :=
  Tree.join (Tree.leaf leaf32) (Tree.leaf leaf33) (by decide +kernel)
noncomputable def node30 : Tree 319 348 3 :=
  Tree.join (Tree.leaf leaf31) (node29) (by decide +kernel)
noncomputable def node31 : Tree 356 364 2 :=
  Tree.join (Tree.leaf leaf34) (Tree.leaf leaf35) (by decide +kernel)
noncomputable def node32 : Tree 373 387 2 :=
  Tree.join (Tree.leaf leaf36) (Tree.leaf leaf37) (by decide +kernel)
noncomputable def node33 : Tree 356 387 4 :=
  Tree.join (node31) (node32) (by decide +kernel)
noncomputable def node34 : Tree 319 387 7 :=
  Tree.join (node30) (node33) (by decide +kernel)
noncomputable def node35 : Tree 263 387 13 :=
  Tree.join (node28) (node34) (by decide +kernel)
noncomputable def node36 : Tree 403 415 2 :=
  Tree.join (Tree.leaf leaf39) (Tree.leaf leaf40) (by decide +kernel)
noncomputable def node37 : Tree 396 415 3 :=
  Tree.join (Tree.leaf leaf38) (node36) (by decide +kernel)
noncomputable def node38 : Tree 435 448 2 :=
  Tree.join (Tree.leaf leaf42) (Tree.leaf leaf43) (by decide +kernel)
noncomputable def node39 : Tree 423 448 3 :=
  Tree.join (Tree.leaf leaf41) (node38) (by decide +kernel)
noncomputable def node40 : Tree 396 448 6 :=
  Tree.join (node37) (node39) (by decide +kernel)
noncomputable def node41 : Tree 468 477 2 :=
  Tree.join (Tree.leaf leaf45) (Tree.leaf leaf46) (by decide +kernel)
noncomputable def node42 : Tree 459 477 3 :=
  Tree.join (Tree.leaf leaf44) (node41) (by decide +kernel)
noncomputable def node43 : Tree 480 492 2 :=
  Tree.join (Tree.leaf leaf47) (Tree.leaf leaf48) (by decide +kernel)
noncomputable def node44 : Tree 502 516 2 :=
  Tree.join (Tree.leaf leaf49) (Tree.leaf leaf50) (by decide +kernel)
noncomputable def node45 : Tree 480 516 4 :=
  Tree.join (node43) (node44) (by decide +kernel)
noncomputable def node46 : Tree 459 516 7 :=
  Tree.join (node42) (node45) (by decide +kernel)
noncomputable def node47 : Tree 396 516 13 :=
  Tree.join (node40) (node46) (by decide +kernel)
noncomputable def node48 : Tree 263 516 26 :=
  Tree.join (node35) (node47) (by decide +kernel)
noncomputable def node49 : Tree 6 516 51 :=
  Tree.join (node23) (node48) (by decide +kernel)
noncomputable def node50 : Tree 528 533 2 :=
  Tree.join (Tree.leaf leaf52) (Tree.leaf leaf53) (by decide +kernel)
noncomputable def node51 : Tree 519 533 3 :=
  Tree.join (Tree.leaf leaf51) (node50) (by decide +kernel)
noncomputable def node52 : Tree 565 574 2 :=
  Tree.join (Tree.leaf leaf55) (Tree.leaf leaf56) (by decide +kernel)
noncomputable def node53 : Tree 548 574 3 :=
  Tree.join (Tree.leaf leaf54) (node52) (by decide +kernel)
noncomputable def node54 : Tree 519 574 6 :=
  Tree.join (node51) (node53) (by decide +kernel)
noncomputable def node55 : Tree 593 609 2 :=
  Tree.join (Tree.leaf leaf58) (Tree.leaf leaf59) (by decide +kernel)
noncomputable def node56 : Tree 583 609 3 :=
  Tree.join (Tree.leaf leaf57) (node55) (by decide +kernel)
noncomputable def node57 : Tree 624 639 2 :=
  Tree.join (Tree.leaf leaf61) (Tree.leaf leaf62) (by decide +kernel)
noncomputable def node58 : Tree 613 639 3 :=
  Tree.join (Tree.leaf leaf60) (node57) (by decide +kernel)
noncomputable def node59 : Tree 583 639 6 :=
  Tree.join (node56) (node58) (by decide +kernel)
noncomputable def node60 : Tree 519 639 12 :=
  Tree.join (node54) (node59) (by decide +kernel)
noncomputable def node61 : Tree 656 668 2 :=
  Tree.join (Tree.leaf leaf64) (Tree.leaf leaf65) (by decide +kernel)
noncomputable def node62 : Tree 643 668 3 :=
  Tree.join (Tree.leaf leaf63) (node61) (by decide +kernel)
noncomputable def node63 : Tree 688 696 2 :=
  Tree.join (Tree.leaf leaf67) (Tree.leaf leaf68) (by decide +kernel)
noncomputable def node64 : Tree 677 696 3 :=
  Tree.join (Tree.leaf leaf66) (node63) (by decide +kernel)
noncomputable def node65 : Tree 643 696 6 :=
  Tree.join (node62) (node64) (by decide +kernel)
noncomputable def node66 : Tree 713 727 2 :=
  Tree.join (Tree.leaf leaf70) (Tree.leaf leaf71) (by decide +kernel)
noncomputable def node67 : Tree 702 727 3 :=
  Tree.join (Tree.leaf leaf69) (node66) (by decide +kernel)
noncomputable def node68 : Tree 731 746 2 :=
  Tree.join (Tree.leaf leaf72) (Tree.leaf leaf73) (by decide +kernel)
noncomputable def node69 : Tree 750 764 2 :=
  Tree.join (Tree.leaf leaf74) (Tree.leaf leaf75) (by decide +kernel)
noncomputable def node70 : Tree 731 764 4 :=
  Tree.join (node68) (node69) (by decide +kernel)
noncomputable def node71 : Tree 702 764 7 :=
  Tree.join (node67) (node70) (by decide +kernel)
noncomputable def node72 : Tree 643 764 13 :=
  Tree.join (node65) (node71) (by decide +kernel)
noncomputable def node73 : Tree 519 764 25 :=
  Tree.join (node60) (node72) (by decide +kernel)
noncomputable def node74 : Tree 787 798 2 :=
  Tree.join (Tree.leaf leaf77) (Tree.leaf leaf78) (by decide +kernel)
noncomputable def node75 : Tree 772 798 3 :=
  Tree.join (Tree.leaf leaf76) (node74) (by decide +kernel)
noncomputable def node76 : Tree 810 822 2 :=
  Tree.join (Tree.leaf leaf80) (Tree.leaf leaf81) (by decide +kernel)
noncomputable def node77 : Tree 806 822 3 :=
  Tree.join (Tree.leaf leaf79) (node76) (by decide +kernel)
noncomputable def node78 : Tree 772 822 6 :=
  Tree.join (node75) (node77) (by decide +kernel)
noncomputable def node79 : Tree 845 854 2 :=
  Tree.join (Tree.leaf leaf83) (Tree.leaf leaf84) (by decide +kernel)
noncomputable def node80 : Tree 833 854 3 :=
  Tree.join (Tree.leaf leaf82) (node79) (by decide +kernel)
noncomputable def node81 : Tree 862 872 2 :=
  Tree.join (Tree.leaf leaf85) (Tree.leaf leaf86) (by decide +kernel)
noncomputable def node82 : Tree 884 886 2 :=
  Tree.join (Tree.leaf leaf87) (Tree.leaf leaf88) (by decide +kernel)
noncomputable def node83 : Tree 862 886 4 :=
  Tree.join (node81) (node82) (by decide +kernel)
noncomputable def node84 : Tree 833 886 7 :=
  Tree.join (node80) (node83) (by decide +kernel)
noncomputable def node85 : Tree 772 886 13 :=
  Tree.join (node78) (node84) (by decide +kernel)
noncomputable def node86 : Tree 917 926 2 :=
  Tree.join (Tree.leaf leaf90) (Tree.leaf leaf91) (by decide +kernel)
noncomputable def node87 : Tree 898 926 3 :=
  Tree.join (Tree.leaf leaf89) (node86) (by decide +kernel)
noncomputable def node88 : Tree 944 959 2 :=
  Tree.join (Tree.leaf leaf93) (Tree.leaf leaf94) (by decide +kernel)
noncomputable def node89 : Tree 935 959 3 :=
  Tree.join (Tree.leaf leaf92) (node88) (by decide +kernel)
noncomputable def node90 : Tree 898 959 6 :=
  Tree.join (node87) (node89) (by decide +kernel)
noncomputable def node91 : Tree 981 990 2 :=
  Tree.join (Tree.leaf leaf96) (Tree.leaf leaf97) (by decide +kernel)
noncomputable def node92 : Tree 969 990 3 :=
  Tree.join (Tree.leaf leaf95) (node91) (by decide +kernel)
noncomputable def node93 : Tree 998 1006 2 :=
  Tree.join (Tree.leaf leaf98) (Tree.leaf leaf99) (by decide +kernel)
noncomputable def node94 : Tree 1019 1026 2 :=
  Tree.join (Tree.leaf leaf100) (Tree.leaf leaf101) (by decide +kernel)
noncomputable def node95 : Tree 998 1026 4 :=
  Tree.join (node93) (node94) (by decide +kernel)
noncomputable def node96 : Tree 969 1026 7 :=
  Tree.join (node92) (node95) (by decide +kernel)
noncomputable def node97 : Tree 898 1026 13 :=
  Tree.join (node90) (node96) (by decide +kernel)
noncomputable def node98 : Tree 772 1026 26 :=
  Tree.join (node85) (node97) (by decide +kernel)
noncomputable def node99 : Tree 519 1026 51 :=
  Tree.join (node73) (node98) (by decide +kernel)
noncomputable def node100 : Tree 6 1026 102 :=
  Tree.join (node49) (node99) (by decide +kernel)
noncomputable def node101 : Tree 1041 1051 2 :=
  Tree.join (Tree.leaf leaf103) (Tree.leaf leaf104) (by decide +kernel)
noncomputable def node102 : Tree 1028 1051 3 :=
  Tree.join (Tree.leaf leaf102) (node101) (by decide +kernel)
noncomputable def node103 : Tree 1074 1084 2 :=
  Tree.join (Tree.leaf leaf106) (Tree.leaf leaf107) (by decide +kernel)
noncomputable def node104 : Tree 1068 1084 3 :=
  Tree.join (Tree.leaf leaf105) (node103) (by decide +kernel)
noncomputable def node105 : Tree 1028 1084 6 :=
  Tree.join (node102) (node104) (by decide +kernel)
noncomputable def node106 : Tree 1102 1115 2 :=
  Tree.join (Tree.leaf leaf109) (Tree.leaf leaf110) (by decide +kernel)
noncomputable def node107 : Tree 1096 1115 3 :=
  Tree.join (Tree.leaf leaf108) (node106) (by decide +kernel)
noncomputable def node108 : Tree 1129 1139 2 :=
  Tree.join (Tree.leaf leaf112) (Tree.leaf leaf113) (by decide +kernel)
noncomputable def node109 : Tree 1120 1139 3 :=
  Tree.join (Tree.leaf leaf111) (node108) (by decide +kernel)
noncomputable def node110 : Tree 1096 1139 6 :=
  Tree.join (node107) (node109) (by decide +kernel)
noncomputable def node111 : Tree 1028 1139 12 :=
  Tree.join (node105) (node110) (by decide +kernel)
noncomputable def node112 : Tree 1168 1180 2 :=
  Tree.join (Tree.leaf leaf115) (Tree.leaf leaf116) (by decide +kernel)
noncomputable def node113 : Tree 1150 1180 3 :=
  Tree.join (Tree.leaf leaf114) (node112) (by decide +kernel)
noncomputable def node114 : Tree 1191 1213 2 :=
  Tree.join (Tree.leaf leaf118) (Tree.leaf leaf119) (by decide +kernel)
noncomputable def node115 : Tree 1184 1213 3 :=
  Tree.join (Tree.leaf leaf117) (node114) (by decide +kernel)
noncomputable def node116 : Tree 1150 1213 6 :=
  Tree.join (node113) (node115) (by decide +kernel)
noncomputable def node117 : Tree 1225 1239 2 :=
  Tree.join (Tree.leaf leaf121) (Tree.leaf leaf122) (by decide +kernel)
noncomputable def node118 : Tree 1219 1239 3 :=
  Tree.join (Tree.leaf leaf120) (node117) (by decide +kernel)
noncomputable def node119 : Tree 1244 1258 2 :=
  Tree.join (Tree.leaf leaf123) (Tree.leaf leaf124) (by decide +kernel)
noncomputable def node120 : Tree 1265 1271 2 :=
  Tree.join (Tree.leaf leaf125) (Tree.leaf leaf126) (by decide +kernel)
noncomputable def node121 : Tree 1244 1271 4 :=
  Tree.join (node119) (node120) (by decide +kernel)
noncomputable def node122 : Tree 1219 1271 7 :=
  Tree.join (node118) (node121) (by decide +kernel)
noncomputable def node123 : Tree 1150 1271 13 :=
  Tree.join (node116) (node122) (by decide +kernel)
noncomputable def node124 : Tree 1028 1271 25 :=
  Tree.join (node111) (node123) (by decide +kernel)
noncomputable def node125 : Tree 1294 1303 2 :=
  Tree.join (Tree.leaf leaf128) (Tree.leaf leaf129) (by decide +kernel)
noncomputable def node126 : Tree 1283 1303 3 :=
  Tree.join (Tree.leaf leaf127) (node125) (by decide +kernel)
noncomputable def node127 : Tree 1326 1341 2 :=
  Tree.join (Tree.leaf leaf131) (Tree.leaf leaf132) (by decide +kernel)
noncomputable def node128 : Tree 1322 1341 3 :=
  Tree.join (Tree.leaf leaf130) (node127) (by decide +kernel)
noncomputable def node129 : Tree 1283 1341 6 :=
  Tree.join (node126) (node128) (by decide +kernel)
noncomputable def node130 : Tree 1356 1361 2 :=
  Tree.join (Tree.leaf leaf134) (Tree.leaf leaf135) (by decide +kernel)
noncomputable def node131 : Tree 1346 1361 3 :=
  Tree.join (Tree.leaf leaf133) (node130) (by decide +kernel)
noncomputable def node132 : Tree 1375 1383 2 :=
  Tree.join (Tree.leaf leaf136) (Tree.leaf leaf137) (by decide +kernel)
noncomputable def node133 : Tree 1399 1404 2 :=
  Tree.join (Tree.leaf leaf138) (Tree.leaf leaf139) (by decide +kernel)
noncomputable def node134 : Tree 1375 1404 4 :=
  Tree.join (node132) (node133) (by decide +kernel)
noncomputable def node135 : Tree 1346 1404 7 :=
  Tree.join (node131) (node134) (by decide +kernel)
noncomputable def node136 : Tree 1283 1404 13 :=
  Tree.join (node129) (node135) (by decide +kernel)
noncomputable def node137 : Tree 1421 1429 2 :=
  Tree.join (Tree.leaf leaf141) (Tree.leaf leaf142) (by decide +kernel)
noncomputable def node138 : Tree 1410 1429 3 :=
  Tree.join (Tree.leaf leaf140) (node137) (by decide +kernel)
noncomputable def node139 : Tree 1455 1461 2 :=
  Tree.join (Tree.leaf leaf144) (Tree.leaf leaf145) (by decide +kernel)
noncomputable def node140 : Tree 1444 1461 3 :=
  Tree.join (Tree.leaf leaf143) (node139) (by decide +kernel)
noncomputable def node141 : Tree 1410 1461 6 :=
  Tree.join (node138) (node140) (by decide +kernel)
noncomputable def node142 : Tree 1488 1503 2 :=
  Tree.join (Tree.leaf leaf147) (Tree.leaf leaf148) (by decide +kernel)
noncomputable def node143 : Tree 1464 1503 3 :=
  Tree.join (Tree.leaf leaf146) (node142) (by decide +kernel)
noncomputable def node144 : Tree 1509 1521 2 :=
  Tree.join (Tree.leaf leaf149) (Tree.leaf leaf150) (by decide +kernel)
noncomputable def node145 : Tree 1526 1535 2 :=
  Tree.join (Tree.leaf leaf151) (Tree.leaf leaf152) (by decide +kernel)
noncomputable def node146 : Tree 1509 1535 4 :=
  Tree.join (node144) (node145) (by decide +kernel)
noncomputable def node147 : Tree 1464 1535 7 :=
  Tree.join (node143) (node146) (by decide +kernel)
noncomputable def node148 : Tree 1410 1535 13 :=
  Tree.join (node141) (node147) (by decide +kernel)
noncomputable def node149 : Tree 1283 1535 26 :=
  Tree.join (node136) (node148) (by decide +kernel)
noncomputable def node150 : Tree 1028 1535 51 :=
  Tree.join (node124) (node149) (by decide +kernel)
noncomputable def node151 : Tree 1558 1569 2 :=
  Tree.join (Tree.leaf leaf154) (Tree.leaf leaf155) (by decide +kernel)
noncomputable def node152 : Tree 1546 1569 3 :=
  Tree.join (Tree.leaf leaf153) (node151) (by decide +kernel)
noncomputable def node153 : Tree 1588 1597 2 :=
  Tree.join (Tree.leaf leaf157) (Tree.leaf leaf158) (by decide +kernel)
noncomputable def node154 : Tree 1582 1597 3 :=
  Tree.join (Tree.leaf leaf156) (node153) (by decide +kernel)
noncomputable def node155 : Tree 1546 1597 6 :=
  Tree.join (node152) (node154) (by decide +kernel)
noncomputable def node156 : Tree 1616 1624 2 :=
  Tree.join (Tree.leaf leaf160) (Tree.leaf leaf161) (by decide +kernel)
noncomputable def node157 : Tree 1606 1624 3 :=
  Tree.join (Tree.leaf leaf159) (node156) (by decide +kernel)
noncomputable def node158 : Tree 1639 1654 2 :=
  Tree.join (Tree.leaf leaf163) (Tree.leaf leaf164) (by decide +kernel)
noncomputable def node159 : Tree 1633 1654 3 :=
  Tree.join (Tree.leaf leaf162) (node158) (by decide +kernel)
noncomputable def node160 : Tree 1606 1654 6 :=
  Tree.join (node157) (node159) (by decide +kernel)
noncomputable def node161 : Tree 1546 1654 12 :=
  Tree.join (node155) (node160) (by decide +kernel)
noncomputable def node162 : Tree 1671 1686 2 :=
  Tree.join (Tree.leaf leaf166) (Tree.leaf leaf167) (by decide +kernel)
noncomputable def node163 : Tree 1661 1686 3 :=
  Tree.join (Tree.leaf leaf165) (node162) (by decide +kernel)
noncomputable def node164 : Tree 1707 1718 2 :=
  Tree.join (Tree.leaf leaf169) (Tree.leaf leaf170) (by decide +kernel)
noncomputable def node165 : Tree 1696 1718 3 :=
  Tree.join (Tree.leaf leaf168) (node164) (by decide +kernel)
noncomputable def node166 : Tree 1661 1718 6 :=
  Tree.join (node163) (node165) (by decide +kernel)
noncomputable def node167 : Tree 1733 1748 2 :=
  Tree.join (Tree.leaf leaf172) (Tree.leaf leaf173) (by decide +kernel)
noncomputable def node168 : Tree 1726 1748 3 :=
  Tree.join (Tree.leaf leaf171) (node167) (by decide +kernel)
noncomputable def node169 : Tree 1756 1762 2 :=
  Tree.join (Tree.leaf leaf174) (Tree.leaf leaf175) (by decide +kernel)
noncomputable def node170 : Tree 1768 1786 2 :=
  Tree.join (Tree.leaf leaf176) (Tree.leaf leaf177) (by decide +kernel)
noncomputable def node171 : Tree 1756 1786 4 :=
  Tree.join (node169) (node170) (by decide +kernel)
noncomputable def node172 : Tree 1726 1786 7 :=
  Tree.join (node168) (node171) (by decide +kernel)
noncomputable def node173 : Tree 1661 1786 13 :=
  Tree.join (node166) (node172) (by decide +kernel)
noncomputable def node174 : Tree 1546 1786 25 :=
  Tree.join (node161) (node173) (by decide +kernel)
noncomputable def node175 : Tree 1810 1821 2 :=
  Tree.join (Tree.leaf leaf179) (Tree.leaf leaf180) (by decide +kernel)
noncomputable def node176 : Tree 1798 1821 3 :=
  Tree.join (Tree.leaf leaf178) (node175) (by decide +kernel)
noncomputable def node177 : Tree 1837 1842 2 :=
  Tree.join (Tree.leaf leaf182) (Tree.leaf leaf183) (by decide +kernel)
noncomputable def node178 : Tree 1827 1842 3 :=
  Tree.join (Tree.leaf leaf181) (node177) (by decide +kernel)
noncomputable def node179 : Tree 1798 1842 6 :=
  Tree.join (node176) (node178) (by decide +kernel)
noncomputable def node180 : Tree 1871 1879 2 :=
  Tree.join (Tree.leaf leaf185) (Tree.leaf leaf186) (by decide +kernel)
noncomputable def node181 : Tree 1857 1879 3 :=
  Tree.join (Tree.leaf leaf184) (node180) (by decide +kernel)
noncomputable def node182 : Tree 1887 1894 2 :=
  Tree.join (Tree.leaf leaf187) (Tree.leaf leaf188) (by decide +kernel)
noncomputable def node183 : Tree 1905 1921 2 :=
  Tree.join (Tree.leaf leaf189) (Tree.leaf leaf190) (by decide +kernel)
noncomputable def node184 : Tree 1887 1921 4 :=
  Tree.join (node182) (node183) (by decide +kernel)
noncomputable def node185 : Tree 1857 1921 7 :=
  Tree.join (node181) (node184) (by decide +kernel)
noncomputable def node186 : Tree 1798 1921 13 :=
  Tree.join (node179) (node185) (by decide +kernel)
noncomputable def node187 : Tree 1936 1948 2 :=
  Tree.join (Tree.leaf leaf192) (Tree.leaf leaf193) (by decide +kernel)
noncomputable def node188 : Tree 1927 1948 3 :=
  Tree.join (Tree.leaf leaf191) (node187) (by decide +kernel)
noncomputable def node189 : Tree 1965 1968 2 :=
  Tree.join (Tree.leaf leaf195) (Tree.leaf leaf196) (by decide +kernel)
noncomputable def node190 : Tree 1958 1968 3 :=
  Tree.join (Tree.leaf leaf194) (node189) (by decide +kernel)
noncomputable def node191 : Tree 1927 1968 6 :=
  Tree.join (node188) (node190) (by decide +kernel)
noncomputable def node192 : Tree 1993 2006 2 :=
  Tree.join (Tree.leaf leaf198) (Tree.leaf leaf199) (by decide +kernel)
noncomputable def node193 : Tree 1980 2006 3 :=
  Tree.join (Tree.leaf leaf197) (node192) (by decide +kernel)
noncomputable def node194 : Tree 2010 2026 2 :=
  Tree.join (Tree.leaf leaf200) (Tree.leaf leaf201) (by decide +kernel)
noncomputable def node195 : Tree 2031 2043 2 :=
  Tree.join (Tree.leaf leaf202) (Tree.leaf leaf203) (by decide +kernel)
noncomputable def node196 : Tree 2010 2043 4 :=
  Tree.join (node194) (node195) (by decide +kernel)
noncomputable def node197 : Tree 1980 2043 7 :=
  Tree.join (node193) (node196) (by decide +kernel)
noncomputable def node198 : Tree 1927 2043 13 :=
  Tree.join (node191) (node197) (by decide +kernel)
noncomputable def node199 : Tree 1798 2043 26 :=
  Tree.join (node186) (node198) (by decide +kernel)
noncomputable def node200 : Tree 1546 2043 51 :=
  Tree.join (node174) (node199) (by decide +kernel)
noncomputable def node201 : Tree 1028 2043 102 :=
  Tree.join (node150) (node200) (by decide +kernel)
noncomputable def node202 : Tree 6 2043 204 :=
  Tree.join (node100) (node201) (by decide +kernel)
noncomputable def node203 : Tree 2072 2082 2 :=
  Tree.join (Tree.leaf leaf205) (Tree.leaf leaf206) (by decide +kernel)
noncomputable def node204 : Tree 2049 2082 3 :=
  Tree.join (Tree.leaf leaf204) (node203) (by decide +kernel)
noncomputable def node205 : Tree 2102 2109 2 :=
  Tree.join (Tree.leaf leaf208) (Tree.leaf leaf209) (by decide +kernel)
noncomputable def node206 : Tree 2093 2109 3 :=
  Tree.join (Tree.leaf leaf207) (node205) (by decide +kernel)
noncomputable def node207 : Tree 2049 2109 6 :=
  Tree.join (node204) (node206) (by decide +kernel)
noncomputable def node208 : Tree 2132 2139 2 :=
  Tree.join (Tree.leaf leaf211) (Tree.leaf leaf212) (by decide +kernel)
noncomputable def node209 : Tree 2117 2139 3 :=
  Tree.join (Tree.leaf leaf210) (node208) (by decide +kernel)
noncomputable def node210 : Tree 2155 2163 2 :=
  Tree.join (Tree.leaf leaf214) (Tree.leaf leaf215) (by decide +kernel)
noncomputable def node211 : Tree 2144 2163 3 :=
  Tree.join (Tree.leaf leaf213) (node210) (by decide +kernel)
noncomputable def node212 : Tree 2117 2163 6 :=
  Tree.join (node209) (node211) (by decide +kernel)
noncomputable def node213 : Tree 2049 2163 12 :=
  Tree.join (node207) (node212) (by decide +kernel)
noncomputable def node214 : Tree 2183 2193 2 :=
  Tree.join (Tree.leaf leaf217) (Tree.leaf leaf218) (by decide +kernel)
noncomputable def node215 : Tree 2179 2193 3 :=
  Tree.join (Tree.leaf leaf216) (node214) (by decide +kernel)
noncomputable def node216 : Tree 2220 2224 2 :=
  Tree.join (Tree.leaf leaf220) (Tree.leaf leaf221) (by decide +kernel)
noncomputable def node217 : Tree 2207 2224 3 :=
  Tree.join (Tree.leaf leaf219) (node216) (by decide +kernel)
noncomputable def node218 : Tree 2179 2224 6 :=
  Tree.join (node215) (node217) (by decide +kernel)
noncomputable def node219 : Tree 2248 2254 2 :=
  Tree.join (Tree.leaf leaf223) (Tree.leaf leaf224) (by decide +kernel)
noncomputable def node220 : Tree 2238 2254 3 :=
  Tree.join (Tree.leaf leaf222) (node219) (by decide +kernel)
noncomputable def node221 : Tree 2265 2276 2 :=
  Tree.join (Tree.leaf leaf225) (Tree.leaf leaf226) (by decide +kernel)
noncomputable def node222 : Tree 2286 2296 2 :=
  Tree.join (Tree.leaf leaf227) (Tree.leaf leaf228) (by decide +kernel)
noncomputable def node223 : Tree 2265 2296 4 :=
  Tree.join (node221) (node222) (by decide +kernel)
noncomputable def node224 : Tree 2238 2296 7 :=
  Tree.join (node220) (node223) (by decide +kernel)
noncomputable def node225 : Tree 2179 2296 13 :=
  Tree.join (node218) (node224) (by decide +kernel)
noncomputable def node226 : Tree 2049 2296 25 :=
  Tree.join (node213) (node225) (by decide +kernel)
noncomputable def node227 : Tree 2316 2324 2 :=
  Tree.join (Tree.leaf leaf230) (Tree.leaf leaf231) (by decide +kernel)
noncomputable def node228 : Tree 2298 2324 3 :=
  Tree.join (Tree.leaf leaf229) (node227) (by decide +kernel)
noncomputable def node229 : Tree 2352 2356 2 :=
  Tree.join (Tree.leaf leaf233) (Tree.leaf leaf234) (by decide +kernel)
noncomputable def node230 : Tree 2339 2356 3 :=
  Tree.join (Tree.leaf leaf232) (node229) (by decide +kernel)
noncomputable def node231 : Tree 2298 2356 6 :=
  Tree.join (node228) (node230) (by decide +kernel)
noncomputable def node232 : Tree 2372 2382 2 :=
  Tree.join (Tree.leaf leaf236) (Tree.leaf leaf237) (by decide +kernel)
noncomputable def node233 : Tree 2365 2382 3 :=
  Tree.join (Tree.leaf leaf235) (node232) (by decide +kernel)
noncomputable def node234 : Tree 2397 2409 2 :=
  Tree.join (Tree.leaf leaf238) (Tree.leaf leaf239) (by decide +kernel)
noncomputable def node235 : Tree 2417 2439 2 :=
  Tree.join (Tree.leaf leaf240) (Tree.leaf leaf241) (by decide +kernel)
noncomputable def node236 : Tree 2397 2439 4 :=
  Tree.join (node234) (node235) (by decide +kernel)
noncomputable def node237 : Tree 2365 2439 7 :=
  Tree.join (node233) (node236) (by decide +kernel)
noncomputable def node238 : Tree 2298 2439 13 :=
  Tree.join (node231) (node237) (by decide +kernel)
noncomputable def node239 : Tree 2448 2459 2 :=
  Tree.join (Tree.leaf leaf243) (Tree.leaf leaf244) (by decide +kernel)
noncomputable def node240 : Tree 2443 2459 3 :=
  Tree.join (Tree.leaf leaf242) (node239) (by decide +kernel)
noncomputable def node241 : Tree 2474 2492 2 :=
  Tree.join (Tree.leaf leaf246) (Tree.leaf leaf247) (by decide +kernel)
noncomputable def node242 : Tree 2469 2492 3 :=
  Tree.join (Tree.leaf leaf245) (node241) (by decide +kernel)
noncomputable def node243 : Tree 2443 2492 6 :=
  Tree.join (node240) (node242) (by decide +kernel)
noncomputable def node244 : Tree 2506 2519 2 :=
  Tree.join (Tree.leaf leaf249) (Tree.leaf leaf250) (by decide +kernel)
noncomputable def node245 : Tree 2495 2519 3 :=
  Tree.join (Tree.leaf leaf248) (node244) (by decide +kernel)
noncomputable def node246 : Tree 2524 2533 2 :=
  Tree.join (Tree.leaf leaf251) (Tree.leaf leaf252) (by decide +kernel)
noncomputable def node247 : Tree 2542 2552 2 :=
  Tree.join (Tree.leaf leaf253) (Tree.leaf leaf254) (by decide +kernel)
noncomputable def node248 : Tree 2524 2552 4 :=
  Tree.join (node246) (node247) (by decide +kernel)
noncomputable def node249 : Tree 2495 2552 7 :=
  Tree.join (node245) (node248) (by decide +kernel)
noncomputable def node250 : Tree 2443 2552 13 :=
  Tree.join (node243) (node249) (by decide +kernel)
noncomputable def node251 : Tree 2298 2552 26 :=
  Tree.join (node238) (node250) (by decide +kernel)
noncomputable def node252 : Tree 2049 2552 51 :=
  Tree.join (node226) (node251) (by decide +kernel)
noncomputable def node253 : Tree 2576 2589 2 :=
  Tree.join (Tree.leaf leaf256) (Tree.leaf leaf257) (by decide +kernel)
noncomputable def node254 : Tree 2563 2589 3 :=
  Tree.join (Tree.leaf leaf255) (node253) (by decide +kernel)
noncomputable def node255 : Tree 2599 2616 2 :=
  Tree.join (Tree.leaf leaf259) (Tree.leaf leaf260) (by decide +kernel)
noncomputable def node256 : Tree 2597 2616 3 :=
  Tree.join (Tree.leaf leaf258) (node255) (by decide +kernel)
noncomputable def node257 : Tree 2563 2616 6 :=
  Tree.join (node254) (node256) (by decide +kernel)
noncomputable def node258 : Tree 2634 2653 2 :=
  Tree.join (Tree.leaf leaf262) (Tree.leaf leaf263) (by decide +kernel)
noncomputable def node259 : Tree 2629 2653 3 :=
  Tree.join (Tree.leaf leaf261) (node258) (by decide +kernel)
noncomputable def node260 : Tree 2666 2683 2 :=
  Tree.join (Tree.leaf leaf265) (Tree.leaf leaf266) (by decide +kernel)
noncomputable def node261 : Tree 2659 2683 3 :=
  Tree.join (Tree.leaf leaf264) (node260) (by decide +kernel)
noncomputable def node262 : Tree 2629 2683 6 :=
  Tree.join (node259) (node261) (by decide +kernel)
noncomputable def node263 : Tree 2563 2683 12 :=
  Tree.join (node257) (node262) (by decide +kernel)
noncomputable def node264 : Tree 2697 2708 2 :=
  Tree.join (Tree.leaf leaf268) (Tree.leaf leaf269) (by decide +kernel)
noncomputable def node265 : Tree 2688 2708 3 :=
  Tree.join (Tree.leaf leaf267) (node264) (by decide +kernel)
noncomputable def node266 : Tree 2730 2735 2 :=
  Tree.join (Tree.leaf leaf271) (Tree.leaf leaf272) (by decide +kernel)
noncomputable def node267 : Tree 2720 2735 3 :=
  Tree.join (Tree.leaf leaf270) (node266) (by decide +kernel)
noncomputable def node268 : Tree 2688 2735 6 :=
  Tree.join (node265) (node267) (by decide +kernel)
noncomputable def node269 : Tree 2756 2760 2 :=
  Tree.join (Tree.leaf leaf274) (Tree.leaf leaf275) (by decide +kernel)
noncomputable def node270 : Tree 2754 2760 3 :=
  Tree.join (Tree.leaf leaf273) (node269) (by decide +kernel)
noncomputable def node271 : Tree 2777 2790 2 :=
  Tree.join (Tree.leaf leaf276) (Tree.leaf leaf277) (by decide +kernel)
noncomputable def node272 : Tree 2796 2805 2 :=
  Tree.join (Tree.leaf leaf278) (Tree.leaf leaf279) (by decide +kernel)
noncomputable def node273 : Tree 2777 2805 4 :=
  Tree.join (node271) (node272) (by decide +kernel)
noncomputable def node274 : Tree 2754 2805 7 :=
  Tree.join (node270) (node273) (by decide +kernel)
noncomputable def node275 : Tree 2688 2805 13 :=
  Tree.join (node268) (node274) (by decide +kernel)
noncomputable def node276 : Tree 2563 2805 25 :=
  Tree.join (node263) (node275) (by decide +kernel)
noncomputable def node277 : Tree 2831 2846 2 :=
  Tree.join (Tree.leaf leaf281) (Tree.leaf leaf282) (by decide +kernel)
noncomputable def node278 : Tree 2817 2846 3 :=
  Tree.join (Tree.leaf leaf280) (node277) (by decide +kernel)
noncomputable def node279 : Tree 2857 2861 2 :=
  Tree.join (Tree.leaf leaf284) (Tree.leaf leaf285) (by decide +kernel)
noncomputable def node280 : Tree 2847 2861 3 :=
  Tree.join (Tree.leaf leaf283) (node279) (by decide +kernel)
noncomputable def node281 : Tree 2817 2861 6 :=
  Tree.join (node278) (node280) (by decide +kernel)
noncomputable def node282 : Tree 2880 2894 2 :=
  Tree.join (Tree.leaf leaf287) (Tree.leaf leaf288) (by decide +kernel)
noncomputable def node283 : Tree 2877 2894 3 :=
  Tree.join (Tree.leaf leaf286) (node282) (by decide +kernel)
noncomputable def node284 : Tree 2901 2911 2 :=
  Tree.join (Tree.leaf leaf289) (Tree.leaf leaf290) (by decide +kernel)
noncomputable def node285 : Tree 2928 2934 2 :=
  Tree.join (Tree.leaf leaf291) (Tree.leaf leaf292) (by decide +kernel)
noncomputable def node286 : Tree 2901 2934 4 :=
  Tree.join (node284) (node285) (by decide +kernel)
noncomputable def node287 : Tree 2877 2934 7 :=
  Tree.join (node283) (node286) (by decide +kernel)
noncomputable def node288 : Tree 2817 2934 13 :=
  Tree.join (node281) (node287) (by decide +kernel)
noncomputable def node289 : Tree 2961 2976 2 :=
  Tree.join (Tree.leaf leaf294) (Tree.leaf leaf295) (by decide +kernel)
noncomputable def node290 : Tree 2951 2976 3 :=
  Tree.join (Tree.leaf leaf293) (node289) (by decide +kernel)
noncomputable def node291 : Tree 2986 3001 2 :=
  Tree.join (Tree.leaf leaf297) (Tree.leaf leaf298) (by decide +kernel)
noncomputable def node292 : Tree 2983 3001 3 :=
  Tree.join (Tree.leaf leaf296) (node291) (by decide +kernel)
noncomputable def node293 : Tree 2951 3001 6 :=
  Tree.join (node290) (node292) (by decide +kernel)
noncomputable def node294 : Tree 3019 3031 2 :=
  Tree.join (Tree.leaf leaf300) (Tree.leaf leaf301) (by decide +kernel)
noncomputable def node295 : Tree 3008 3031 3 :=
  Tree.join (Tree.leaf leaf299) (node294) (by decide +kernel)
noncomputable def node296 : Tree 3037 3048 2 :=
  Tree.join (Tree.leaf leaf302) (Tree.leaf leaf303) (by decide +kernel)
noncomputable def node297 : Tree 3058 3069 2 :=
  Tree.join (Tree.leaf leaf304) (Tree.leaf leaf305) (by decide +kernel)
noncomputable def node298 : Tree 3037 3069 4 :=
  Tree.join (node296) (node297) (by decide +kernel)
noncomputable def node299 : Tree 3008 3069 7 :=
  Tree.join (node295) (node298) (by decide +kernel)
noncomputable def node300 : Tree 2951 3069 13 :=
  Tree.join (node293) (node299) (by decide +kernel)
noncomputable def node301 : Tree 2817 3069 26 :=
  Tree.join (node288) (node300) (by decide +kernel)
noncomputable def node302 : Tree 2563 3069 51 :=
  Tree.join (node276) (node301) (by decide +kernel)
noncomputable def node303 : Tree 2049 3069 102 :=
  Tree.join (node252) (node302) (by decide +kernel)
noncomputable def node304 : Tree 3086 3097 2 :=
  Tree.join (Tree.leaf leaf307) (Tree.leaf leaf308) (by decide +kernel)
noncomputable def node305 : Tree 3081 3097 3 :=
  Tree.join (Tree.leaf leaf306) (node304) (by decide +kernel)
noncomputable def node306 : Tree 3116 3125 2 :=
  Tree.join (Tree.leaf leaf310) (Tree.leaf leaf311) (by decide +kernel)
noncomputable def node307 : Tree 3100 3125 3 :=
  Tree.join (Tree.leaf leaf309) (node306) (by decide +kernel)
noncomputable def node308 : Tree 3081 3125 6 :=
  Tree.join (node305) (node307) (by decide +kernel)
noncomputable def node309 : Tree 3145 3157 2 :=
  Tree.join (Tree.leaf leaf313) (Tree.leaf leaf314) (by decide +kernel)
noncomputable def node310 : Tree 3133 3157 3 :=
  Tree.join (Tree.leaf leaf312) (node309) (by decide +kernel)
noncomputable def node311 : Tree 3177 3188 2 :=
  Tree.join (Tree.leaf leaf316) (Tree.leaf leaf317) (by decide +kernel)
noncomputable def node312 : Tree 3168 3188 3 :=
  Tree.join (Tree.leaf leaf315) (node311) (by decide +kernel)
noncomputable def node313 : Tree 3133 3188 6 :=
  Tree.join (node310) (node312) (by decide +kernel)
noncomputable def node314 : Tree 3081 3188 12 :=
  Tree.join (node308) (node313) (by decide +kernel)
noncomputable def node315 : Tree 3204 3215 2 :=
  Tree.join (Tree.leaf leaf319) (Tree.leaf leaf320) (by decide +kernel)
noncomputable def node316 : Tree 3200 3215 3 :=
  Tree.join (Tree.leaf leaf318) (node315) (by decide +kernel)
noncomputable def node317 : Tree 3239 3247 2 :=
  Tree.join (Tree.leaf leaf322) (Tree.leaf leaf323) (by decide +kernel)
noncomputable def node318 : Tree 3236 3247 3 :=
  Tree.join (Tree.leaf leaf321) (node317) (by decide +kernel)
noncomputable def node319 : Tree 3200 3247 6 :=
  Tree.join (node316) (node318) (by decide +kernel)
noncomputable def node320 : Tree 3273 3278 2 :=
  Tree.join (Tree.leaf leaf325) (Tree.leaf leaf326) (by decide +kernel)
noncomputable def node321 : Tree 3256 3278 3 :=
  Tree.join (Tree.leaf leaf324) (node320) (by decide +kernel)
noncomputable def node322 : Tree 3287 3296 2 :=
  Tree.join (Tree.leaf leaf327) (Tree.leaf leaf328) (by decide +kernel)
noncomputable def node323 : Tree 3309 3317 2 :=
  Tree.join (Tree.leaf leaf329) (Tree.leaf leaf330) (by decide +kernel)
noncomputable def node324 : Tree 3287 3317 4 :=
  Tree.join (node322) (node323) (by decide +kernel)
noncomputable def node325 : Tree 3256 3317 7 :=
  Tree.join (node321) (node324) (by decide +kernel)
noncomputable def node326 : Tree 3200 3317 13 :=
  Tree.join (node319) (node325) (by decide +kernel)
noncomputable def node327 : Tree 3081 3317 25 :=
  Tree.join (node314) (node326) (by decide +kernel)
noncomputable def node328 : Tree 3343 3354 2 :=
  Tree.join (Tree.leaf leaf332) (Tree.leaf leaf333) (by decide +kernel)
noncomputable def node329 : Tree 3326 3354 3 :=
  Tree.join (Tree.leaf leaf331) (node328) (by decide +kernel)
noncomputable def node330 : Tree 3372 3378 2 :=
  Tree.join (Tree.leaf leaf335) (Tree.leaf leaf336) (by decide +kernel)
noncomputable def node331 : Tree 3364 3378 3 :=
  Tree.join (Tree.leaf leaf334) (node330) (by decide +kernel)
noncomputable def node332 : Tree 3326 3378 6 :=
  Tree.join (node329) (node331) (by decide +kernel)
noncomputable def node333 : Tree 3395 3401 2 :=
  Tree.join (Tree.leaf leaf338) (Tree.leaf leaf339) (by decide +kernel)
noncomputable def node334 : Tree 3387 3401 3 :=
  Tree.join (Tree.leaf leaf337) (node333) (by decide +kernel)
noncomputable def node335 : Tree 3414 3430 2 :=
  Tree.join (Tree.leaf leaf340) (Tree.leaf leaf341) (by decide +kernel)
noncomputable def node336 : Tree 3436 3449 2 :=
  Tree.join (Tree.leaf leaf342) (Tree.leaf leaf343) (by decide +kernel)
noncomputable def node337 : Tree 3414 3449 4 :=
  Tree.join (node335) (node336) (by decide +kernel)
noncomputable def node338 : Tree 3387 3449 7 :=
  Tree.join (node334) (node337) (by decide +kernel)
noncomputable def node339 : Tree 3326 3449 13 :=
  Tree.join (node332) (node338) (by decide +kernel)
noncomputable def node340 : Tree 3462 3474 2 :=
  Tree.join (Tree.leaf leaf345) (Tree.leaf leaf346) (by decide +kernel)
noncomputable def node341 : Tree 3457 3474 3 :=
  Tree.join (Tree.leaf leaf344) (node340) (by decide +kernel)
noncomputable def node342 : Tree 3493 3510 2 :=
  Tree.join (Tree.leaf leaf348) (Tree.leaf leaf349) (by decide +kernel)
noncomputable def node343 : Tree 3485 3510 3 :=
  Tree.join (Tree.leaf leaf347) (node342) (by decide +kernel)
noncomputable def node344 : Tree 3457 3510 6 :=
  Tree.join (node341) (node343) (by decide +kernel)
noncomputable def node345 : Tree 3525 3541 2 :=
  Tree.join (Tree.leaf leaf351) (Tree.leaf leaf352) (by decide +kernel)
noncomputable def node346 : Tree 3521 3541 3 :=
  Tree.join (Tree.leaf leaf350) (node345) (by decide +kernel)
noncomputable def node347 : Tree 3553 3563 2 :=
  Tree.join (Tree.leaf leaf353) (Tree.leaf leaf354) (by decide +kernel)
noncomputable def node348 : Tree 3574 3585 2 :=
  Tree.join (Tree.leaf leaf355) (Tree.leaf leaf356) (by decide +kernel)
noncomputable def node349 : Tree 3553 3585 4 :=
  Tree.join (node347) (node348) (by decide +kernel)
noncomputable def node350 : Tree 3521 3585 7 :=
  Tree.join (node346) (node349) (by decide +kernel)
noncomputable def node351 : Tree 3457 3585 13 :=
  Tree.join (node344) (node350) (by decide +kernel)
noncomputable def node352 : Tree 3326 3585 26 :=
  Tree.join (node339) (node351) (by decide +kernel)
noncomputable def node353 : Tree 3081 3585 51 :=
  Tree.join (node327) (node352) (by decide +kernel)
noncomputable def node354 : Tree 3596 3613 2 :=
  Tree.join (Tree.leaf leaf358) (Tree.leaf leaf359) (by decide +kernel)
noncomputable def node355 : Tree 3594 3613 3 :=
  Tree.join (Tree.leaf leaf357) (node354) (by decide +kernel)
noncomputable def node356 : Tree 3627 3633 2 :=
  Tree.join (Tree.leaf leaf361) (Tree.leaf leaf362) (by decide +kernel)
noncomputable def node357 : Tree 3619 3633 3 :=
  Tree.join (Tree.leaf leaf360) (node356) (by decide +kernel)
noncomputable def node358 : Tree 3594 3633 6 :=
  Tree.join (node355) (node357) (by decide +kernel)
noncomputable def node359 : Tree 3660 3668 2 :=
  Tree.join (Tree.leaf leaf364) (Tree.leaf leaf365) (by decide +kernel)
noncomputable def node360 : Tree 3640 3668 3 :=
  Tree.join (Tree.leaf leaf363) (node359) (by decide +kernel)
noncomputable def node361 : Tree 3689 3702 2 :=
  Tree.join (Tree.leaf leaf367) (Tree.leaf leaf368) (by decide +kernel)
noncomputable def node362 : Tree 3676 3702 3 :=
  Tree.join (Tree.leaf leaf366) (node361) (by decide +kernel)
noncomputable def node363 : Tree 3640 3702 6 :=
  Tree.join (node360) (node362) (by decide +kernel)
noncomputable def node364 : Tree 3594 3702 12 :=
  Tree.join (node358) (node363) (by decide +kernel)
noncomputable def node365 : Tree 3722 3724 2 :=
  Tree.join (Tree.leaf leaf370) (Tree.leaf leaf371) (by decide +kernel)
noncomputable def node366 : Tree 3707 3724 3 :=
  Tree.join (Tree.leaf leaf369) (node365) (by decide +kernel)
noncomputable def node367 : Tree 3747 3759 2 :=
  Tree.join (Tree.leaf leaf373) (Tree.leaf leaf374) (by decide +kernel)
noncomputable def node368 : Tree 3739 3759 3 :=
  Tree.join (Tree.leaf leaf372) (node367) (by decide +kernel)
noncomputable def node369 : Tree 3707 3759 6 :=
  Tree.join (node366) (node368) (by decide +kernel)
noncomputable def node370 : Tree 3780 3789 2 :=
  Tree.join (Tree.leaf leaf376) (Tree.leaf leaf377) (by decide +kernel)
noncomputable def node371 : Tree 3762 3789 3 :=
  Tree.join (Tree.leaf leaf375) (node370) (by decide +kernel)
noncomputable def node372 : Tree 3795 3808 2 :=
  Tree.join (Tree.leaf leaf378) (Tree.leaf leaf379) (by decide +kernel)
noncomputable def node373 : Tree 3816 3827 2 :=
  Tree.join (Tree.leaf leaf380) (Tree.leaf leaf381) (by decide +kernel)
noncomputable def node374 : Tree 3795 3827 4 :=
  Tree.join (node372) (node373) (by decide +kernel)
noncomputable def node375 : Tree 3762 3827 7 :=
  Tree.join (node371) (node374) (by decide +kernel)
noncomputable def node376 : Tree 3707 3827 13 :=
  Tree.join (node369) (node375) (by decide +kernel)
noncomputable def node377 : Tree 3594 3827 25 :=
  Tree.join (node364) (node376) (by decide +kernel)
noncomputable def node378 : Tree 3852 3860 2 :=
  Tree.join (Tree.leaf leaf383) (Tree.leaf leaf384) (by decide +kernel)
noncomputable def node379 : Tree 3846 3860 3 :=
  Tree.join (Tree.leaf leaf382) (node378) (by decide +kernel)
noncomputable def node380 : Tree 3878 3889 2 :=
  Tree.join (Tree.leaf leaf386) (Tree.leaf leaf387) (by decide +kernel)
noncomputable def node381 : Tree 3871 3889 3 :=
  Tree.join (Tree.leaf leaf385) (node380) (by decide +kernel)
noncomputable def node382 : Tree 3846 3889 6 :=
  Tree.join (node379) (node381) (by decide +kernel)
noncomputable def node383 : Tree 3910 3925 2 :=
  Tree.join (Tree.leaf leaf389) (Tree.leaf leaf390) (by decide +kernel)
noncomputable def node384 : Tree 3901 3925 3 :=
  Tree.join (Tree.leaf leaf388) (node383) (by decide +kernel)
noncomputable def node385 : Tree 3931 3939 2 :=
  Tree.join (Tree.leaf leaf391) (Tree.leaf leaf392) (by decide +kernel)
noncomputable def node386 : Tree 3948 3964 2 :=
  Tree.join (Tree.leaf leaf393) (Tree.leaf leaf394) (by decide +kernel)
noncomputable def node387 : Tree 3931 3964 4 :=
  Tree.join (node385) (node386) (by decide +kernel)
noncomputable def node388 : Tree 3901 3964 7 :=
  Tree.join (node384) (node387) (by decide +kernel)
noncomputable def node389 : Tree 3846 3964 13 :=
  Tree.join (node382) (node388) (by decide +kernel)
noncomputable def node390 : Tree 3977 3990 2 :=
  Tree.join (Tree.leaf leaf396) (Tree.leaf leaf397) (by decide +kernel)
noncomputable def node391 : Tree 3966 3990 3 :=
  Tree.join (Tree.leaf leaf395) (node390) (by decide +kernel)
noncomputable def node392 : Tree 4007 4017 2 :=
  Tree.join (Tree.leaf leaf399) (Tree.leaf leaf400) (by decide +kernel)
noncomputable def node393 : Tree 3999 4017 3 :=
  Tree.join (Tree.leaf leaf398) (node392) (by decide +kernel)
noncomputable def node394 : Tree 3966 4017 6 :=
  Tree.join (node391) (node393) (by decide +kernel)
noncomputable def node395 : Tree 4030 4039 2 :=
  Tree.join (Tree.leaf leaf402) (Tree.leaf leaf403) (by decide +kernel)
noncomputable def node396 : Tree 4022 4039 3 :=
  Tree.join (Tree.leaf leaf401) (node395) (by decide +kernel)
noncomputable def node397 : Tree 4059 4076 2 :=
  Tree.join (Tree.leaf leaf404) (Tree.leaf leaf405) (by decide +kernel)
noncomputable def node398 : Tree 4077 4094 2 :=
  Tree.join (Tree.leaf leaf406) (Tree.leaf leaf407) (by decide +kernel)
noncomputable def node399 : Tree 4059 4094 4 :=
  Tree.join (node397) (node398) (by decide +kernel)
noncomputable def node400 : Tree 4022 4094 7 :=
  Tree.join (node396) (node399) (by decide +kernel)
noncomputable def node401 : Tree 3966 4094 13 :=
  Tree.join (node394) (node400) (by decide +kernel)
noncomputable def node402 : Tree 3846 4094 26 :=
  Tree.join (node389) (node401) (by decide +kernel)
noncomputable def node403 : Tree 3594 4094 51 :=
  Tree.join (node377) (node402) (by decide +kernel)
noncomputable def node404 : Tree 3081 4094 102 :=
  Tree.join (node353) (node403) (by decide +kernel)
noncomputable def node405 : Tree 2049 4094 204 :=
  Tree.join (node303) (node404) (by decide +kernel)
noncomputable def node406 : Tree 6 4094 408 :=
  Tree.join (node202) (node405) (by decide +kernel)
noncomputable def certificate : Tree 6 4094 408 := node406
end RHBatch02HeightBracketData
noncomputable def TaoFivePrimes_RHBatch02HeightBracketTree := RHBatch02HeightBracketData.certificate


