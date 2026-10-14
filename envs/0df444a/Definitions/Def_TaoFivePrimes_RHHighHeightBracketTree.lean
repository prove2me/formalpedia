-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighHeightBracketTree
-- name    : TaoFivePrimes_RHHighHeightBracketTree
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T10:15:10.77515+00:00
-- url     : https://prove2.me/theorems/cc54ae5d-33bd-4c71-849f-3fedf5dc9cf8
-- title:
--   TaoFivePrimes_RHHighHeightBracketTree
-- statement:
--   An ordered tree of 409 proposed sign brackets from a 1/32-spaced high-height grid. Each leaf carries ordinary proofs of coordinate bounds, interval ordering and opposite strict signs of its proposed dyadic boxes. Each join carries a proof that its subtrees are ordered. These certificates assert no containment of normalized zeta values.
-- source:
--   Finite structural sign and order certificates, generated from the native FLINT 3.6.0 Platt FFT/interpolation proposal on [3289999872,3290000000]. Numeric tests are necessary constructor proof fields and use ordinary decide +kernel. No value containment, total zero count or RH conclusion is asserted. Platt method: DOI 10.1090/mcom/3198. The surrounding project preserves attribution to sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham.

/- Structural certificates for proposed high-height sign brackets.
Every finite sign/order test is a necessary proof field checked in ordinary Lean.
Containment of mathematical zeta values is NOT asserted by these records.
Numerical proposals: Platt/FLINT. Surrounding xi/theta work: sometik179 and
Gabewhigham. -/
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace RHHighHeightBracketData
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
  ⟨6, 7, (Int.ofNat 164065789351914712), (Int.ofNat 164065789351914727), (Int.negSucc 60733384172761460), (Int.negSucc 60733384172761447),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf1 : Bracket :=
  ⟨20, 21, (Int.negSucc 2033362201154685), (Int.negSucc 2033362201154678), (Int.ofNat 56842001198223904), (Int.ofNat 56842001198223914),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf2 : Bracket :=
  ⟨25, 26, (Int.ofNat 39907622561627588), (Int.ofNat 39907622561627603), (Int.negSucc 5659374192335703), (Int.negSucc 5659374192335692),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf3 : Bracket :=
  ⟨35, 36, (Int.negSucc 8330806619358518), (Int.negSucc 8330806619358510), (Int.ofNat 40325333561982019), (Int.ofNat 40325333561982023),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf4 : Bracket :=
  ⟨43, 44, (Int.ofNat 36953031990428950), (Int.ofNat 36953031990428970), (Int.negSucc 12730893006029766), (Int.negSucc 12730893006029756),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf5 : Bracket :=
  ⟨53, 54, (Int.negSucc 7238922048008458), (Int.negSucc 7238922048008440), (Int.ofNat 50280565901684344), (Int.ofNat 50280565901684355),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf6 : Bracket :=
  ⟨63, 64, (Int.ofNat 4002349325116783), (Int.ofNat 4002349325116790), (Int.negSucc 51364149593091171), (Int.negSucc 51364149593091168),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf7 : Bracket :=
  ⟨71, 72, (Int.negSucc 26218127285749070), (Int.negSucc 26218127285749061), (Int.ofNat 27499803906182995), (Int.ofNat 27499803906183005),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf8 : Bracket :=
  ⟨77, 78, (Int.ofNat 34170139045687546), (Int.ofNat 34170139045687555), (Int.negSucc 63141528980439185), (Int.negSucc 63141528980439166),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf9 : Bracket :=
  ⟨94, 95, (Int.negSucc 78570446580755216), (Int.negSucc 78570446580755202), (Int.ofNat 240054098384223437), (Int.ofNat 240054098384223450),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf10 : Bracket :=
  ⟨110, 111, (Int.ofNat 58212255655628829), (Int.ofNat 58212255655628848), (Int.negSucc 49912513323442596), (Int.negSucc 49912513323442581),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf11 : Bracket :=
  ⟨118, 119, (Int.negSucc 14388729568201708), (Int.negSucc 14388729568201689), (Int.ofNat 28296987283137965), (Int.ofNat 28296987283137973),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf12 : Bracket :=
  ⟨125, 126, (Int.ofNat 609868618130618), (Int.ofNat 609868618130631), (Int.negSucc 38671923964199899), (Int.negSucc 38671923964199889),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf13 : Bracket :=
  ⟨135, 136, (Int.negSucc 18169425083112309), (Int.negSucc 18169425083112295), (Int.ofNat 17257731152724382), (Int.ofNat 17257731152724386),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf14 : Bracket :=
  ⟨143, 144, (Int.ofNat 1167707333099940), (Int.ofNat 1167707333099952), (Int.negSucc 31986210400133786), (Int.negSucc 31986210400133782),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf15 : Bracket :=
  ⟨151, 152, (Int.negSucc 26240112648274001), (Int.negSucc 26240112648273988), (Int.ofNat 19895682781373842), (Int.ofNat 19895682781373854),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf16 : Bracket :=
  ⟨164, 165, (Int.ofNat 31619082053885968), (Int.ofNat 31619082053885981), (Int.negSucc 7148777845011915), (Int.negSucc 7148777845011900),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf17 : Bracket :=
  ⟨170, 171, (Int.negSucc 22686457539523142), (Int.negSucc 22686457539523131), (Int.ofNat 7130737489174622), (Int.ofNat 7130737489174637),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf18 : Bracket :=
  ⟨179, 180, (Int.ofNat 18390997006390837), (Int.ofNat 18390997006390845), (Int.negSucc 38607093436955750), (Int.negSucc 38607093436955741),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf19 : Bracket :=
  ⟨193, 194, (Int.negSucc 30881432295056840), (Int.negSucc 30881432295056832), (Int.ofNat 9844160519773249), (Int.ofNat 9844160519773265),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf20 : Bracket :=
  ⟨198, 199, (Int.ofNat 19479001470896522), (Int.ofNat 19479001470896539), (Int.negSucc 7574495118824164), (Int.negSucc 7574495118824146),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf21 : Bracket :=
  ⟨204, 205, (Int.negSucc 11435096439399671), (Int.negSucc 11435096439399664), (Int.ofNat 56223434626482815), (Int.ofNat 56223434626482833),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf22 : Bracket :=
  ⟨218, 219, (Int.ofNat 37431706394453018), (Int.ofNat 37431706394453032), (Int.negSucc 272705447671306375), (Int.negSucc 272705447671306361),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf23 : Bracket :=
  ⟨231, 232, (Int.negSucc 206552138075516955), (Int.negSucc 206552138075516935), (Int.ofNat 157327651331005568), (Int.ofNat 157327651331005575),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf24 : Bracket :=
  ⟨239, 240, (Int.ofNat 65598659183592681), (Int.ofNat 65598659183592694), (Int.negSucc 468864845608482477), (Int.negSucc 468864845608482474),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf25 : Bracket :=
  ⟨259, 260, (Int.negSucc 225981353596961704), (Int.negSucc 225981353596961690), (Int.ofNat 103838743467991100), (Int.ofNat 103838743467991103),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf26 : Bracket :=
  ⟨264, 265, (Int.ofNat 128399315000792769), (Int.ofNat 128399315000792780), (Int.negSucc 125991390101200366), (Int.negSucc 125991390101200350),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf27 : Bracket :=
  ⟨281, 282, (Int.negSucc 119535608811838869), (Int.negSucc 119535608811838857), (Int.ofNat 34130398958981441), (Int.ofNat 34130398958981461),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf28 : Bracket :=
  ⟨288, 289, (Int.ofNat 16720101583577598), (Int.ofNat 16720101583577601), (Int.negSucc 59757641614731969), (Int.negSucc 59757641614731958),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf29 : Bracket :=
  ⟨296, 297, (Int.negSucc 52414886702994711), (Int.negSucc 52414886702994699), (Int.ofNat 18459990007932745), (Int.ofNat 18459990007932763),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf30 : Bracket :=
  ⟨306, 307, (Int.ofNat 22896613100851141), (Int.ofNat 22896613100851154), (Int.negSucc 36342490852606686), (Int.negSucc 36342490852606670),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf31 : Bracket :=
  ⟨313, 314, (Int.negSucc 29398403040362334), (Int.negSucc 29398403040362314), (Int.ofNat 40864543195690383), (Int.ofNat 40864543195690393),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf32 : Bracket :=
  ⟨324, 325, (Int.ofNat 92255538437420095), (Int.ofNat 92255538437420108), (Int.negSucc 14888878223785294), (Int.negSucc 14888878223785277),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf33 : Bracket :=
  ⟨335, 336, (Int.negSucc 47929227951151739), (Int.negSucc 47929227951151720), (Int.ofNat 73877615149020484), (Int.ofNat 73877615149020498),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf34 : Bracket :=
  ⟨349, 350, (Int.ofNat 55292324714238140), (Int.ofNat 55292324714238151), (Int.negSucc 4314263124099765), (Int.negSucc 4314263124099746),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf35 : Bracket :=
  ⟨356, 357, (Int.negSucc 12346378895201973), (Int.negSucc 12346378895201967), (Int.ofNat 19627458137759545), (Int.ofNat 19627458137759565),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf36 : Bracket :=
  ⟨364, 365, (Int.ofNat 19457996083894995), (Int.ofNat 19457996083895006), (Int.negSucc 14348400415181615), (Int.negSucc 14348400415181601),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf37 : Bracket :=
  ⟨375, 376, (Int.negSucc 10705178754486286), (Int.negSucc 10705178754486278), (Int.ofNat 12283302799747843), (Int.ofNat 12283302799747847),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf38 : Bracket :=
  ⟨380, 381, (Int.ofNat 13714861120733397), (Int.ofNat 13714861120733409), (Int.negSucc 9783323747613148), (Int.negSucc 9783323747613133),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf39 : Bracket :=
  ⟨390, 391, (Int.negSucc 22784927229720010), (Int.negSucc 22784927229719990), (Int.ofNat 30071585808772006), (Int.ofNat 30071585808772025),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf40 : Bracket :=
  ⟨399, 400, (Int.ofNat 78984085278692911), (Int.ofNat 78984085278692929), (Int.negSucc 7216851601703298), (Int.negSucc 7216851601703291),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf41 : Bracket :=
  ⟨412, 413, (Int.negSucc 5637071629029357), (Int.negSucc 5637071629029346), (Int.ofNat 158723107394089721), (Int.ofNat 158723107394089732),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf42 : Bracket :=
  ⟨427, 428, (Int.ofNat 49119255387317166), (Int.ofNat 49119255387317183), (Int.negSucc 24132847155931641), (Int.negSucc 24132847155931632),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf43 : Bracket :=
  ⟨433, 434, (Int.negSucc 13069034773424703), (Int.negSucc 13069034773424686), (Int.ofNat 35028365897039556), (Int.ofNat 35028365897039570),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf44 : Bracket :=
  ⟨440, 441, (Int.ofNat 55442657298303285), (Int.ofNat 55442657298303299), (Int.negSucc 15243867794497601), (Int.negSucc 15243867794497589),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf45 : Bracket :=
  ⟨455, 456, (Int.negSucc 44780771264256927), (Int.negSucc 44780771264256913), (Int.ofNat 24091294549791389), (Int.ofNat 24091294549791397),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf46 : Bracket :=
  ⟨461, 462, (Int.ofNat 18642489663406714), (Int.ofNat 18642489663406730), (Int.negSucc 41325813033203475), (Int.negSucc 41325813033203458),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf47 : Bracket :=
  ⟨472, 473, (Int.negSucc 21332879067105491), (Int.negSucc 21332879067105479), (Int.ofNat 39012300100737098), (Int.ofNat 39012300100737111),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf48 : Bracket :=
  ⟨476, 477, (Int.ofNat 61145631370679525), (Int.ofNat 61145631370679534), (Int.negSucc 11324374857827938), (Int.negSucc 11324374857827921),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf49 : Bracket :=
  ⟨496, 497, (Int.negSucc 61187075070077560), (Int.negSucc 61187075070077557), (Int.ofNat 165955867414049129), (Int.ofNat 165955867414049136),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf50 : Bracket :=
  ⟨506, 507, (Int.ofNat 57469652746412405), (Int.ofNat 57469652746412421), (Int.negSucc 44001810073527641), (Int.negSucc 44001810073527629),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf51 : Bracket :=
  ⟨512, 513, (Int.negSucc 18510225116774676), (Int.negSucc 18510225116774673), (Int.ofNat 91801225587129607), (Int.ofNat 91801225587129616),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf52 : Bracket :=
  ⟨527, 528, (Int.ofNat 10599877189317801), (Int.ofNat 10599877189317819), (Int.negSucc 69853060101505918), (Int.negSucc 69853060101505915),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf53 : Bracket :=
  ⟨534, 535, (Int.negSucc 16289957386724317), (Int.negSucc 16289957386724306), (Int.ofNat 22389415584486755), (Int.ofNat 22389415584486773),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf54 : Bracket :=
  ⟨537, 538, (Int.ofNat 31401012342779540), (Int.ofNat 31401012342779548), (Int.negSucc 15347661809690868), (Int.negSucc 15347661809690853),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf55 : Bracket :=
  ⟨557, 558, (Int.negSucc 30486726641495209), (Int.negSucc 30486726641495195), (Int.ofNat 178825874774153956), (Int.ofNat 178825874774153976),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf56 : Bracket :=
  ⟨569, 570, (Int.ofNat 311342812716150), (Int.ofNat 311342812716163), (Int.negSucc 53338184654081433), (Int.negSucc 53338184654081420),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf57 : Bracket :=
  ⟨575, 576, (Int.negSucc 4914138627229901), (Int.negSucc 4914138627229882), (Int.ofNat 28588446243242706), (Int.ofNat 28588446243242709),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf58 : Bracket :=
  ⟨580, 581, (Int.ofNat 19462102638299586), (Int.ofNat 19462102638299593), (Int.negSucc 27799242423869620), (Int.negSucc 27799242423869604),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf59 : Bracket :=
  ⟨589, 590, (Int.negSucc 84501491596530337), (Int.negSucc 84501491596530328), (Int.ofNat 46936818190391282), (Int.ofNat 46936818190391303),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf60 : Bracket :=
  ⟨601, 602, (Int.ofNat 177431081515815275), (Int.ofNat 177431081515815293), (Int.negSucc 198860207949291623), (Int.negSucc 198860207949291613),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf61 : Bracket :=
  ⟨624, 625, (Int.negSucc 5670249735954450), (Int.negSucc 5670249735954438), (Int.ofNat 34120955515393691), (Int.ofNat 34120955515393703),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf62 : Bracket :=
  ⟨627, 628, (Int.ofNat 11107295384396842), (Int.ofNat 11107295384396855), (Int.negSucc 24916955076802710), (Int.negSucc 24916955076802695),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf63 : Bracket :=
  ⟨632, 633, (Int.negSucc 51189598206465799), (Int.negSucc 51189598206465789), (Int.ofNat 5909438027332149), (Int.ofNat 5909438027332160),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf64 : Bracket :=
  ⟨647, 648, (Int.ofNat 40503434245360461), (Int.ofNat 40503434245360474), (Int.negSucc 131297745100511314), (Int.negSucc 131297745100511310),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf65 : Bracket :=
  ⟨663, 664, (Int.negSucc 34950739167923267), (Int.negSucc 34950739167923254), (Int.ofNat 1208580958500765), (Int.ofNat 1208580958500777),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf66 : Bracket :=
  ⟨668, 669, (Int.ofNat 5436206210172777), (Int.ofNat 5436206210172787), (Int.negSucc 10298235856066273), (Int.negSucc 10298235856066259),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf67 : Bracket :=
  ⟨675, 676, (Int.negSucc 14729170800880306), (Int.negSucc 14729170800880286), (Int.ofNat 309652965310265), (Int.ofNat 309652965310270),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf68 : Bracket :=
  ⟨682, 683, (Int.ofNat 2088711768551494), (Int.ofNat 2088711768551513), (Int.negSucc 19723323922064245), (Int.negSucc 19723323922064224),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf69 : Bracket :=
  ⟨692, 693, (Int.negSucc 19656213402241799), (Int.negSucc 19656213402241789), (Int.ofNat 19681676992887280), (Int.ofNat 19681676992887300),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf70 : Bracket :=
  ⟨702, 703, (Int.ofNat 5978717209229105), (Int.ofNat 5978717209229121), (Int.negSucc 49437786694625159), (Int.negSucc 49437786694625143),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf71 : Bracket :=
  ⟨713, 714, (Int.negSucc 29357665875162968), (Int.negSucc 29357665875162947), (Int.ofNat 29060565504205390), (Int.ofNat 29060565504205405),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf72 : Bracket :=
  ⟨722, 723, (Int.ofNat 12582739452584393), (Int.ofNat 12582739452584409), (Int.negSucc 42038740686377158), (Int.negSucc 42038740686377140),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf73 : Bracket :=
  ⟨730, 731, (Int.negSucc 11514159503662115), (Int.negSucc 11514159503662095), (Int.ofNat 74133417281004157), (Int.ofNat 74133417281004169),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf74 : Bracket :=
  ⟨743, 744, (Int.ofNat 52360756949582487), (Int.ofNat 52360756949582500), (Int.negSucc 73262498741625532), (Int.negSucc 73262498741625517),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf75 : Bracket :=
  ⟨754, 755, (Int.negSucc 52786711364420180), (Int.negSucc 52786711364420165), (Int.ofNat 43643991303401789), (Int.ofNat 43643991303401797),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf76 : Bracket :=
  ⟨764, 765, (Int.ofNat 34954235431848203), (Int.ofNat 34954235431848207), (Int.negSucc 22265013284402309), (Int.negSucc 22265013284402297),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf77 : Bracket :=
  ⟨770, 771, (Int.negSucc 33438284784479996), (Int.negSucc 33438284784479980), (Int.ofNat 24852362535845546), (Int.ofNat 24852362535845562),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf78 : Bracket :=
  ⟨782, 783, (Int.ofNat 10799040957971124), (Int.ofNat 10799040957971136), (Int.negSucc 77613117265267505), (Int.negSucc 77613117265267486),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf79 : Bracket :=
  ⟨790, 791, (Int.negSucc 17082208907689884), (Int.negSucc 17082208907689873), (Int.ofNat 95485762716582230), (Int.ofNat 95485762716582243),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf80 : Bracket :=
  ⟨801, 802, (Int.ofNat 38902887355044119), (Int.ofNat 38902887355044129), (Int.negSucc 96456219965951912), (Int.negSucc 96456219965951902),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf81 : Bracket :=
  ⟨807, 808, (Int.negSucc 141015039964550801), (Int.negSucc 141015039964550781), (Int.ofNat 47786273969418085), (Int.ofNat 47786273969418088),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf82 : Bracket :=
  ⟨821, 822, (Int.ofNat 125074034802022306), (Int.ofNat 125074034802022318), (Int.negSucc 618070320558012643), (Int.negSucc 618070320558012626),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf83 : Bracket :=
  ⟨840, 841, (Int.negSucc 292703359063386517), (Int.negSucc 292703359063386502), (Int.ofNat 177101208861937794), (Int.ofNat 177101208861937803),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf84 : Bracket :=
  ⟨850, 851, (Int.ofNat 70140051004424866), (Int.ofNat 70140051004424877), (Int.negSucc 81238018495500127), (Int.negSucc 81238018495500113),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf85 : Bracket :=
  ⟨856, 857, (Int.negSucc 38501996358665307), (Int.negSucc 38501996358665302), (Int.ofNat 106021859560101627), (Int.ofNat 106021859560101642),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf86 : Bracket :=
  ⟨868, 869, (Int.ofNat 175270835148910948), (Int.ofNat 175270835148910963), (Int.negSucc 886014831382741), (Int.negSucc 886014831382733),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf87 : Bracket :=
  ⟨882, 883, (Int.negSucc 9464438316313923), (Int.negSucc 9464438316313908), (Int.ofNat 41288083367407321), (Int.ofNat 41288083367407340),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf88 : Bracket :=
  ⟨889, 890, (Int.ofNat 13829034980860483), (Int.ofNat 13829034980860496), (Int.negSucc 3119107894579926), (Int.negSucc 3119107894579915),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf89 : Bracket :=
  ⟨892, 893, (Int.negSucc 3393544511216682), (Int.negSucc 3393544511216669), (Int.ofNat 17030604272039685), (Int.ofNat 17030604272039700),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf90 : Bracket :=
  ⟨907, 908, (Int.ofNat 45658609738587783), (Int.ofNat 45658609738587797), (Int.negSucc 1958824252483708), (Int.negSucc 1958824252483694),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf91 : Bracket :=
  ⟨912, 913, (Int.negSucc 34072573420453834), (Int.negSucc 34072573420453819), (Int.ofNat 2916744583539492), (Int.ofNat 2916744583539501),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf92 : Bracket :=
  ⟨927, 928, (Int.ofNat 11084185468570558), (Int.ofNat 11084185468570573), (Int.negSucc 42713832134535408), (Int.negSucc 42713832134535405),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf93 : Bracket :=
  ⟨934, 935, (Int.negSucc 28474195235213081), (Int.negSucc 28474195235213068), (Int.ofNat 17887983366789094), (Int.ofNat 17887983366789105),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf94 : Bracket :=
  ⟨945, 946, (Int.ofNat 13482005286794453), (Int.ofNat 13482005286794471), (Int.negSucc 23484565778690742), (Int.negSucc 23484565778690725),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf95 : Bracket :=
  ⟨951, 952, (Int.negSucc 13170089169296696), (Int.negSucc 13170089169296682), (Int.ofNat 30295962623353039), (Int.ofNat 30295962623353043),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf96 : Bracket :=
  ⟨961, 962, (Int.ofNat 61476887185636440), (Int.ofNat 61476887185636448), (Int.negSucc 17243271743138470), (Int.negSucc 17243271743138456),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf97 : Bracket :=
  ⟨970, 971, (Int.negSucc 39828413522709748), (Int.negSucc 39828413522709738), (Int.ofNat 113148028544785524), (Int.ofNat 113148028544785533),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf98 : Bracket :=
  ⟨990, 991, (Int.ofNat 43279864024216824), (Int.ofNat 43279864024216835), (Int.negSucc 17376414459681944), (Int.negSucc 17376414459681927),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf99 : Bracket :=
  ⟨993, 994, (Int.negSucc 33515250195610716), (Int.negSucc 33515250195610698), (Int.ofNat 316840876136863), (Int.ofNat 316840876136873),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf100 : Bracket :=
  ⟨1003, 1004, (Int.ofNat 68531525712408019), (Int.ofNat 68531525712408026), (Int.negSucc 22731082445534195), (Int.negSucc 22731082445534190),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf101 : Bracket :=
  ⟨1015, 1016, (Int.negSucc 86131531678395997), (Int.negSucc 86131531678395987), (Int.ofNat 17161868351458652), (Int.ofNat 17161868351458655),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf102 : Bracket :=
  ⟨1026, 1027, (Int.ofNat 37028973902927878), (Int.ofNat 37028973902927896), (Int.negSucc 9920660007970794), (Int.negSucc 9920660007970777),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf103 : Bracket :=
  ⟨1030, 1031, (Int.negSucc 4893207566919980), (Int.negSucc 4893207566919971), (Int.ofNat 57565095586750076), (Int.ofNat 57565095586750089),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf104 : Bracket :=
  ⟨1053, 1054, (Int.ofNat 16615580493119174), (Int.ofNat 16615580493119182), (Int.negSucc 799379634804278), (Int.negSucc 799379634804268),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf105 : Bracket :=
  ⟨1055, 1056, (Int.negSucc 4664556872339192), (Int.negSucc 4664556872339177), (Int.ofNat 282147859198073), (Int.ofNat 282147859198077),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf106 : Bracket :=
  ⟨1062, 1063, (Int.ofNat 1079921421220854), (Int.ofNat 1079921421220873), (Int.negSucc 14488341833888556), (Int.negSucc 14488341833888550),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf107 : Bracket :=
  ⟨1068, 1069, (Int.negSucc 17850584047754158), (Int.negSucc 17850584047754145), (Int.ofNat 13760003799911616), (Int.ofNat 13760003799911633),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf108 : Bracket :=
  ⟨1082, 1083, (Int.ofNat 16683562366757454), (Int.ofNat 16683562366757473), (Int.negSucc 44811138310198422), (Int.negSucc 44811138310198412),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf109 : Bracket :=
  ⟨1087, 1088, (Int.negSucc 57655826511544356), (Int.negSucc 57655826511544349), (Int.ofNat 17378889885442986), (Int.ofNat 17378889885442989),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf110 : Bracket :=
  ⟨1100, 1101, (Int.ofNat 127145859787050581), (Int.ofNat 127145859787050591), (Int.negSucc 141853279401908720), (Int.negSucc 141853279401908713),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf111 : Bracket :=
  ⟨1112, 1113, (Int.negSucc 278055236101285111), (Int.negSucc 278055236101285108), (Int.ofNat 134610617487507828), (Int.ofNat 134610617487507840),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf112 : Bracket :=
  ⟨1129, 1130, (Int.ofNat 796265918755291), (Int.ofNat 796265918755300), (Int.negSucc 100390230331011819), (Int.negSucc 100390230331011802),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf113 : Bracket :=
  ⟨1132, 1133, (Int.negSucc 45652193486158841), (Int.negSucc 45652193486158836), (Int.ofNat 100801304997655495), (Int.ofNat 100801304997655513),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf114 : Bracket :=
  ⟨1149, 1150, (Int.ofNat 43815185879092040), (Int.ofNat 43815185879092055), (Int.negSucc 172407073693549274), (Int.negSucc 172407073693549267),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf115 : Bracket :=
  ⟨1159, 1160, (Int.negSucc 57124690325619632), (Int.negSucc 57124690325619615), (Int.ofNat 6580146189979571), (Int.ofNat 6580146189979575),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf116 : Bracket :=
  ⟨1162, 1163, (Int.ofNat 28168864100392047), (Int.ofNat 28168864100392063), (Int.negSucc 16929812921683358), (Int.negSucc 16929812921683346),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf117 : Bracket :=
  ⟨1173, 1174, (Int.negSucc 99934792949556504), (Int.negSucc 99934792949556489), (Int.ofNat 144115792219797880), (Int.ofNat 144115792219797898),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf118 : Bracket :=
  ⟨1194, 1195, (Int.ofNat 42324402445433486), (Int.ofNat 42324402445433499), (Int.negSucc 56173123065433032), (Int.negSucc 56173123065433013),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf119 : Bracket :=
  ⟨1202, 1203, (Int.negSucc 5458923193876227), (Int.negSucc 5458923193876215), (Int.ofNat 16658232145663667), (Int.ofNat 16658232145663683),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf120 : Bracket :=
  ⟨1206, 1207, (Int.ofNat 12426476400794261), (Int.ofNat 12426476400794277), (Int.negSucc 6682997277473608), (Int.negSucc 6682997277473599),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf121 : Bracket :=
  ⟨1213, 1214, (Int.negSucc 27009003650752782), (Int.negSucc 27009003650752766), (Int.ofNat 6710020487776905), (Int.ofNat 6710020487776913),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf122 : Bracket :=
  ⟨1224, 1225, (Int.ofNat 42246845269494113), (Int.ofNat 42246845269494119), (Int.negSucc 22391003298829049), (Int.negSucc 22391003298829033),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf123 : Bracket :=
  ⟨1232, 1233, (Int.negSucc 78944346494595064), (Int.negSucc 78944346494595061), (Int.ofNat 13768324062499463), (Int.ofNat 13768324062499476),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf124 : Bracket :=
  ⟨1248, 1249, (Int.ofNat 92962696373275268), (Int.ofNat 92962696373275280), (Int.negSucc 23095441438377966), (Int.negSucc 23095441438377956),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf125 : Bracket :=
  ⟨1256, 1257, (Int.negSucc 51763621399784790), (Int.negSucc 51763621399784780), (Int.ofNat 40361577398609864), (Int.ofNat 40361577398609883),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf126 : Bracket :=
  ⟨1272, 1273, (Int.ofNat 14580835314667878), (Int.ofNat 14580835314667880), (Int.negSucc 17737431737971785), (Int.negSucc 17737431737971769),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf127 : Bracket :=
  ⟨1278, 1279, (Int.negSucc 13890349317076402), (Int.negSucc 13890349317076389), (Int.ofNat 2187925561536658), (Int.ofNat 2187925561536668),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf128 : Bracket :=
  ⟨1288, 1289, (Int.ofNat 1645795401900294), (Int.ofNat 1645795401900297), (Int.negSucc 791395281360401), (Int.negSucc 791395281360384),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf129 : Bracket :=
  ⟨1289, 1290, (Int.negSucc 791395281360401), (Int.negSucc 791395281360384), (Int.ofNat 313308359343366), (Int.ofNat 313308359343380),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf130 : Bracket :=
  ⟨1296, 1297, (Int.ofNat 12546740444494956), (Int.ofNat 12546740444494959), (Int.negSucc 3176141791408033), (Int.negSucc 3176141791408017),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf131 : Bracket :=
  ⟨1312, 1313, (Int.negSucc 25390823453987499), (Int.negSucc 25390823453987496), (Int.ofNat 37276172440905242), (Int.ofNat 37276172440905258),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf132 : Bracket :=
  ⟨1320, 1321, (Int.ofNat 27764745508077760), (Int.ofNat 27764745508077775), (Int.negSucc 31833698076258193), (Int.negSucc 31833698076258183),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf133 : Bracket :=
  ⟨1327, 1328, (Int.negSucc 58486796519804290), (Int.negSucc 58486796519804279), (Int.ofNat 42479352845489905), (Int.ofNat 42479352845489920),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf134 : Bracket :=
  ⟨1340, 1341, (Int.ofNat 202873745941188589), (Int.ofNat 202873745941188593), (Int.negSucc 102201295510932509), (Int.negSucc 102201295510932490),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf135 : Bracket :=
  ⟨1355, 1356, (Int.negSucc 69891502999114582), (Int.negSucc 69891502999114563), (Int.ofNat 248525578240537697), (Int.ofNat 248525578240537702),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf136 : Bracket :=
  ⟨1365, 1366, (Int.ofNat 28681228233850791), (Int.ofNat 28681228233850808), (Int.negSucc 218364584332048556), (Int.negSucc 218364584332048543),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf137 : Bracket :=
  ⟨1373, 1374, (Int.negSucc 275687740853234985), (Int.negSucc 275687740853234975), (Int.ofNat 10393122358710862), (Int.ofNat 10393122358710880),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf138 : Bracket :=
  ⟨1392, 1393, (Int.ofNat 87814145167481981), (Int.ofNat 87814145167481989), (Int.negSucc 4530341942021529), (Int.negSucc 4530341942021514),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf139 : Bracket :=
  ⟨1397, 1398, (Int.negSucc 20484360054704172), (Int.negSucc 20484360054704159), (Int.ofNat 11983210108231949), (Int.ofNat 11983210108231964),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf140 : Bracket :=
  ⟨1401, 1402, (Int.ofNat 21372234715594176), (Int.ofNat 21372234715594182), (Int.negSucc 25150397516681805), (Int.negSucc 25150397516681785),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf141 : Bracket :=
  ⟨1415, 1416, (Int.negSucc 71656531777812156), (Int.negSucc 71656531777812142), (Int.ofNat 91869401040712477), (Int.ofNat 91869401040712481),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf142 : Bracket :=
  ⟨1424, 1425, (Int.ofNat 19876053593556532), (Int.ofNat 19876053593556547), (Int.negSucc 204075362797785195), (Int.negSucc 204075362797785183),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf143 : Bracket :=
  ⟨1440, 1441, (Int.negSucc 56071963058996193), (Int.negSucc 56071963058996190), (Int.ofNat 102753319480547530), (Int.ofNat 102753319480547549),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf144 : Bracket :=
  ⟨1448, 1449, (Int.ofNat 59084606579432783), (Int.ofNat 59084606579432798), (Int.negSucc 39245202589870695), (Int.negSucc 39245202589870678),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf145 : Bracket :=
  ⟨1458, 1459, (Int.negSucc 42001193284334422), (Int.negSucc 42001193284334407), (Int.ofNat 22171830748875192), (Int.ofNat 22171830748875200),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf146 : Bracket :=
  ⟨1465, 1466, (Int.ofNat 22794428158383484), (Int.ofNat 22794428158383498), (Int.negSucc 38768320463039121), (Int.negSucc 38768320463039114),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf147 : Bracket :=
  ⟨1475, 1476, (Int.negSucc 45853282656775766), (Int.negSucc 45853282656775755), (Int.ofNat 40969098632062854), (Int.ofNat 40969098632062871),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf148 : Bracket :=
  ⟨1486, 1487, (Int.ofNat 13653803273364398), (Int.ofNat 13653803273364407), (Int.negSucc 74753235732374528), (Int.negSucc 74753235732374516),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf149 : Bracket :=
  ⟨1494, 1495, (Int.negSucc 75126134629209272), (Int.negSucc 75126134629209254), (Int.ofNat 26561151790055109), (Int.ofNat 26561151790055125),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf150 : Bracket :=
  ⟨1508, 1509, (Int.ofNat 28308234413669598), (Int.ofNat 28308234413669601), (Int.negSucc 44151021055197431), (Int.negSucc 44151021055197424),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf151 : Bracket :=
  ⟨1513, 1514, (Int.negSucc 52214440031986634), (Int.negSucc 52214440031986622), (Int.ofNat 18373477176263949), (Int.ofNat 18373477176263967),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf152 : Bracket :=
  ⟨1527, 1528, (Int.ofNat 76804840693950973), (Int.ofNat 76804840693950985), (Int.negSucc 41367381592624202), (Int.negSucc 41367381592624199),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf153 : Bracket :=
  ⟨1538, 1539, (Int.negSucc 18455054872862219), (Int.negSucc 18455054872862202), (Int.ofNat 48865125205072209), (Int.ofNat 48865125205072214),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf154 : Bracket :=
  ⟨1546, 1547, (Int.ofNat 26927277286866193), (Int.ofNat 26927277286866210), (Int.negSucc 19217105449029816), (Int.negSucc 19217105449029800),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf155 : Bracket :=
  ⟨1552, 1553, (Int.negSucc 21326527543889931), (Int.negSucc 21326527543889927), (Int.ofNat 44580002172666430), (Int.ofNat 44580002172666448),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf156 : Bracket :=
  ⟨1568, 1569, (Int.ofNat 44193212539295727), (Int.ofNat 44193212539295729), (Int.negSucc 46375434891812710), (Int.negSucc 46375434891812699),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf157 : Bracket :=
  ⟨1576, 1577, (Int.negSucc 34709191460708750), (Int.negSucc 34709191460708747), (Int.ofNat 29009520021847720), (Int.ofNat 29009520021847729),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf158 : Bracket :=
  ⟨1585, 1586, (Int.ofNat 47627964737157348), (Int.ofNat 47627964737157356), (Int.negSucc 15535859130223616), (Int.negSucc 15535859130223603),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf159 : Bracket :=
  ⟨1595, 1596, (Int.negSucc 17080598928539441), (Int.negSucc 17080598928539435), (Int.ofNat 52276951943671066), (Int.ofNat 52276951943671069),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf160 : Bracket :=
  ⟨1605, 1606, (Int.ofNat 43163575068227878), (Int.ofNat 43163575068227894), (Int.negSucc 26642491490776667), (Int.negSucc 26642491490776655),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf161 : Bracket :=
  ⟨1614, 1615, (Int.negSucc 30817091523512952), (Int.negSucc 30817091523512939), (Int.ofNat 49465815961414573), (Int.ofNat 49465815961414580),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf162 : Bracket :=
  ⟨1629, 1630, (Int.ofNat 1077391097681707), (Int.ofNat 1077391097681721), (Int.negSucc 31893369252569334), (Int.negSucc 31893369252569325),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf163 : Bracket :=
  ⟨1635, 1636, (Int.negSucc 11406563175885561), (Int.negSucc 11406563175885547), (Int.ofNat 6719563204296475), (Int.ofNat 6719563204296485),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf164 : Bracket :=
  ⟨1639, 1640, (Int.ofNat 16471153261938218), (Int.ofNat 16471153261938227), (Int.negSucc 981046679502992), (Int.negSucc 981046679502987),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf165 : Bracket :=
  ⟨1649, 1650, (Int.negSucc 5867246232352402), (Int.negSucc 5867246232352392), (Int.ofNat 76975432796433905), (Int.ofNat 76975432796433923),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf166 : Bracket :=
  ⟨1660, 1661, (Int.ofNat 154495800008558288), (Int.ofNat 154495800008558291), (Int.negSucc 38327853273273616), (Int.negSucc 38327853273273609),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf167 : Bracket :=
  ⟨1674, 1675, (Int.negSucc 253287854414221981), (Int.negSucc 253287854414221971), (Int.ofNat 16942862799765265), (Int.ofNat 16942862799765273),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf168 : Bracket :=
  ⟨1687, 1688, (Int.ofNat 90537633096902714), (Int.ofNat 90537633096902724), (Int.negSucc 32923219073190249), (Int.negSucc 32923219073190236),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf169 : Bracket :=
  ⟨1693, 1694, (Int.negSucc 53305177575869310), (Int.negSucc 53305177575869293), (Int.ofNat 34359879602052056), (Int.ofNat 34359879602052069),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf170 : Bracket :=
  ⟨1700, 1701, (Int.ofNat 119314885012980625), (Int.ofNat 119314885012980632), (Int.negSucc 28460395674572217), (Int.negSucc 28460395674572206),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf171 : Bracket :=
  ⟨1715, 1716, (Int.negSucc 163488731197868476), (Int.negSucc 163488731197868465), (Int.ofNat 109169023237987821), (Int.ofNat 109169023237987825),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf172 : Bracket :=
  ⟨1721, 1722, (Int.ofNat 232670046383676439), (Int.ofNat 232670046383676457), (Int.negSucc 89804284995257691), (Int.negSucc 89804284995257675),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf173 : Bracket :=
  ⟨1741, 1742, (Int.negSucc 99492552240033404), (Int.negSucc 99492552240033394), (Int.ofNat 410781612491916833), (Int.ofNat 410781612491916848),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf174 : Bracket :=
  ⟨1752, 1753, (Int.ofNat 50788539396897081), (Int.ofNat 50788539396897084), (Int.negSucc 193364157284478986), (Int.negSucc 193364157284478970),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf175 : Bracket :=
  ⟨1763, 1764, (Int.negSucc 38500188883157673), (Int.negSucc 38500188883157660), (Int.ofNat 58069989146704727), (Int.ofNat 58069989146704730),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf176 : Bracket :=
  ⟨1769, 1770, (Int.ofNat 70950547167755025), (Int.ofNat 70950547167755035), (Int.negSucc 2283166756318669), (Int.negSucc 2283166756318659),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf177 : Bracket :=
  ⟨1784, 1785, (Int.negSucc 7905549109869972), (Int.negSucc 7905549109869969), (Int.ofNat 17144256492758277), (Int.ofNat 17144256492758295),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf178 : Bracket :=
  ⟨1789, 1790, (Int.ofNat 990402229787702), (Int.ofNat 990402229787710), (Int.negSucc 18612279231875366), (Int.negSucc 18612279231875355),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf179 : Bracket :=
  ⟨1797, 1798, (Int.negSucc 7153157077763289), (Int.negSucc 7153157077763277), (Int.ofNat 17827523841348975), (Int.ofNat 17827523841348991),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf180 : Bracket :=
  ⟨1807, 1808, (Int.ofNat 9121793343295128), (Int.ofNat 9121793343295134), (Int.negSucc 12289474785623934), (Int.negSucc 12289474785623931),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf181 : Bracket :=
  ⟨1813, 1814, (Int.negSucc 13858595449429604), (Int.negSucc 13858595449429599), (Int.ofNat 9367858335594443), (Int.ofNat 9367858335594456),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf182 : Bracket :=
  ⟨1822, 1823, (Int.ofNat 34928479287446708), (Int.ofNat 34928479287446715), (Int.negSucc 11896788054846016), (Int.negSucc 11896788054846002),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf183 : Bracket :=
  ⟨1835, 1836, (Int.negSucc 59665321294792575), (Int.negSucc 59665321294792564), (Int.ofNat 1231255816749436), (Int.ofNat 1231255816749440),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf184 : Bracket :=
  ⟨1843, 1844, (Int.ofNat 11512254749474721), (Int.ofNat 11512254749474728), (Int.negSucc 50079635637172991), (Int.negSucc 50079635637172976),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf185 : Bracket :=
  ⟨1854, 1855, (Int.negSucc 34675036694291950), (Int.negSucc 34675036694291933), (Int.ofNat 44488039932733282), (Int.ofNat 44488039932733288),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf186 : Bracket :=
  ⟨1862, 1863, (Int.ofNat 45995687080882785), (Int.ofNat 45995687080882797), (Int.negSucc 62767403711818689), (Int.negSucc 62767403711818676),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf187 : Bracket :=
  ⟨1878, 1879, (Int.negSucc 66139991433604579), (Int.negSucc 66139991433604569), (Int.ofNat 12144407278201793), (Int.ofNat 12144407278201806),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf188 : Bracket :=
  ⟨1883, 1884, (Int.ofNat 36667773608120107), (Int.ofNat 36667773608120125), (Int.negSucc 19689603954914995), (Int.negSucc 19689603954914992),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf189 : Bracket :=
  ⟨1893, 1894, (Int.negSucc 71948213560469250), (Int.negSucc 71948213560469234), (Int.ofNat 46080138654967299), (Int.ofNat 46080138654967313),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf190 : Bracket :=
  ⟨1907, 1908, (Int.ofNat 27282015484757822), (Int.ofNat 27282015484757837), (Int.negSucc 89553786117769973), (Int.negSucc 89553786117769970),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf191 : Bracket :=
  ⟨1916, 1917, (Int.negSucc 20350567225674032), (Int.negSucc 20350567225674030), (Int.ofNat 71285334497520940), (Int.ofNat 71285334497520958),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf192 : Bracket :=
  ⟨1927, 1928, (Int.ofNat 23972065337421590), (Int.ofNat 23972065337421608), (Int.negSucc 21797373594135856), (Int.negSucc 21797373594135853),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf193 : Bracket :=
  ⟨1931, 1932, (Int.negSucc 30873292712848212), (Int.negSucc 30873292712848204), (Int.ofNat 13540549779497513), (Int.ofNat 13540549779497516),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf194 : Bracket :=
  ⟨1944, 1945, (Int.ofNat 76670945202866013), (Int.ofNat 76670945202866016), (Int.negSucc 33452338105863279), (Int.negSucc 33452338105863263),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf195 : Bracket :=
  ⟨1953, 1954, (Int.negSucc 33261128943509812), (Int.negSucc 33261128943509801), (Int.ofNat 77698873642311159), (Int.ofNat 77698873642311168),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf196 : Bracket :=
  ⟨1960, 1961, (Int.ofNat 158014692385525208), (Int.ofNat 158014692385525220), (Int.negSucc 11068009824874471), (Int.negSucc 11068009824874459),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf197 : Bracket :=
  ⟨1977, 1978, (Int.negSucc 235653884704962747), (Int.negSucc 235653884704962735), (Int.ofNat 99548433302392389), (Int.ofNat 99548433302392403),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf198 : Bracket :=
  ⟨1988, 1989, (Int.ofNat 119130103738824487), (Int.ofNat 119130103738824490), (Int.negSucc 68621791840360534), (Int.negSucc 68621791840360520),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf199 : Bracket :=
  ⟨1995, 1996, (Int.negSucc 160010535458865112), (Int.negSucc 160010535458865096), (Int.ofNat 9798350111375881), (Int.ofNat 9798350111375894),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf200 : Bracket :=
  ⟨2009, 2010, (Int.ofNat 114010671957646086), (Int.ofNat 114010671957646100), (Int.negSucc 78645557755034707), (Int.negSucc 78645557755034700),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf201 : Bracket :=
  ⟨2020, 2021, (Int.negSucc 30995934637066260), (Int.negSucc 30995934637066257), (Int.ofNat 69542578004103130), (Int.ofNat 69542578004103146),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf202 : Bracket :=
  ⟨2028, 2029, (Int.ofNat 57095928697544143), (Int.ofNat 57095928697544146), (Int.negSucc 13307222382204614), (Int.negSucc 13307222382204609),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf203 : Bracket :=
  ⟨2037, 2038, (Int.negSucc 43027789337893564), (Int.negSucc 43027789337893550), (Int.ofNat 12966837429345535), (Int.ofNat 12966837429345545),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf204 : Bracket :=
  ⟨2045, 2046, (Int.ofNat 21585572914315761), (Int.ofNat 21585572914315764), (Int.negSucc 36955607407144047), (Int.negSucc 36955607407144037),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf205 : Bracket :=
  ⟨2054, 2055, (Int.negSucc 2083268816111751), (Int.negSucc 2083268816111743), (Int.ofNat 94886257488498866), (Int.ofNat 94886257488498870),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf206 : Bracket :=
  ⟨2065, 2066, (Int.ofNat 55662204045643430), (Int.ofNat 55662204045643437), (Int.negSucc 89064221868690407), (Int.negSucc 89064221868690401),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf207 : Bracket :=
  ⟨2075, 2076, (Int.negSucc 102789838942583921), (Int.negSucc 102789838942583910), (Int.ofNat 80390093966138226), (Int.ofNat 80390093966138229),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf208 : Bracket :=
  ⟨2087, 2088, (Int.ofNat 99645245299948005), (Int.ofNat 99645245299948016), (Int.negSucc 127963189649882224), (Int.negSucc 127963189649882221),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf209 : Bracket :=
  ⟨2101, 2102, (Int.negSucc 105576263431239193), (Int.negSucc 105576263431239180), (Int.ofNat 5890919340117586), (Int.ofNat 5890919340117595),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf210 : Bracket :=
  ⟨2107, 2108, (Int.ofNat 45903075233833344), (Int.ofNat 45903075233833359), (Int.negSucc 30237674440352633), (Int.negSucc 30237674440352631),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf211 : Bracket :=
  ⟨2118, 2119, (Int.negSucc 90238379685290233), (Int.negSucc 90238379685290219), (Int.ofNat 11189074660449559), (Int.ofNat 11189074660449577),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf212 : Bracket :=
  ⟨2130, 2131, (Int.ofNat 51148239293580060), (Int.ofNat 51148239293580075), (Int.negSucc 15642241396914629), (Int.negSucc 15642241396914624),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf213 : Bracket :=
  ⟨2139, 2140, (Int.negSucc 12264284382089359), (Int.negSucc 12264284382089351), (Int.ofNat 28756575320142530), (Int.ofNat 28756575320142537),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf214 : Bracket :=
  ⟨2149, 2150, (Int.ofNat 2085761984968366), (Int.ofNat 2085761984968380), (Int.negSucc 16680608689125319), (Int.negSucc 16680608689125308),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf215 : Bracket :=
  ⟨2153, 2154, (Int.negSucc 10840693171076866), (Int.negSucc 10840693171076861), (Int.ofNat 13698418947031079), (Int.ofNat 13698418947031089),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf216 : Bracket :=
  ⟨2166, 2167, (Int.ofNat 21195227069118511), (Int.ofNat 21195227069118524), (Int.negSucc 33658265615718750), (Int.negSucc 33658265615718735),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf217 : Bracket :=
  ⟨2175, 2176, (Int.negSucc 47175963617711461), (Int.negSucc 47175963617711454), (Int.ofNat 5121344957778306), (Int.ofNat 5121344957778309),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf218 : Bracket :=
  ⟨2188, 2189, (Int.ofNat 9409074300189929), (Int.ofNat 9409074300189932), (Int.negSucc 8995118724565301), (Int.negSucc 8995118724565291),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf219 : Bracket :=
  ⟨2191, 2192, (Int.negSucc 10898407438103487), (Int.negSucc 10898407438103475), (Int.ofNat 4758939148848787), (Int.ofNat 4758939148848789),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf220 : Bracket :=
  ⟨2200, 2201, (Int.ofNat 28501684980366360), (Int.ofNat 28501684980366375), (Int.negSucc 34653315531296501), (Int.negSucc 34653315531296485),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf221 : Bracket :=
  ⟨2215, 2216, (Int.negSucc 37398635419554464), (Int.negSucc 37398635419554448), (Int.ofNat 66267556448840478), (Int.ofNat 66267556448840481),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf222 : Bracket :=
  ⟨2224, 2225, (Int.ofNat 12963526159998699), (Int.ofNat 12963526159998702), (Int.negSucc 78640536595115553), (Int.negSucc 78640536595115545),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf223 : Bracket :=
  ⟨2237, 2238, (Int.negSucc 3832617629277668), (Int.negSucc 3832617629277663), (Int.ofNat 9795646958182989), (Int.ofNat 9795646958182999),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf224 : Bracket :=
  ⟨2239, 2240, (Int.ofNat 4997008072061634), (Int.ofNat 4997008072061650), (Int.negSucc 13666168587154006), (Int.negSucc 13666168587154003),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf225 : Bracket :=
  ⟨2244, 2245, (Int.negSucc 8655337694698312), (Int.negSucc 8655337694698309), (Int.ofNat 86774242045709267), (Int.ofNat 86774242045709274),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf226 : Bracket :=
  ⟨2265, 2266, (Int.ofNat 606388786163117284), (Int.ofNat 606388786163117295), (Int.negSucc 488263421759087345), (Int.negSucc 488263421759087329),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf227 : Bracket :=
  ⟨2283, 2284, (Int.negSucc 230576195195914161), (Int.negSucc 230576195195914149), (Int.ofNat 169352754506701809), (Int.ofNat 169352754506701812),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf228 : Bracket :=
  ⟨2292, 2293, (Int.ofNat 4218135840264777), (Int.ofNat 4218135840264781), (Int.negSucc 148584936257875242), (Int.negSucc 148584936257875237),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf229 : Bracket :=
  ⟨2300, 2301, (Int.negSucc 17955970460029678), (Int.negSucc 17955970460029675), (Int.ofNat 103936549786613517), (Int.ofNat 103936549786613530),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf230 : Bracket :=
  ⟨2310, 2311, (Int.ofNat 37767322623253576), (Int.ofNat 37767322623253585), (Int.negSucc 55200562549812517), (Int.negSucc 55200562549812513),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf231 : Bracket :=
  ⟨2318, 2319, (Int.negSucc 63888558603249752), (Int.negSucc 63888558603249735), (Int.ofNat 6216667043794536), (Int.ofNat 6216667043794543),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf232 : Bracket :=
  ⟨2325, 2326, (Int.ofNat 21269876197942645), (Int.ofNat 21269876197942662), (Int.negSucc 82005468049380360), (Int.negSucc 82005468049380349),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf233 : Bracket :=
  ⟨2342, 2343, (Int.negSucc 7469778011916113), (Int.negSucc 7469778011916105), (Int.ofNat 94750315137696823), (Int.ofNat 94750315137696841),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf234 : Bracket :=
  ⟨2352, 2353, (Int.ofNat 27267555592621310), (Int.ofNat 27267555592621313), (Int.negSucc 1143029497104524), (Int.negSucc 1143029497104506),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf235 : Bracket :=
  ⟨2357, 2358, (Int.negSucc 804120634024724), (Int.negSucc 804120634024713), (Int.ofNat 11507553350055880), (Int.ofNat 11507553350055886),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf236 : Bracket :=
  ⟨2360, 2361, (Int.ofNat 10423791908729865), (Int.ofNat 10423791908729868), (Int.negSucc 14611198212134174), (Int.negSucc 14611198212134164),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf237 : Bracket :=
  ⟨2380, 2381, (Int.negSucc 146045838551395093), (Int.negSucc 146045838551395090), (Int.ofNat 6169965870772505), (Int.ofNat 6169965870772513),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf238 : Bracket :=
  ⟨2394, 2395, (Int.ofNat 9029775470920929), (Int.ofNat 9029775470920944), (Int.negSucc 6827463439852590), (Int.negSucc 6827463439852577),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf239 : Bracket :=
  ⟨2396, 2397, (Int.negSucc 8526231450629209), (Int.negSucc 8526231450629202), (Int.ofNat 1698594236535885), (Int.ofNat 1698594236535894),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf240 : Bracket :=
  ⟨2407, 2408, (Int.ofNat 26046016210657139), (Int.ofNat 26046016210657146), (Int.negSucc 1726052509356278), (Int.negSucc 1726052509356263),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf241 : Bracket :=
  ⟨2415, 2416, (Int.negSucc 5344735926428495), (Int.negSucc 5344735926428488), (Int.ofNat 19739976649417909), (Int.ofNat 19739976649417912),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf242 : Bracket :=
  ⟨2422, 2423, (Int.ofNat 14441455560204159), (Int.ofNat 14441455560204176), (Int.negSucc 26443206136436522), (Int.negSucc 26443206136436505),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf243 : Bracket :=
  ⟨2433, 2434, (Int.negSucc 15087543307838033), (Int.negSucc 15087543307838019), (Int.ofNat 79271168331706907), (Int.ofNat 79271168331706915),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf244 : Bracket :=
  ⟨2445, 2446, (Int.ofNat 63394871980947872), (Int.ofNat 63394871980947885), (Int.negSucc 59139134377828481), (Int.negSucc 59139134377828463),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf245 : Bracket :=
  ⟨2456, 2457, (Int.negSucc 42395740538494464), (Int.negSucc 42395740538494460), (Int.ofNat 48327424904287204), (Int.ofNat 48327424904287210),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf246 : Bracket :=
  ⟨2462, 2463, (Int.ofNat 63032510555644923), (Int.ofNat 63032510555644934), (Int.negSucc 49519332607362488), (Int.negSucc 49519332607362483),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf247 : Bracket :=
  ⟨2480, 2481, (Int.negSucc 30247885872052939), (Int.negSucc 30247885872052936), (Int.ofNat 59012701780196498), (Int.ofNat 59012701780196515),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf248 : Bracket :=
  ⟨2484, 2485, (Int.ofNat 66326270085840962), (Int.ofNat 66326270085840965), (Int.negSucc 11391371123813435), (Int.negSucc 11391371123813425),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf249 : Bracket :=
  ⟨2499, 2500, (Int.negSucc 63377406888031898), (Int.negSucc 63377406888031882), (Int.ofNat 50826918826648640), (Int.ofNat 50826918826648643),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf250 : Bracket :=
  ⟨2508, 2509, (Int.ofNat 20327676556236940), (Int.ofNat 20327676556236943), (Int.negSucc 48316990591731306), (Int.negSucc 48316990591731291),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf251 : Bracket :=
  ⟨2515, 2516, (Int.negSucc 63638598546924478), (Int.negSucc 63638598546924472), (Int.ofNat 3520643642972573), (Int.ofNat 3520643642972588),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf252 : Bracket :=
  ⟨2525, 2526, (Int.ofNat 69078755415737564), (Int.ofNat 69078755415737571), (Int.negSucc 31505225104118135), (Int.negSucc 31505225104118127),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf253 : Bracket :=
  ⟨2539, 2540, (Int.negSucc 55329479630155167), (Int.negSucc 55329479630155162), (Int.ofNat 5054345674225960), (Int.ofNat 5054345674225962),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf254 : Bracket :=
  ⟨2545, 2546, (Int.ofNat 2823939939368649), (Int.ofNat 2823939939368660), (Int.negSucc 41397244831940600), (Int.negSucc 41397244831940588),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf255 : Bracket :=
  ⟨2553, 2554, (Int.negSucc 38646105026743208), (Int.negSucc 38646105026743203), (Int.ofNat 33303718414634571), (Int.ofNat 33303718414634587),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf256 : Bracket :=
  ⟨2564, 2565, (Int.ofNat 90726378899164281), (Int.ofNat 90726378899164285), (Int.negSucc 899964553190867), (Int.negSucc 899964553190855),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf257 : Bracket :=
  ⟨2571, 2572, (Int.negSucc 54919372534059683), (Int.negSucc 54919372534059671), (Int.ofNat 61933123331170703), (Int.ofNat 61933123331170706),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf258 : Bracket :=
  ⟨2582, 2583, (Int.ofNat 257763141090584130), (Int.ofNat 257763141090584145), (Int.negSucc 28394157905063875), (Int.negSucc 28394157905063862),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf259 : Bracket :=
  ⟨2594, 2595, (Int.negSucc 273082389760280150), (Int.negSucc 273082389760280138), (Int.ofNat 330351227023788870), (Int.ofNat 330351227023788887),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf260 : Bracket :=
  ⟨2614, 2615, (Int.ofNat 102585009859090658), (Int.ofNat 102585009859090674), (Int.negSucc 215614483827535506), (Int.negSucc 215614483827535491),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf261 : Bracket :=
  ⟨2623, 2624, (Int.negSucc 97872760129698828), (Int.negSucc 97872760129698820), (Int.ofNat 16812217595138794), (Int.ofNat 16812217595138796),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf262 : Bracket :=
  ⟨2630, 2631, (Int.ofNat 19985885188852596), (Int.ofNat 19985885188852601), (Int.negSucc 59575833220254212), (Int.negSucc 59575833220254199),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf263 : Bracket :=
  ⟨2640, 2641, (Int.negSucc 62822194755023608), (Int.negSucc 62822194755023605), (Int.ofNat 3746016506451814), (Int.ofNat 3746016506451824),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf264 : Bracket :=
  ⟨2647, 2648, (Int.ofNat 41100173939444509), (Int.ofNat 41100173939444526), (Int.negSucc 16974335543126478), (Int.negSucc 16974335543126475),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf265 : Bracket :=
  ⟨2656, 2657, (Int.negSucc 87171968371985461), (Int.negSucc 87171968371985459), (Int.ofNat 3026848216345403), (Int.ofNat 3026848216345420),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf266 : Bracket :=
  ⟨2668, 2669, (Int.ofNat 104655187336259230), (Int.ofNat 104655187336259242), (Int.negSucc 27960353557617870), (Int.negSucc 27960353557617852),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf267 : Bracket :=
  ⟨2682, 2683, (Int.negSucc 24591415016376118), (Int.negSucc 24591415016376113), (Int.ofNat 34443982546779603), (Int.ofNat 34443982546779619),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf268 : Bracket :=
  ⟨2687, 2688, (Int.ofNat 25344922642056078), (Int.ofNat 25344922642056092), (Int.negSucc 32010866170757109), (Int.negSucc 32010866170757106),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf269 : Bracket :=
  ⟨2703, 2704, (Int.negSucc 4317222117910663), (Int.negSucc 4317222117910647), (Int.ofNat 32144307101607285), (Int.ofNat 32144307101607287),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf270 : Bracket :=
  ⟨2710, 2711, (Int.ofNat 10987555657565763), (Int.ofNat 10987555657565779), (Int.negSucc 5922503250636419), (Int.negSucc 5922503250636401),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf271 : Bracket :=
  ⟨2715, 2716, (Int.negSucc 5593268620921193), (Int.negSucc 5593268620921179), (Int.ofNat 12417715927332198), (Int.ofNat 12417715927332202),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf272 : Bracket :=
  ⟨2724, 2725, (Int.ofNat 34012361367979879), (Int.ofNat 34012361367979883), (Int.negSucc 376266184547245), (Int.negSucc 376266184547236),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf273 : Bracket :=
  ⟨2733, 2734, (Int.negSucc 35223956340799852), (Int.negSucc 35223956340799841), (Int.ofNat 27073960954502474), (Int.ofNat 27073960954502480),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf274 : Bracket :=
  ⟨2748, 2749, (Int.ofNat 26069908619808279), (Int.ofNat 26069908619808282), (Int.negSucc 46153019361130508), (Int.negSucc 46153019361130495),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf275 : Bracket :=
  ⟨2757, 2758, (Int.negSucc 22420520262011970), (Int.negSucc 22420520262011959), (Int.ofNat 17667362546324138), (Int.ofNat 17667362546324145),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf276 : Bracket :=
  ⟨2762, 2763, (Int.ofNat 38068617507667503), (Int.ofNat 38068617507667510), (Int.negSucc 2094344988686126), (Int.negSucc 2094344988686118),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf277 : Bracket :=
  ⟨2777, 2778, (Int.negSucc 24263533919751079), (Int.negSucc 24263533919751069), (Int.ofNat 42717940985533378), (Int.ofNat 42717940985533384),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf278 : Bracket :=
  ⟨2784, 2785, (Int.ofNat 42501832059942662), (Int.ofNat 42501832059942665), (Int.negSucc 12817717163580789), (Int.negSucc 12817717163580783),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf279 : Bracket :=
  ⟨2792, 2793, (Int.negSucc 69869015689458031), (Int.negSucc 69869015689458027), (Int.ofNat 3919805304174848), (Int.ofNat 3919805304174858),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf280 : Bracket :=
  ⟨2803, 2804, (Int.ofNat 68395509654635428), (Int.ofNat 68395509654635441), (Int.negSucc 61222790792472745), (Int.negSucc 61222790792472742),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf281 : Bracket :=
  ⟨2813, 2814, (Int.negSucc 5981994280893667), (Int.negSucc 5981994280893651), (Int.ofNat 206351813821569234), (Int.ofNat 206351813821569247),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf282 : Bracket :=
  ⟨2826, 2827, (Int.ofNat 203285056415301432), (Int.ofNat 203285056415301450), (Int.negSucc 30678938039885314), (Int.negSucc 30678938039885309),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf283 : Bracket :=
  ⟨2834, 2835, (Int.negSucc 167468232957665453), (Int.negSucc 167468232957665435), (Int.ofNat 44372588305699811), (Int.ofNat 44372588305699817),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf284 : Bracket :=
  ⟨2844, 2845, (Int.ofNat 97604713193627775), (Int.ofNat 97604713193627778), (Int.negSucc 313193993489727788), (Int.negSucc 313193993489727783),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf285 : Bracket :=
  ⟨2861, 2862, (Int.negSucc 186421658612396014), (Int.negSucc 186421658612396008), (Int.ofNat 221835495180911892), (Int.ofNat 221835495180911907),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf286 : Bracket :=
  ⟨2871, 2872, (Int.ofNat 168358457648405982), (Int.ofNat 168358457648405997), (Int.negSucc 52913800938712674), (Int.negSucc 52913800938712671),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf287 : Bracket :=
  ⟨2882, 2883, (Int.negSucc 19474331245032678), (Int.negSucc 19474331245032669), (Int.ofNat 63303143117193169), (Int.ofNat 63303143117193179),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf288 : Bracket :=
  ⟨2886, 2887, (Int.ofNat 71512190398244157), (Int.ofNat 71512190398244175), (Int.negSucc 12846894036580495), (Int.negSucc 12846894036580485),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf289 : Bracket :=
  ⟨2902, 2903, (Int.negSucc 74036592792111805), (Int.negSucc 74036592792111788), (Int.ofNat 84069068183971169), (Int.ofNat 84069068183971177),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf290 : Bracket :=
  ⟨2914, 2915, (Int.ofNat 36196542061252056), (Int.ofNat 36196542061252061), (Int.negSucc 10118157751881195), (Int.negSucc 10118157751881188),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf291 : Bracket :=
  ⟨2919, 2920, (Int.negSucc 21145527911121072), (Int.negSucc 21145527911121060), (Int.ofNat 6723299826499581), (Int.ofNat 6723299826499584),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf292 : Bracket :=
  ⟨2927, 2928, (Int.ofNat 31949241179008099), (Int.ofNat 31949241179008108), (Int.negSucc 8245492846978443), (Int.negSucc 8245492846978440),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf293 : Bracket :=
  ⟨2938, 2939, (Int.negSucc 12717275296629070), (Int.negSucc 12717275296629062), (Int.ofNat 41135951671581170), (Int.ofNat 41135951671581176),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf294 : Bracket :=
  ⟨2948, 2949, (Int.ofNat 12465233928680794), (Int.ofNat 12465233928680797), (Int.negSucc 36038362241641725), (Int.negSucc 36038362241641718),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf295 : Bracket :=
  ⟨2957, 2958, (Int.negSucc 22821091520397223), (Int.negSucc 22821091520397205), (Int.ofNat 11667296284505057), (Int.ofNat 11667296284505074),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf296 : Bracket :=
  ⟨2962, 2963, (Int.ofNat 21042003962846375), (Int.ofNat 21042003962846383), (Int.negSucc 22949521069157784), (Int.negSucc 22949521069157770),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf297 : Bracket :=
  ⟨2976, 2977, (Int.negSucc 80570323684907510), (Int.negSucc 80570323684907508), (Int.ofNat 36561511080104149), (Int.ofNat 36561511080104166),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf298 : Bracket :=
  ⟨2985, 2986, (Int.ofNat 30025992575926613), (Int.ofNat 30025992575926624), (Int.negSucc 109519386892800882), (Int.negSucc 109519386892800864),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf299 : Bracket :=
  ⟨2996, 2997, (Int.negSucc 18697152435473985), (Int.negSucc 18697152435473972), (Int.ofNat 227552121501019880), (Int.ofNat 227552121501019887),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf300 : Bracket :=
  ⟨3013, 3014, (Int.ofNat 110210053624633569), (Int.ofNat 110210053624633573), (Int.negSucc 791953153394488), (Int.negSucc 791953153394482),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf301 : Bracket :=
  ⟨3018, 3019, (Int.negSucc 22622553723843815), (Int.negSucc 22622553723843810), (Int.ofNat 55302933733508774), (Int.ofNat 55302933733508786),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf302 : Bracket :=
  ⟨3032, 3033, (Int.ofNat 62754477430340656), (Int.ofNat 62754477430340658), (Int.negSucc 14292724971555790), (Int.negSucc 14292724971555779),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf303 : Bracket :=
  ⟨3042, 3043, (Int.negSucc 7770828437791587), (Int.negSucc 7770828437791578), (Int.ofNat 19069237119498800), (Int.ofNat 19069237119498817),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf304 : Bracket :=
  ⟨3048, 3049, (Int.ofNat 7425435372074766), (Int.ofNat 7425435372074769), (Int.negSucc 15895864336762853), (Int.negSucc 15895864336762850),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf305 : Bracket :=
  ⟨3059, 3060, (Int.negSucc 3005853591661893), (Int.negSucc 3005853591661881), (Int.ofNat 7706943105693947), (Int.ofNat 7706943105693950),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf306 : Bracket :=
  ⟨3062, 3063, (Int.ofNat 6343706917988505), (Int.ofNat 6343706917988509), (Int.negSucc 6301868452884773), (Int.negSucc 6301868452884770),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf307 : Bracket :=
  ⟨3072, 3073, (Int.negSucc 21333812323079861), (Int.negSucc 21333812323079859), (Int.ofNat 28635711530866974), (Int.ofNat 28635711530866977),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf308 : Bracket :=
  ⟨3083, 3084, (Int.ofNat 67839028736757814), (Int.ofNat 67839028736757823), (Int.negSucc 13041892056385537), (Int.negSucc 13041892056385534),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf309 : Bracket :=
  ⟨3090, 3091, (Int.negSucc 94438791704779609), (Int.negSucc 94438791704779593), (Int.ofNat 28893392551294992), (Int.ofNat 28893392551295004),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf310 : Bracket :=
  ⟨3109, 3110, (Int.ofNat 16891972867870852), (Int.ofNat 16891972867870863), (Int.negSucc 230350047703172529), (Int.negSucc 230350047703172520),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf311 : Bracket :=
  ⟨3121, 3122, (Int.negSucc 53305800098031132), (Int.negSucc 53305800098031115), (Int.ofNat 26729384227075725), (Int.ofNat 26729384227075741),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf312 : Bracket :=
  ⟨3127, 3128, (Int.ofNat 30843629373974105), (Int.ofNat 30843629373974109), (Int.negSucc 11138334957129680), (Int.negSucc 11138334957129677),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf313 : Bracket :=
  ⟨3133, 3134, (Int.negSucc 23199832043150283), (Int.negSucc 23199832043150267), (Int.ofNat 27790265361885842), (Int.ofNat 27790265361885850),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf314 : Bracket :=
  ⟨3140, 3141, (Int.ofNat 75558182024163409), (Int.ofNat 75558182024163412), (Int.negSucc 57191313168487494), (Int.negSucc 57191313168487490),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf315 : Bracket :=
  ⟨3158, 3159, (Int.negSucc 266093568645831347), (Int.negSucc 266093568645831342), (Int.ofNat 146166436172790080), (Int.ofNat 146166436172790089),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf316 : Bracket :=
  ⟨3170, 3171, (Int.ofNat 39018497058387111), (Int.ofNat 39018497058387129), (Int.negSucc 203116817158274106), (Int.negSucc 203116817158274090),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf317 : Bracket :=
  ⟨3179, 3180, (Int.negSucc 7484834409232359), (Int.negSucc 7484834409232344), (Int.ofNat 193160765107672545), (Int.ofNat 193160765107672548),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf318 : Bracket :=
  ⟨3188, 3189, (Int.ofNat 127456841813374643), (Int.ofNat 127456841813374646), (Int.negSucc 104839328252821716), (Int.negSucc 104839328252821707),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf319 : Bracket :=
  ⟨3201, 3202, (Int.negSucc 110893839626631576), (Int.negSucc 110893839626631573), (Int.ofNat 85738286517601488), (Int.ofNat 85738286517601495),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf320 : Bracket :=
  ⟨3210, 3211, (Int.ofNat 56299389948198695), (Int.ofNat 56299389948198707), (Int.negSucc 88469893221165002), (Int.negSucc 88469893221164994),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf321 : Bracket :=
  ⟨3218, 3219, (Int.negSucc 147962388725811559), (Int.negSucc 147962388725811551), (Int.ofNat 21294889890128875), (Int.ofNat 21294889890128891),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf322 : Bracket :=
  ⟨3233, 3234, (Int.ofNat 152418656602964691), (Int.ofNat 152418656602964698), (Int.negSucc 14750724449781088), (Int.negSucc 14750724449781070),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf323 : Bracket :=
  ⟨3244, 3245, (Int.negSucc 54431033176072313), (Int.negSucc 54431033176072309), (Int.ofNat 14372234832799282), (Int.ofNat 14372234832799292),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf324 : Bracket :=
  ⟨3253, 3254, (Int.ofNat 12261766033947882), (Int.ofNat 12261766033947900), (Int.negSucc 17841901673536462), (Int.negSucc 17841901673536445),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf325 : Bracket :=
  ⟨3259, 3260, (Int.negSucc 23366620759595605), (Int.negSucc 23366620759595597), (Int.ofNat 2133654282523386), (Int.ofNat 2133654282523389),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf326 : Bracket :=
  ⟨3270, 3271, (Int.ofNat 16825801618297827), (Int.ofNat 16825801618297833), (Int.negSucc 5244572278155464), (Int.negSucc 5244572278155452),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf327 : Bracket :=
  ⟨3275, 3276, (Int.negSucc 18329784207757777), (Int.negSucc 18329784207757763), (Int.ofNat 954489230511800), (Int.ofNat 954489230511803),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf328 : Bracket :=
  ⟨3286, 3287, (Int.ofNat 28987455079683779), (Int.ofNat 28987455079683795), (Int.negSucc 19426932144081399), (Int.negSucc 19426932144081393),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf329 : Bracket :=
  ⟨3299, 3300, (Int.negSucc 12154899898129100), (Int.negSucc 12154899898129092), (Int.ofNat 18692286453315440), (Int.ofNat 18692286453315443),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf330 : Bracket :=
  ⟨3303, 3304, (Int.ofNat 26039973745323818), (Int.ofNat 26039973745323828), (Int.negSucc 3566849575386070), (Int.negSucc 3566849575386067),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf331 : Bracket :=
  ⟨3318, 3319, (Int.negSucc 58560275932210478), (Int.negSucc 58560275932210461), (Int.ofNat 333871749485013), (Int.ofNat 333871749485017),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf332 : Bracket :=
  ⟨3326, 3327, (Int.ofNat 21318877382745024), (Int.ofNat 21318877382745031), (Int.negSucc 15602958711163647), (Int.negSucc 15602958711163632),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf333 : Bracket :=
  ⟨3333, 3334, (Int.negSucc 13959999392059797), (Int.negSucc 13959999392059789), (Int.ofNat 36370951015568173), (Int.ofNat 36370951015568177),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf334 : Bracket :=
  ⟨3343, 3344, (Int.ofNat 4166727900123907), (Int.ofNat 4166727900123917), (Int.negSucc 113324802835117958), (Int.negSucc 113324802835117955),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf335 : Bracket :=
  ⟨3356, 3357, (Int.negSucc 18994904287535120), (Int.negSucc 18994904287535117), (Int.ofNat 145068510703623090), (Int.ofNat 145068510703623096),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf336 : Bracket :=
  ⟨3365, 3366, (Int.ofNat 11386305942027321), (Int.ofNat 11386305942027335), (Int.negSucc 200279074169288059), (Int.negSucc 200279074169288051),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf337 : Bracket :=
  ⟨3378, 3379, (Int.negSucc 34576174543818276), (Int.negSucc 34576174543818263), (Int.ofNat 222309205954967121), (Int.ofNat 222309205954967137),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf338 : Bracket :=
  ⟨3390, 3391, (Int.ofNat 81030448396860525), (Int.ofNat 81030448396860539), (Int.negSucc 84432137575341539), (Int.negSucc 84432137575341523),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf339 : Bracket :=
  ⟨3399, 3400, (Int.negSucc 38202659492584798), (Int.negSucc 38202659492584782), (Int.ofNat 75416406756420944), (Int.ofNat 75416406756420946),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf340 : Bracket :=
  ⟨3409, 3410, (Int.ofNat 22509622605477260), (Int.ofNat 22509622605477266), (Int.negSucc 55975511568479228), (Int.negSucc 55975511568479216),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf341 : Bracket :=
  ⟨3416, 3417, (Int.negSucc 46881150863545467), (Int.negSucc 46881150863545464), (Int.ofNat 18271170318601609), (Int.ofNat 18271170318601614),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf342 : Bracket :=
  ⟨3421, 3422, (Int.ofNat 86538828540183468), (Int.ofNat 86538828540183483), (Int.negSucc 1813472411575168), (Int.negSucc 1813472411575159),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf343 : Bracket :=
  ⟨3445, 3446, (Int.negSucc 60434590023178880), (Int.negSucc 60434590023178873), (Int.ofNat 20254026928065715), (Int.ofNat 20254026928065728),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf344 : Bracket :=
  ⟨3448, 3449, (Int.ofNat 31724913432773246), (Int.ofNat 31724913432773249), (Int.negSucc 17879369283986531), (Int.negSucc 17879369283986522),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf345 : Bracket :=
  ⟨3458, 3459, (Int.negSucc 59167225337541023), (Int.negSucc 59167225337541017), (Int.ofNat 53118857656998315), (Int.ofNat 53118857656998325),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf346 : Bracket :=
  ⟨3469, 3470, (Int.ofNat 26399595391374188), (Int.ofNat 26399595391374195), (Int.negSucc 99991431053281180), (Int.negSucc 99991431053281162),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf347 : Bracket :=
  ⟨3478, 3479, (Int.negSucc 119019406804258034), (Int.negSucc 119019406804258020), (Int.ofNat 12194260852017264), (Int.ofNat 12194260852017271),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf348 : Bracket :=
  ⟨3491, 3492, (Int.ofNat 36481931308915072), (Int.ofNat 36481931308915089), (Int.negSucc 39483583274417019), (Int.negSucc 39483583274417016),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf349 : Bracket :=
  ⟨3496, 3497, (Int.negSucc 23049251776836019), (Int.negSucc 23049251776836016), (Int.ofNat 63741439560509059), (Int.ofNat 63741439560509067),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf350 : Bracket :=
  ⟨3509, 3510, (Int.ofNat 148440212957349643), (Int.ofNat 148440212957349654), (Int.negSucc 17483795134183215), (Int.negSucc 17483795134183204),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf351 : Bracket :=
  ⟨3522, 3523, (Int.negSucc 36558388867152234), (Int.negSucc 36558388867152224), (Int.ofNat 40257941637353526), (Int.ofNat 40257941637353531),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf352 : Bracket :=
  ⟨3527, 3528, (Int.ofNat 51485520216810199), (Int.ofNat 51485520216810203), (Int.negSucc 15984237289118404), (Int.negSucc 15984237289118402),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf353 : Bracket :=
  ⟨3539, 3540, (Int.negSucc 3662818690275754), (Int.negSucc 3662818690275750), (Int.ofNat 136958392279609087), (Int.ofNat 136958392279609089),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf354 : Bracket :=
  ⟨3552, 3553, (Int.ofNat 76112174088579062), (Int.ofNat 76112174088579065), (Int.negSucc 31373283392141626), (Int.negSucc 31373283392141614),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf355 : Bracket :=
  ⟨3563, 3564, (Int.negSucc 23768241536696906), (Int.negSucc 23768241536696902), (Int.ofNat 12369649676040581), (Int.ofNat 12369649676040584),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf356 : Bracket :=
  ⟨3569, 3570, (Int.ofNat 11681663651829845), (Int.ofNat 11681663651829851), (Int.negSucc 8589277437402599), (Int.negSucc 8589277437402585),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf357 : Bracket :=
  ⟨3574, 3575, (Int.negSucc 14039016055830205), (Int.negSucc 14039016055830202), (Int.ofNat 16244859714188945), (Int.ofNat 16244859714188949),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf358 : Bracket :=
  ⟨3587, 3588, (Int.ofNat 4586854047937261), (Int.ofNat 4586854047937273), (Int.negSucc 94009095516317495), (Int.negSucc 94009095516317493),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf359 : Bracket :=
  ⟨3598, 3599, (Int.negSucc 30006912877030889), (Int.negSucc 30006912877030873), (Int.ofNat 86806609650940860), (Int.ofNat 86806609650940863),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf360 : Bracket :=
  ⟨3608, 3609, (Int.ofNat 103843921149920766), (Int.ofNat 103843921149920769), (Int.negSucc 20821968620641428), (Int.negSucc 20821968620641425),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf361 : Bracket :=
  ⟨3621, 3622, (Int.negSucc 24378848244094294), (Int.negSucc 24378848244094291), (Int.ofNat 70287361074535361), (Int.ofNat 70287361074535377),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf362 : Bracket :=
  ⟨3630, 3631, (Int.ofNat 46664984399428866), (Int.ofNat 46664984399428875), (Int.negSucc 22514632811520330), (Int.negSucc 22514632811520327),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf363 : Bracket :=
  ⟨3641, 3642, (Int.negSucc 20397365037696981), (Int.negSucc 20397365037696970), (Int.ofNat 20666318414066084), (Int.ofNat 20666318414066100),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf364 : Bracket :=
  ⟨3649, 3650, (Int.ofNat 9420863832082765), (Int.ofNat 9420863832082769), (Int.negSucc 18503491042735983), (Int.negSucc 18503491042735974),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf365 : Bracket :=
  ⟨3657, 3658, (Int.negSucc 14778184506805950), (Int.negSucc 14778184506805938), (Int.ofNat 10922500053724696), (Int.ofNat 10922500053724705),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf366 : Bracket :=
  ⟨3666, 3667, (Int.ofNat 15594403603499790), (Int.ofNat 15594403603499805), (Int.negSucc 1582178010752774), (Int.negSucc 1582178010752761),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf367 : Bracket :=
  ⟨3670, 3671, (Int.negSucc 1733118658732232), (Int.negSucc 1733118658732225), (Int.ofNat 23566078221177091), (Int.ofNat 23566078221177104),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf368 : Bracket :=
  ⟨3685, 3686, (Int.ofNat 15113272573136546), (Int.ofNat 15113272573136557), (Int.negSucc 49603507652465837), (Int.negSucc 49603507652465828),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf369 : Bracket :=
  ⟨3689, 3690, (Int.negSucc 69461444583433182), (Int.negSucc 69461444583433167), (Int.ofNat 4683560132816166), (Int.ofNat 4683560132816171),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf370 : Bracket :=
  ⟨3708, 3709, (Int.ofNat 76077194081538231), (Int.ofNat 76077194081538234), (Int.negSucc 39192303794270098), (Int.negSucc 39192303794270094),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf371 : Bracket :=
  ⟨3711, 3712, (Int.negSucc 23859982688739226), (Int.negSucc 23859982688739222), (Int.ofNat 117045949440318603), (Int.ofNat 117045949440318605),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf372 : Bracket :=
  ⟨3725, 3726, (Int.ofNat 98945930031518750), (Int.ofNat 98945930031518758), (Int.negSucc 735742070775548157), (Int.negSucc 735742070775548153),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf373 : Bracket :=
  ⟨3744, 3745, (Int.negSucc 99065145360183756), (Int.negSucc 99065145360183754), (Int.ofNat 522919645264234270), (Int.ofNat 522919645264234275),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf374 : Bracket :=
  ⟨3756, 3757, (Int.ofNat 33261610316152347), (Int.ofNat 33261610316152350), (Int.negSucc 120755739522020518), (Int.negSucc 120755739522020513),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf375 : Bracket :=
  ⟨3761, 3762, (Int.negSucc 81109389822755568), (Int.negSucc 81109389822755558), (Int.ofNat 51962987967779707), (Int.ofNat 51962987967779717),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf376 : Bracket :=
  ⟨3773, 3774, (Int.ofNat 103682359134693567), (Int.ofNat 103682359134693573), (Int.negSucc 53501483511750900), (Int.negSucc 53501483511750891),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf377 : Bracket :=
  ⟨3784, 3785, (Int.negSucc 77825867918270691), (Int.negSucc 77825867918270688), (Int.ofNat 17431861035764775), (Int.ofNat 17431861035764790),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf378 : Bracket :=
  ⟨3795, 3796, (Int.ofNat 21500134375233970), (Int.ofNat 21500134375233974), (Int.negSucc 8530310240586838), (Int.negSucc 8530310240586835),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf379 : Bracket :=
  ⟨3800, 3801, (Int.negSucc 8460861958740766), (Int.negSucc 8460861958740763), (Int.ofNat 13288547195191545), (Int.ofNat 13288547195191549),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf380 : Bracket :=
  ⟨3807, 3808, (Int.ofNat 31131449071617448), (Int.ofNat 31131449071617460), (Int.negSucc 4513526956046738), (Int.negSucc 4513526956046735),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf381 : Bracket :=
  ⟨3822, 3823, (Int.negSucc 3964440636303959), (Int.negSucc 3964440636303948), (Int.ofNat 13840433426167640), (Int.ofNat 13840433426167643),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf382 : Bracket :=
  ⟨3824, 3825, (Int.ofNat 14872539504041285), (Int.ofNat 14872539504041288), (Int.negSucc 2148628641360998), (Int.negSucc 2148628641360995),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf383 : Bracket :=
  ⟨3840, 3841, (Int.negSucc 26544729814553468), (Int.negSucc 26544729814553465), (Int.ofNat 52580426739524910), (Int.ofNat 52580426739524913),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf384 : Bracket :=
  ⟨3850, 3851, (Int.ofNat 22929559617877285), (Int.ofNat 22929559617877300), (Int.negSucc 14186042876361164), (Int.negSucc 14186042876361160),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf385 : Bracket :=
  ⟨3854, 3855, (Int.negSucc 11866569658425507), (Int.negSucc 11866569658425491), (Int.ofNat 37141876737032131), (Int.ofNat 37141876737032135),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf386 : Bracket :=
  ⟨3874, 3875, (Int.ofNat 25546436616947499), (Int.ofNat 25546436616947503), (Int.negSucc 21967101385256292), (Int.negSucc 21967101385256282),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf387 : Bracket :=
  ⟨3879, 3880, (Int.negSucc 12167111556027456), (Int.negSucc 12167111556027452), (Int.ofNat 20950245203471330), (Int.ofNat 20950245203471332),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf388 : Bracket :=
  ⟨3890, 3891, (Int.ofNat 4965703636222259), (Int.ofNat 4965703636222271), (Int.negSucc 9482353984332424), (Int.negSucc 9482353984332417),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf389 : Bracket :=
  ⟨3892, 3893, (Int.negSucc 11356833767905579), (Int.negSucc 11356833767905575), (Int.ofNat 1576933568938946), (Int.ofNat 1576933568938962),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf390 : Bracket :=
  ⟨3907, 3908, (Int.ofNat 47308689542126911), (Int.ofNat 47308689542126918), (Int.negSucc 41119452636947972), (Int.negSucc 41119452636947970),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf391 : Bracket :=
  ⟨3916, 3917, (Int.negSucc 17374059911211742), (Int.negSucc 17374059911211740), (Int.ofNat 80310706924338466), (Int.ofNat 80310706924338470),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf392 : Bracket :=
  ⟨3925, 3926, (Int.ofNat 121152327162594364), (Int.ofNat 121152327162594379), (Int.negSucc 21776497589138417), (Int.negSucc 21776497589138405),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf393 : Bracket :=
  ⟨3938, 3939, (Int.negSucc 104299198462018198), (Int.negSucc 104299198462018182), (Int.ofNat 112624907457769770), (Int.ofNat 112624907457769774),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf394 : Bracket :=
  ⟨3952, 3953, (Int.ofNat 90263796166250730), (Int.ofNat 90263796166250734), (Int.negSucc 17043276351731597), (Int.negSucc 17043276351731594),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf395 : Bracket :=
  ⟨3958, 3959, (Int.negSucc 50528773158637472), (Int.negSucc 50528773158637467), (Int.ofNat 24883750827629842), (Int.ofNat 24883750827629851),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf396 : Bracket :=
  ⟨3970, 3971, (Int.ofNat 68377842021450952), (Int.ofNat 68377842021450960), (Int.negSucc 7717603871170867), (Int.negSucc 7717603871170864),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf397 : Bracket :=
  ⟨3981, 3982, (Int.negSucc 488927930198329), (Int.negSucc 488927930198316), (Int.ofNat 4750190976998413), (Int.ofNat 4750190976998429),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf398 : Bracket :=
  ⟨3982, 3983, (Int.ofNat 4750190976998413), (Int.ofNat 4750190976998429), (Int.negSucc 7715077778385074), (Int.negSucc 7715077778385059),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf399 : Bracket :=
  ⟨3993, 3994, (Int.negSucc 53456083287748601), (Int.negSucc 53456083287748586), (Int.ofNat 86982527678043011), (Int.ofNat 86982527678043015),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf400 : Bracket :=
  ⟨4005, 4006, (Int.ofNat 341844521722744976), (Int.ofNat 341844521722744980), (Int.negSucc 4115714771701274), (Int.negSucc 4115714771701271),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf401 : Bracket :=
  ⟨4025, 4026, (Int.negSucc 70703621890699665), (Int.negSucc 70703621890699662), (Int.ofNat 76378318788948817), (Int.ofNat 76378318788948830),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf402 : Bracket :=
  ⟨4032, 4033, (Int.ofNat 22128848910365045), (Int.ofNat 22128848910365047), (Int.negSucc 28393310299217432), (Int.negSucc 28393310299217429),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf403 : Bracket :=
  ⟨4036, 4037, (Int.negSucc 16084143347948765), (Int.negSucc 16084143347948763), (Int.ofNat 54224116829720032), (Int.ofNat 54224116829720035),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf404 : Bracket :=
  ⟨4050, 4051, (Int.ofNat 10200003136976913), (Int.ofNat 10200003136976920), (Int.negSucc 192809084914350528), (Int.negSucc 192809084914350525),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf405 : Bracket :=
  ⟨4066, 4067, (Int.negSucc 22722310851913028), (Int.negSucc 22722310851913025), (Int.ofNat 14040931831111069), (Int.ofNat 14040931831111072),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf406 : Bracket :=
  ⟨4070, 4071, (Int.ofNat 13375015250730424), (Int.ofNat 13375015250730437), (Int.negSucc 3239713058050751), (Int.negSucc 3239713058050747),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf407 : Bracket :=
  ⟨4074, 4075, (Int.negSucc 12471233955463892), (Int.negSucc 12471233955463889), (Int.ofNat 9139316188839843), (Int.ofNat 9139316188839847),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def leaf408 : Bracket :=
  ⟨4082, 4083, (Int.ofNat 50236602858691670), (Int.ofNat 50236602858691677), (Int.negSucc 65834486487702937), (Int.negSucc 65834486487702934),
   by decide +kernel, by decide +kernel, by decide +kernel⟩
noncomputable def node0 : Tree 20 26 2 :=
  Tree.join (Tree.leaf leaf1) (Tree.leaf leaf2) (by decide +kernel)
noncomputable def node1 : Tree 6 26 3 :=
  Tree.join (Tree.leaf leaf0) (node0) (by decide +kernel)
noncomputable def node2 : Tree 43 54 2 :=
  Tree.join (Tree.leaf leaf4) (Tree.leaf leaf5) (by decide +kernel)
noncomputable def node3 : Tree 35 54 3 :=
  Tree.join (Tree.leaf leaf3) (node2) (by decide +kernel)
noncomputable def node4 : Tree 6 54 6 :=
  Tree.join (node1) (node3) (by decide +kernel)
noncomputable def node5 : Tree 71 78 2 :=
  Tree.join (Tree.leaf leaf7) (Tree.leaf leaf8) (by decide +kernel)
noncomputable def node6 : Tree 63 78 3 :=
  Tree.join (Tree.leaf leaf6) (node5) (by decide +kernel)
noncomputable def node7 : Tree 110 119 2 :=
  Tree.join (Tree.leaf leaf10) (Tree.leaf leaf11) (by decide +kernel)
noncomputable def node8 : Tree 94 119 3 :=
  Tree.join (Tree.leaf leaf9) (node7) (by decide +kernel)
noncomputable def node9 : Tree 63 119 6 :=
  Tree.join (node6) (node8) (by decide +kernel)
noncomputable def node10 : Tree 6 119 12 :=
  Tree.join (node4) (node9) (by decide +kernel)
noncomputable def node11 : Tree 135 144 2 :=
  Tree.join (Tree.leaf leaf13) (Tree.leaf leaf14) (by decide +kernel)
noncomputable def node12 : Tree 125 144 3 :=
  Tree.join (Tree.leaf leaf12) (node11) (by decide +kernel)
noncomputable def node13 : Tree 164 171 2 :=
  Tree.join (Tree.leaf leaf16) (Tree.leaf leaf17) (by decide +kernel)
noncomputable def node14 : Tree 151 171 3 :=
  Tree.join (Tree.leaf leaf15) (node13) (by decide +kernel)
noncomputable def node15 : Tree 125 171 6 :=
  Tree.join (node12) (node14) (by decide +kernel)
noncomputable def node16 : Tree 193 199 2 :=
  Tree.join (Tree.leaf leaf19) (Tree.leaf leaf20) (by decide +kernel)
noncomputable def node17 : Tree 179 199 3 :=
  Tree.join (Tree.leaf leaf18) (node16) (by decide +kernel)
noncomputable def node18 : Tree 204 219 2 :=
  Tree.join (Tree.leaf leaf21) (Tree.leaf leaf22) (by decide +kernel)
noncomputable def node19 : Tree 231 240 2 :=
  Tree.join (Tree.leaf leaf23) (Tree.leaf leaf24) (by decide +kernel)
noncomputable def node20 : Tree 204 240 4 :=
  Tree.join (node18) (node19) (by decide +kernel)
noncomputable def node21 : Tree 179 240 7 :=
  Tree.join (node17) (node20) (by decide +kernel)
noncomputable def node22 : Tree 125 240 13 :=
  Tree.join (node15) (node21) (by decide +kernel)
noncomputable def node23 : Tree 6 240 25 :=
  Tree.join (node10) (node22) (by decide +kernel)
noncomputable def node24 : Tree 264 282 2 :=
  Tree.join (Tree.leaf leaf26) (Tree.leaf leaf27) (by decide +kernel)
noncomputable def node25 : Tree 259 282 3 :=
  Tree.join (Tree.leaf leaf25) (node24) (by decide +kernel)
noncomputable def node26 : Tree 296 307 2 :=
  Tree.join (Tree.leaf leaf29) (Tree.leaf leaf30) (by decide +kernel)
noncomputable def node27 : Tree 288 307 3 :=
  Tree.join (Tree.leaf leaf28) (node26) (by decide +kernel)
noncomputable def node28 : Tree 259 307 6 :=
  Tree.join (node25) (node27) (by decide +kernel)
noncomputable def node29 : Tree 324 336 2 :=
  Tree.join (Tree.leaf leaf32) (Tree.leaf leaf33) (by decide +kernel)
noncomputable def node30 : Tree 313 336 3 :=
  Tree.join (Tree.leaf leaf31) (node29) (by decide +kernel)
noncomputable def node31 : Tree 349 357 2 :=
  Tree.join (Tree.leaf leaf34) (Tree.leaf leaf35) (by decide +kernel)
noncomputable def node32 : Tree 364 376 2 :=
  Tree.join (Tree.leaf leaf36) (Tree.leaf leaf37) (by decide +kernel)
noncomputable def node33 : Tree 349 376 4 :=
  Tree.join (node31) (node32) (by decide +kernel)
noncomputable def node34 : Tree 313 376 7 :=
  Tree.join (node30) (node33) (by decide +kernel)
noncomputable def node35 : Tree 259 376 13 :=
  Tree.join (node28) (node34) (by decide +kernel)
noncomputable def node36 : Tree 390 400 2 :=
  Tree.join (Tree.leaf leaf39) (Tree.leaf leaf40) (by decide +kernel)
noncomputable def node37 : Tree 380 400 3 :=
  Tree.join (Tree.leaf leaf38) (node36) (by decide +kernel)
noncomputable def node38 : Tree 427 434 2 :=
  Tree.join (Tree.leaf leaf42) (Tree.leaf leaf43) (by decide +kernel)
noncomputable def node39 : Tree 412 434 3 :=
  Tree.join (Tree.leaf leaf41) (node38) (by decide +kernel)
noncomputable def node40 : Tree 380 434 6 :=
  Tree.join (node37) (node39) (by decide +kernel)
noncomputable def node41 : Tree 455 462 2 :=
  Tree.join (Tree.leaf leaf45) (Tree.leaf leaf46) (by decide +kernel)
noncomputable def node42 : Tree 440 462 3 :=
  Tree.join (Tree.leaf leaf44) (node41) (by decide +kernel)
noncomputable def node43 : Tree 472 477 2 :=
  Tree.join (Tree.leaf leaf47) (Tree.leaf leaf48) (by decide +kernel)
noncomputable def node44 : Tree 496 507 2 :=
  Tree.join (Tree.leaf leaf49) (Tree.leaf leaf50) (by decide +kernel)
noncomputable def node45 : Tree 472 507 4 :=
  Tree.join (node43) (node44) (by decide +kernel)
noncomputable def node46 : Tree 440 507 7 :=
  Tree.join (node42) (node45) (by decide +kernel)
noncomputable def node47 : Tree 380 507 13 :=
  Tree.join (node40) (node46) (by decide +kernel)
noncomputable def node48 : Tree 259 507 26 :=
  Tree.join (node35) (node47) (by decide +kernel)
noncomputable def node49 : Tree 6 507 51 :=
  Tree.join (node23) (node48) (by decide +kernel)
noncomputable def node50 : Tree 527 535 2 :=
  Tree.join (Tree.leaf leaf52) (Tree.leaf leaf53) (by decide +kernel)
noncomputable def node51 : Tree 512 535 3 :=
  Tree.join (Tree.leaf leaf51) (node50) (by decide +kernel)
noncomputable def node52 : Tree 557 570 2 :=
  Tree.join (Tree.leaf leaf55) (Tree.leaf leaf56) (by decide +kernel)
noncomputable def node53 : Tree 537 570 3 :=
  Tree.join (Tree.leaf leaf54) (node52) (by decide +kernel)
noncomputable def node54 : Tree 512 570 6 :=
  Tree.join (node51) (node53) (by decide +kernel)
noncomputable def node55 : Tree 580 590 2 :=
  Tree.join (Tree.leaf leaf58) (Tree.leaf leaf59) (by decide +kernel)
noncomputable def node56 : Tree 575 590 3 :=
  Tree.join (Tree.leaf leaf57) (node55) (by decide +kernel)
noncomputable def node57 : Tree 624 628 2 :=
  Tree.join (Tree.leaf leaf61) (Tree.leaf leaf62) (by decide +kernel)
noncomputable def node58 : Tree 601 628 3 :=
  Tree.join (Tree.leaf leaf60) (node57) (by decide +kernel)
noncomputable def node59 : Tree 575 628 6 :=
  Tree.join (node56) (node58) (by decide +kernel)
noncomputable def node60 : Tree 512 628 12 :=
  Tree.join (node54) (node59) (by decide +kernel)
noncomputable def node61 : Tree 647 664 2 :=
  Tree.join (Tree.leaf leaf64) (Tree.leaf leaf65) (by decide +kernel)
noncomputable def node62 : Tree 632 664 3 :=
  Tree.join (Tree.leaf leaf63) (node61) (by decide +kernel)
noncomputable def node63 : Tree 675 683 2 :=
  Tree.join (Tree.leaf leaf67) (Tree.leaf leaf68) (by decide +kernel)
noncomputable def node64 : Tree 668 683 3 :=
  Tree.join (Tree.leaf leaf66) (node63) (by decide +kernel)
noncomputable def node65 : Tree 632 683 6 :=
  Tree.join (node62) (node64) (by decide +kernel)
noncomputable def node66 : Tree 702 714 2 :=
  Tree.join (Tree.leaf leaf70) (Tree.leaf leaf71) (by decide +kernel)
noncomputable def node67 : Tree 692 714 3 :=
  Tree.join (Tree.leaf leaf69) (node66) (by decide +kernel)
noncomputable def node68 : Tree 722 731 2 :=
  Tree.join (Tree.leaf leaf72) (Tree.leaf leaf73) (by decide +kernel)
noncomputable def node69 : Tree 743 755 2 :=
  Tree.join (Tree.leaf leaf74) (Tree.leaf leaf75) (by decide +kernel)
noncomputable def node70 : Tree 722 755 4 :=
  Tree.join (node68) (node69) (by decide +kernel)
noncomputable def node71 : Tree 692 755 7 :=
  Tree.join (node67) (node70) (by decide +kernel)
noncomputable def node72 : Tree 632 755 13 :=
  Tree.join (node65) (node71) (by decide +kernel)
noncomputable def node73 : Tree 512 755 25 :=
  Tree.join (node60) (node72) (by decide +kernel)
noncomputable def node74 : Tree 770 783 2 :=
  Tree.join (Tree.leaf leaf77) (Tree.leaf leaf78) (by decide +kernel)
noncomputable def node75 : Tree 764 783 3 :=
  Tree.join (Tree.leaf leaf76) (node74) (by decide +kernel)
noncomputable def node76 : Tree 801 808 2 :=
  Tree.join (Tree.leaf leaf80) (Tree.leaf leaf81) (by decide +kernel)
noncomputable def node77 : Tree 790 808 3 :=
  Tree.join (Tree.leaf leaf79) (node76) (by decide +kernel)
noncomputable def node78 : Tree 764 808 6 :=
  Tree.join (node75) (node77) (by decide +kernel)
noncomputable def node79 : Tree 840 851 2 :=
  Tree.join (Tree.leaf leaf83) (Tree.leaf leaf84) (by decide +kernel)
noncomputable def node80 : Tree 821 851 3 :=
  Tree.join (Tree.leaf leaf82) (node79) (by decide +kernel)
noncomputable def node81 : Tree 856 869 2 :=
  Tree.join (Tree.leaf leaf85) (Tree.leaf leaf86) (by decide +kernel)
noncomputable def node82 : Tree 882 890 2 :=
  Tree.join (Tree.leaf leaf87) (Tree.leaf leaf88) (by decide +kernel)
noncomputable def node83 : Tree 856 890 4 :=
  Tree.join (node81) (node82) (by decide +kernel)
noncomputable def node84 : Tree 821 890 7 :=
  Tree.join (node80) (node83) (by decide +kernel)
noncomputable def node85 : Tree 764 890 13 :=
  Tree.join (node78) (node84) (by decide +kernel)
noncomputable def node86 : Tree 907 913 2 :=
  Tree.join (Tree.leaf leaf90) (Tree.leaf leaf91) (by decide +kernel)
noncomputable def node87 : Tree 892 913 3 :=
  Tree.join (Tree.leaf leaf89) (node86) (by decide +kernel)
noncomputable def node88 : Tree 934 946 2 :=
  Tree.join (Tree.leaf leaf93) (Tree.leaf leaf94) (by decide +kernel)
noncomputable def node89 : Tree 927 946 3 :=
  Tree.join (Tree.leaf leaf92) (node88) (by decide +kernel)
noncomputable def node90 : Tree 892 946 6 :=
  Tree.join (node87) (node89) (by decide +kernel)
noncomputable def node91 : Tree 961 971 2 :=
  Tree.join (Tree.leaf leaf96) (Tree.leaf leaf97) (by decide +kernel)
noncomputable def node92 : Tree 951 971 3 :=
  Tree.join (Tree.leaf leaf95) (node91) (by decide +kernel)
noncomputable def node93 : Tree 990 994 2 :=
  Tree.join (Tree.leaf leaf98) (Tree.leaf leaf99) (by decide +kernel)
noncomputable def node94 : Tree 1003 1016 2 :=
  Tree.join (Tree.leaf leaf100) (Tree.leaf leaf101) (by decide +kernel)
noncomputable def node95 : Tree 990 1016 4 :=
  Tree.join (node93) (node94) (by decide +kernel)
noncomputable def node96 : Tree 951 1016 7 :=
  Tree.join (node92) (node95) (by decide +kernel)
noncomputable def node97 : Tree 892 1016 13 :=
  Tree.join (node90) (node96) (by decide +kernel)
noncomputable def node98 : Tree 764 1016 26 :=
  Tree.join (node85) (node97) (by decide +kernel)
noncomputable def node99 : Tree 512 1016 51 :=
  Tree.join (node73) (node98) (by decide +kernel)
noncomputable def node100 : Tree 6 1016 102 :=
  Tree.join (node49) (node99) (by decide +kernel)
noncomputable def node101 : Tree 1030 1054 2 :=
  Tree.join (Tree.leaf leaf103) (Tree.leaf leaf104) (by decide +kernel)
noncomputable def node102 : Tree 1026 1054 3 :=
  Tree.join (Tree.leaf leaf102) (node101) (by decide +kernel)
noncomputable def node103 : Tree 1062 1069 2 :=
  Tree.join (Tree.leaf leaf106) (Tree.leaf leaf107) (by decide +kernel)
noncomputable def node104 : Tree 1055 1069 3 :=
  Tree.join (Tree.leaf leaf105) (node103) (by decide +kernel)
noncomputable def node105 : Tree 1026 1069 6 :=
  Tree.join (node102) (node104) (by decide +kernel)
noncomputable def node106 : Tree 1087 1101 2 :=
  Tree.join (Tree.leaf leaf109) (Tree.leaf leaf110) (by decide +kernel)
noncomputable def node107 : Tree 1082 1101 3 :=
  Tree.join (Tree.leaf leaf108) (node106) (by decide +kernel)
noncomputable def node108 : Tree 1129 1133 2 :=
  Tree.join (Tree.leaf leaf112) (Tree.leaf leaf113) (by decide +kernel)
noncomputable def node109 : Tree 1112 1133 3 :=
  Tree.join (Tree.leaf leaf111) (node108) (by decide +kernel)
noncomputable def node110 : Tree 1082 1133 6 :=
  Tree.join (node107) (node109) (by decide +kernel)
noncomputable def node111 : Tree 1026 1133 12 :=
  Tree.join (node105) (node110) (by decide +kernel)
noncomputable def node112 : Tree 1159 1163 2 :=
  Tree.join (Tree.leaf leaf115) (Tree.leaf leaf116) (by decide +kernel)
noncomputable def node113 : Tree 1149 1163 3 :=
  Tree.join (Tree.leaf leaf114) (node112) (by decide +kernel)
noncomputable def node114 : Tree 1194 1203 2 :=
  Tree.join (Tree.leaf leaf118) (Tree.leaf leaf119) (by decide +kernel)
noncomputable def node115 : Tree 1173 1203 3 :=
  Tree.join (Tree.leaf leaf117) (node114) (by decide +kernel)
noncomputable def node116 : Tree 1149 1203 6 :=
  Tree.join (node113) (node115) (by decide +kernel)
noncomputable def node117 : Tree 1213 1225 2 :=
  Tree.join (Tree.leaf leaf121) (Tree.leaf leaf122) (by decide +kernel)
noncomputable def node118 : Tree 1206 1225 3 :=
  Tree.join (Tree.leaf leaf120) (node117) (by decide +kernel)
noncomputable def node119 : Tree 1232 1249 2 :=
  Tree.join (Tree.leaf leaf123) (Tree.leaf leaf124) (by decide +kernel)
noncomputable def node120 : Tree 1256 1273 2 :=
  Tree.join (Tree.leaf leaf125) (Tree.leaf leaf126) (by decide +kernel)
noncomputable def node121 : Tree 1232 1273 4 :=
  Tree.join (node119) (node120) (by decide +kernel)
noncomputable def node122 : Tree 1206 1273 7 :=
  Tree.join (node118) (node121) (by decide +kernel)
noncomputable def node123 : Tree 1149 1273 13 :=
  Tree.join (node116) (node122) (by decide +kernel)
noncomputable def node124 : Tree 1026 1273 25 :=
  Tree.join (node111) (node123) (by decide +kernel)
noncomputable def node125 : Tree 1288 1290 2 :=
  Tree.join (Tree.leaf leaf128) (Tree.leaf leaf129) (by decide +kernel)
noncomputable def node126 : Tree 1278 1290 3 :=
  Tree.join (Tree.leaf leaf127) (node125) (by decide +kernel)
noncomputable def node127 : Tree 1312 1321 2 :=
  Tree.join (Tree.leaf leaf131) (Tree.leaf leaf132) (by decide +kernel)
noncomputable def node128 : Tree 1296 1321 3 :=
  Tree.join (Tree.leaf leaf130) (node127) (by decide +kernel)
noncomputable def node129 : Tree 1278 1321 6 :=
  Tree.join (node126) (node128) (by decide +kernel)
noncomputable def node130 : Tree 1340 1356 2 :=
  Tree.join (Tree.leaf leaf134) (Tree.leaf leaf135) (by decide +kernel)
noncomputable def node131 : Tree 1327 1356 3 :=
  Tree.join (Tree.leaf leaf133) (node130) (by decide +kernel)
noncomputable def node132 : Tree 1365 1374 2 :=
  Tree.join (Tree.leaf leaf136) (Tree.leaf leaf137) (by decide +kernel)
noncomputable def node133 : Tree 1392 1398 2 :=
  Tree.join (Tree.leaf leaf138) (Tree.leaf leaf139) (by decide +kernel)
noncomputable def node134 : Tree 1365 1398 4 :=
  Tree.join (node132) (node133) (by decide +kernel)
noncomputable def node135 : Tree 1327 1398 7 :=
  Tree.join (node131) (node134) (by decide +kernel)
noncomputable def node136 : Tree 1278 1398 13 :=
  Tree.join (node129) (node135) (by decide +kernel)
noncomputable def node137 : Tree 1415 1425 2 :=
  Tree.join (Tree.leaf leaf141) (Tree.leaf leaf142) (by decide +kernel)
noncomputable def node138 : Tree 1401 1425 3 :=
  Tree.join (Tree.leaf leaf140) (node137) (by decide +kernel)
noncomputable def node139 : Tree 1448 1459 2 :=
  Tree.join (Tree.leaf leaf144) (Tree.leaf leaf145) (by decide +kernel)
noncomputable def node140 : Tree 1440 1459 3 :=
  Tree.join (Tree.leaf leaf143) (node139) (by decide +kernel)
noncomputable def node141 : Tree 1401 1459 6 :=
  Tree.join (node138) (node140) (by decide +kernel)
noncomputable def node142 : Tree 1475 1487 2 :=
  Tree.join (Tree.leaf leaf147) (Tree.leaf leaf148) (by decide +kernel)
noncomputable def node143 : Tree 1465 1487 3 :=
  Tree.join (Tree.leaf leaf146) (node142) (by decide +kernel)
noncomputable def node144 : Tree 1494 1509 2 :=
  Tree.join (Tree.leaf leaf149) (Tree.leaf leaf150) (by decide +kernel)
noncomputable def node145 : Tree 1513 1528 2 :=
  Tree.join (Tree.leaf leaf151) (Tree.leaf leaf152) (by decide +kernel)
noncomputable def node146 : Tree 1494 1528 4 :=
  Tree.join (node144) (node145) (by decide +kernel)
noncomputable def node147 : Tree 1465 1528 7 :=
  Tree.join (node143) (node146) (by decide +kernel)
noncomputable def node148 : Tree 1401 1528 13 :=
  Tree.join (node141) (node147) (by decide +kernel)
noncomputable def node149 : Tree 1278 1528 26 :=
  Tree.join (node136) (node148) (by decide +kernel)
noncomputable def node150 : Tree 1026 1528 51 :=
  Tree.join (node124) (node149) (by decide +kernel)
noncomputable def node151 : Tree 1546 1553 2 :=
  Tree.join (Tree.leaf leaf154) (Tree.leaf leaf155) (by decide +kernel)
noncomputable def node152 : Tree 1538 1553 3 :=
  Tree.join (Tree.leaf leaf153) (node151) (by decide +kernel)
noncomputable def node153 : Tree 1576 1586 2 :=
  Tree.join (Tree.leaf leaf157) (Tree.leaf leaf158) (by decide +kernel)
noncomputable def node154 : Tree 1568 1586 3 :=
  Tree.join (Tree.leaf leaf156) (node153) (by decide +kernel)
noncomputable def node155 : Tree 1538 1586 6 :=
  Tree.join (node152) (node154) (by decide +kernel)
noncomputable def node156 : Tree 1605 1615 2 :=
  Tree.join (Tree.leaf leaf160) (Tree.leaf leaf161) (by decide +kernel)
noncomputable def node157 : Tree 1595 1615 3 :=
  Tree.join (Tree.leaf leaf159) (node156) (by decide +kernel)
noncomputable def node158 : Tree 1635 1640 2 :=
  Tree.join (Tree.leaf leaf163) (Tree.leaf leaf164) (by decide +kernel)
noncomputable def node159 : Tree 1629 1640 3 :=
  Tree.join (Tree.leaf leaf162) (node158) (by decide +kernel)
noncomputable def node160 : Tree 1595 1640 6 :=
  Tree.join (node157) (node159) (by decide +kernel)
noncomputable def node161 : Tree 1538 1640 12 :=
  Tree.join (node155) (node160) (by decide +kernel)
noncomputable def node162 : Tree 1660 1675 2 :=
  Tree.join (Tree.leaf leaf166) (Tree.leaf leaf167) (by decide +kernel)
noncomputable def node163 : Tree 1649 1675 3 :=
  Tree.join (Tree.leaf leaf165) (node162) (by decide +kernel)
noncomputable def node164 : Tree 1693 1701 2 :=
  Tree.join (Tree.leaf leaf169) (Tree.leaf leaf170) (by decide +kernel)
noncomputable def node165 : Tree 1687 1701 3 :=
  Tree.join (Tree.leaf leaf168) (node164) (by decide +kernel)
noncomputable def node166 : Tree 1649 1701 6 :=
  Tree.join (node163) (node165) (by decide +kernel)
noncomputable def node167 : Tree 1721 1742 2 :=
  Tree.join (Tree.leaf leaf172) (Tree.leaf leaf173) (by decide +kernel)
noncomputable def node168 : Tree 1715 1742 3 :=
  Tree.join (Tree.leaf leaf171) (node167) (by decide +kernel)
noncomputable def node169 : Tree 1752 1764 2 :=
  Tree.join (Tree.leaf leaf174) (Tree.leaf leaf175) (by decide +kernel)
noncomputable def node170 : Tree 1769 1785 2 :=
  Tree.join (Tree.leaf leaf176) (Tree.leaf leaf177) (by decide +kernel)
noncomputable def node171 : Tree 1752 1785 4 :=
  Tree.join (node169) (node170) (by decide +kernel)
noncomputable def node172 : Tree 1715 1785 7 :=
  Tree.join (node168) (node171) (by decide +kernel)
noncomputable def node173 : Tree 1649 1785 13 :=
  Tree.join (node166) (node172) (by decide +kernel)
noncomputable def node174 : Tree 1538 1785 25 :=
  Tree.join (node161) (node173) (by decide +kernel)
noncomputable def node175 : Tree 1797 1808 2 :=
  Tree.join (Tree.leaf leaf179) (Tree.leaf leaf180) (by decide +kernel)
noncomputable def node176 : Tree 1789 1808 3 :=
  Tree.join (Tree.leaf leaf178) (node175) (by decide +kernel)
noncomputable def node177 : Tree 1822 1836 2 :=
  Tree.join (Tree.leaf leaf182) (Tree.leaf leaf183) (by decide +kernel)
noncomputable def node178 : Tree 1813 1836 3 :=
  Tree.join (Tree.leaf leaf181) (node177) (by decide +kernel)
noncomputable def node179 : Tree 1789 1836 6 :=
  Tree.join (node176) (node178) (by decide +kernel)
noncomputable def node180 : Tree 1854 1863 2 :=
  Tree.join (Tree.leaf leaf185) (Tree.leaf leaf186) (by decide +kernel)
noncomputable def node181 : Tree 1843 1863 3 :=
  Tree.join (Tree.leaf leaf184) (node180) (by decide +kernel)
noncomputable def node182 : Tree 1878 1884 2 :=
  Tree.join (Tree.leaf leaf187) (Tree.leaf leaf188) (by decide +kernel)
noncomputable def node183 : Tree 1893 1908 2 :=
  Tree.join (Tree.leaf leaf189) (Tree.leaf leaf190) (by decide +kernel)
noncomputable def node184 : Tree 1878 1908 4 :=
  Tree.join (node182) (node183) (by decide +kernel)
noncomputable def node185 : Tree 1843 1908 7 :=
  Tree.join (node181) (node184) (by decide +kernel)
noncomputable def node186 : Tree 1789 1908 13 :=
  Tree.join (node179) (node185) (by decide +kernel)
noncomputable def node187 : Tree 1927 1932 2 :=
  Tree.join (Tree.leaf leaf192) (Tree.leaf leaf193) (by decide +kernel)
noncomputable def node188 : Tree 1916 1932 3 :=
  Tree.join (Tree.leaf leaf191) (node187) (by decide +kernel)
noncomputable def node189 : Tree 1953 1961 2 :=
  Tree.join (Tree.leaf leaf195) (Tree.leaf leaf196) (by decide +kernel)
noncomputable def node190 : Tree 1944 1961 3 :=
  Tree.join (Tree.leaf leaf194) (node189) (by decide +kernel)
noncomputable def node191 : Tree 1916 1961 6 :=
  Tree.join (node188) (node190) (by decide +kernel)
noncomputable def node192 : Tree 1988 1996 2 :=
  Tree.join (Tree.leaf leaf198) (Tree.leaf leaf199) (by decide +kernel)
noncomputable def node193 : Tree 1977 1996 3 :=
  Tree.join (Tree.leaf leaf197) (node192) (by decide +kernel)
noncomputable def node194 : Tree 2009 2021 2 :=
  Tree.join (Tree.leaf leaf200) (Tree.leaf leaf201) (by decide +kernel)
noncomputable def node195 : Tree 2028 2038 2 :=
  Tree.join (Tree.leaf leaf202) (Tree.leaf leaf203) (by decide +kernel)
noncomputable def node196 : Tree 2009 2038 4 :=
  Tree.join (node194) (node195) (by decide +kernel)
noncomputable def node197 : Tree 1977 2038 7 :=
  Tree.join (node193) (node196) (by decide +kernel)
noncomputable def node198 : Tree 1916 2038 13 :=
  Tree.join (node191) (node197) (by decide +kernel)
noncomputable def node199 : Tree 1789 2038 26 :=
  Tree.join (node186) (node198) (by decide +kernel)
noncomputable def node200 : Tree 1538 2038 51 :=
  Tree.join (node174) (node199) (by decide +kernel)
noncomputable def node201 : Tree 1026 2038 102 :=
  Tree.join (node150) (node200) (by decide +kernel)
noncomputable def node202 : Tree 6 2038 204 :=
  Tree.join (node100) (node201) (by decide +kernel)
noncomputable def node203 : Tree 2054 2066 2 :=
  Tree.join (Tree.leaf leaf205) (Tree.leaf leaf206) (by decide +kernel)
noncomputable def node204 : Tree 2045 2066 3 :=
  Tree.join (Tree.leaf leaf204) (node203) (by decide +kernel)
noncomputable def node205 : Tree 2087 2102 2 :=
  Tree.join (Tree.leaf leaf208) (Tree.leaf leaf209) (by decide +kernel)
noncomputable def node206 : Tree 2075 2102 3 :=
  Tree.join (Tree.leaf leaf207) (node205) (by decide +kernel)
noncomputable def node207 : Tree 2045 2102 6 :=
  Tree.join (node204) (node206) (by decide +kernel)
noncomputable def node208 : Tree 2118 2131 2 :=
  Tree.join (Tree.leaf leaf211) (Tree.leaf leaf212) (by decide +kernel)
noncomputable def node209 : Tree 2107 2131 3 :=
  Tree.join (Tree.leaf leaf210) (node208) (by decide +kernel)
noncomputable def node210 : Tree 2149 2154 2 :=
  Tree.join (Tree.leaf leaf214) (Tree.leaf leaf215) (by decide +kernel)
noncomputable def node211 : Tree 2139 2154 3 :=
  Tree.join (Tree.leaf leaf213) (node210) (by decide +kernel)
noncomputable def node212 : Tree 2107 2154 6 :=
  Tree.join (node209) (node211) (by decide +kernel)
noncomputable def node213 : Tree 2045 2154 12 :=
  Tree.join (node207) (node212) (by decide +kernel)
noncomputable def node214 : Tree 2175 2189 2 :=
  Tree.join (Tree.leaf leaf217) (Tree.leaf leaf218) (by decide +kernel)
noncomputable def node215 : Tree 2166 2189 3 :=
  Tree.join (Tree.leaf leaf216) (node214) (by decide +kernel)
noncomputable def node216 : Tree 2200 2216 2 :=
  Tree.join (Tree.leaf leaf220) (Tree.leaf leaf221) (by decide +kernel)
noncomputable def node217 : Tree 2191 2216 3 :=
  Tree.join (Tree.leaf leaf219) (node216) (by decide +kernel)
noncomputable def node218 : Tree 2166 2216 6 :=
  Tree.join (node215) (node217) (by decide +kernel)
noncomputable def node219 : Tree 2237 2240 2 :=
  Tree.join (Tree.leaf leaf223) (Tree.leaf leaf224) (by decide +kernel)
noncomputable def node220 : Tree 2224 2240 3 :=
  Tree.join (Tree.leaf leaf222) (node219) (by decide +kernel)
noncomputable def node221 : Tree 2244 2266 2 :=
  Tree.join (Tree.leaf leaf225) (Tree.leaf leaf226) (by decide +kernel)
noncomputable def node222 : Tree 2283 2293 2 :=
  Tree.join (Tree.leaf leaf227) (Tree.leaf leaf228) (by decide +kernel)
noncomputable def node223 : Tree 2244 2293 4 :=
  Tree.join (node221) (node222) (by decide +kernel)
noncomputable def node224 : Tree 2224 2293 7 :=
  Tree.join (node220) (node223) (by decide +kernel)
noncomputable def node225 : Tree 2166 2293 13 :=
  Tree.join (node218) (node224) (by decide +kernel)
noncomputable def node226 : Tree 2045 2293 25 :=
  Tree.join (node213) (node225) (by decide +kernel)
noncomputable def node227 : Tree 2310 2319 2 :=
  Tree.join (Tree.leaf leaf230) (Tree.leaf leaf231) (by decide +kernel)
noncomputable def node228 : Tree 2300 2319 3 :=
  Tree.join (Tree.leaf leaf229) (node227) (by decide +kernel)
noncomputable def node229 : Tree 2342 2353 2 :=
  Tree.join (Tree.leaf leaf233) (Tree.leaf leaf234) (by decide +kernel)
noncomputable def node230 : Tree 2325 2353 3 :=
  Tree.join (Tree.leaf leaf232) (node229) (by decide +kernel)
noncomputable def node231 : Tree 2300 2353 6 :=
  Tree.join (node228) (node230) (by decide +kernel)
noncomputable def node232 : Tree 2360 2381 2 :=
  Tree.join (Tree.leaf leaf236) (Tree.leaf leaf237) (by decide +kernel)
noncomputable def node233 : Tree 2357 2381 3 :=
  Tree.join (Tree.leaf leaf235) (node232) (by decide +kernel)
noncomputable def node234 : Tree 2394 2397 2 :=
  Tree.join (Tree.leaf leaf238) (Tree.leaf leaf239) (by decide +kernel)
noncomputable def node235 : Tree 2407 2416 2 :=
  Tree.join (Tree.leaf leaf240) (Tree.leaf leaf241) (by decide +kernel)
noncomputable def node236 : Tree 2394 2416 4 :=
  Tree.join (node234) (node235) (by decide +kernel)
noncomputable def node237 : Tree 2357 2416 7 :=
  Tree.join (node233) (node236) (by decide +kernel)
noncomputable def node238 : Tree 2300 2416 13 :=
  Tree.join (node231) (node237) (by decide +kernel)
noncomputable def node239 : Tree 2433 2446 2 :=
  Tree.join (Tree.leaf leaf243) (Tree.leaf leaf244) (by decide +kernel)
noncomputable def node240 : Tree 2422 2446 3 :=
  Tree.join (Tree.leaf leaf242) (node239) (by decide +kernel)
noncomputable def node241 : Tree 2462 2481 2 :=
  Tree.join (Tree.leaf leaf246) (Tree.leaf leaf247) (by decide +kernel)
noncomputable def node242 : Tree 2456 2481 3 :=
  Tree.join (Tree.leaf leaf245) (node241) (by decide +kernel)
noncomputable def node243 : Tree 2422 2481 6 :=
  Tree.join (node240) (node242) (by decide +kernel)
noncomputable def node244 : Tree 2499 2509 2 :=
  Tree.join (Tree.leaf leaf249) (Tree.leaf leaf250) (by decide +kernel)
noncomputable def node245 : Tree 2484 2509 3 :=
  Tree.join (Tree.leaf leaf248) (node244) (by decide +kernel)
noncomputable def node246 : Tree 2515 2526 2 :=
  Tree.join (Tree.leaf leaf251) (Tree.leaf leaf252) (by decide +kernel)
noncomputable def node247 : Tree 2539 2546 2 :=
  Tree.join (Tree.leaf leaf253) (Tree.leaf leaf254) (by decide +kernel)
noncomputable def node248 : Tree 2515 2546 4 :=
  Tree.join (node246) (node247) (by decide +kernel)
noncomputable def node249 : Tree 2484 2546 7 :=
  Tree.join (node245) (node248) (by decide +kernel)
noncomputable def node250 : Tree 2422 2546 13 :=
  Tree.join (node243) (node249) (by decide +kernel)
noncomputable def node251 : Tree 2300 2546 26 :=
  Tree.join (node238) (node250) (by decide +kernel)
noncomputable def node252 : Tree 2045 2546 51 :=
  Tree.join (node226) (node251) (by decide +kernel)
noncomputable def node253 : Tree 2564 2572 2 :=
  Tree.join (Tree.leaf leaf256) (Tree.leaf leaf257) (by decide +kernel)
noncomputable def node254 : Tree 2553 2572 3 :=
  Tree.join (Tree.leaf leaf255) (node253) (by decide +kernel)
noncomputable def node255 : Tree 2594 2615 2 :=
  Tree.join (Tree.leaf leaf259) (Tree.leaf leaf260) (by decide +kernel)
noncomputable def node256 : Tree 2582 2615 3 :=
  Tree.join (Tree.leaf leaf258) (node255) (by decide +kernel)
noncomputable def node257 : Tree 2553 2615 6 :=
  Tree.join (node254) (node256) (by decide +kernel)
noncomputable def node258 : Tree 2630 2641 2 :=
  Tree.join (Tree.leaf leaf262) (Tree.leaf leaf263) (by decide +kernel)
noncomputable def node259 : Tree 2623 2641 3 :=
  Tree.join (Tree.leaf leaf261) (node258) (by decide +kernel)
noncomputable def node260 : Tree 2656 2669 2 :=
  Tree.join (Tree.leaf leaf265) (Tree.leaf leaf266) (by decide +kernel)
noncomputable def node261 : Tree 2647 2669 3 :=
  Tree.join (Tree.leaf leaf264) (node260) (by decide +kernel)
noncomputable def node262 : Tree 2623 2669 6 :=
  Tree.join (node259) (node261) (by decide +kernel)
noncomputable def node263 : Tree 2553 2669 12 :=
  Tree.join (node257) (node262) (by decide +kernel)
noncomputable def node264 : Tree 2687 2704 2 :=
  Tree.join (Tree.leaf leaf268) (Tree.leaf leaf269) (by decide +kernel)
noncomputable def node265 : Tree 2682 2704 3 :=
  Tree.join (Tree.leaf leaf267) (node264) (by decide +kernel)
noncomputable def node266 : Tree 2715 2725 2 :=
  Tree.join (Tree.leaf leaf271) (Tree.leaf leaf272) (by decide +kernel)
noncomputable def node267 : Tree 2710 2725 3 :=
  Tree.join (Tree.leaf leaf270) (node266) (by decide +kernel)
noncomputable def node268 : Tree 2682 2725 6 :=
  Tree.join (node265) (node267) (by decide +kernel)
noncomputable def node269 : Tree 2748 2758 2 :=
  Tree.join (Tree.leaf leaf274) (Tree.leaf leaf275) (by decide +kernel)
noncomputable def node270 : Tree 2733 2758 3 :=
  Tree.join (Tree.leaf leaf273) (node269) (by decide +kernel)
noncomputable def node271 : Tree 2762 2778 2 :=
  Tree.join (Tree.leaf leaf276) (Tree.leaf leaf277) (by decide +kernel)
noncomputable def node272 : Tree 2784 2793 2 :=
  Tree.join (Tree.leaf leaf278) (Tree.leaf leaf279) (by decide +kernel)
noncomputable def node273 : Tree 2762 2793 4 :=
  Tree.join (node271) (node272) (by decide +kernel)
noncomputable def node274 : Tree 2733 2793 7 :=
  Tree.join (node270) (node273) (by decide +kernel)
noncomputable def node275 : Tree 2682 2793 13 :=
  Tree.join (node268) (node274) (by decide +kernel)
noncomputable def node276 : Tree 2553 2793 25 :=
  Tree.join (node263) (node275) (by decide +kernel)
noncomputable def node277 : Tree 2813 2827 2 :=
  Tree.join (Tree.leaf leaf281) (Tree.leaf leaf282) (by decide +kernel)
noncomputable def node278 : Tree 2803 2827 3 :=
  Tree.join (Tree.leaf leaf280) (node277) (by decide +kernel)
noncomputable def node279 : Tree 2844 2862 2 :=
  Tree.join (Tree.leaf leaf284) (Tree.leaf leaf285) (by decide +kernel)
noncomputable def node280 : Tree 2834 2862 3 :=
  Tree.join (Tree.leaf leaf283) (node279) (by decide +kernel)
noncomputable def node281 : Tree 2803 2862 6 :=
  Tree.join (node278) (node280) (by decide +kernel)
noncomputable def node282 : Tree 2882 2887 2 :=
  Tree.join (Tree.leaf leaf287) (Tree.leaf leaf288) (by decide +kernel)
noncomputable def node283 : Tree 2871 2887 3 :=
  Tree.join (Tree.leaf leaf286) (node282) (by decide +kernel)
noncomputable def node284 : Tree 2902 2915 2 :=
  Tree.join (Tree.leaf leaf289) (Tree.leaf leaf290) (by decide +kernel)
noncomputable def node285 : Tree 2919 2928 2 :=
  Tree.join (Tree.leaf leaf291) (Tree.leaf leaf292) (by decide +kernel)
noncomputable def node286 : Tree 2902 2928 4 :=
  Tree.join (node284) (node285) (by decide +kernel)
noncomputable def node287 : Tree 2871 2928 7 :=
  Tree.join (node283) (node286) (by decide +kernel)
noncomputable def node288 : Tree 2803 2928 13 :=
  Tree.join (node281) (node287) (by decide +kernel)
noncomputable def node289 : Tree 2948 2958 2 :=
  Tree.join (Tree.leaf leaf294) (Tree.leaf leaf295) (by decide +kernel)
noncomputable def node290 : Tree 2938 2958 3 :=
  Tree.join (Tree.leaf leaf293) (node289) (by decide +kernel)
noncomputable def node291 : Tree 2976 2986 2 :=
  Tree.join (Tree.leaf leaf297) (Tree.leaf leaf298) (by decide +kernel)
noncomputable def node292 : Tree 2962 2986 3 :=
  Tree.join (Tree.leaf leaf296) (node291) (by decide +kernel)
noncomputable def node293 : Tree 2938 2986 6 :=
  Tree.join (node290) (node292) (by decide +kernel)
noncomputable def node294 : Tree 3013 3019 2 :=
  Tree.join (Tree.leaf leaf300) (Tree.leaf leaf301) (by decide +kernel)
noncomputable def node295 : Tree 2996 3019 3 :=
  Tree.join (Tree.leaf leaf299) (node294) (by decide +kernel)
noncomputable def node296 : Tree 3032 3043 2 :=
  Tree.join (Tree.leaf leaf302) (Tree.leaf leaf303) (by decide +kernel)
noncomputable def node297 : Tree 3048 3060 2 :=
  Tree.join (Tree.leaf leaf304) (Tree.leaf leaf305) (by decide +kernel)
noncomputable def node298 : Tree 3032 3060 4 :=
  Tree.join (node296) (node297) (by decide +kernel)
noncomputable def node299 : Tree 2996 3060 7 :=
  Tree.join (node295) (node298) (by decide +kernel)
noncomputable def node300 : Tree 2938 3060 13 :=
  Tree.join (node293) (node299) (by decide +kernel)
noncomputable def node301 : Tree 2803 3060 26 :=
  Tree.join (node288) (node300) (by decide +kernel)
noncomputable def node302 : Tree 2553 3060 51 :=
  Tree.join (node276) (node301) (by decide +kernel)
noncomputable def node303 : Tree 2045 3060 102 :=
  Tree.join (node252) (node302) (by decide +kernel)
noncomputable def node304 : Tree 3072 3084 2 :=
  Tree.join (Tree.leaf leaf307) (Tree.leaf leaf308) (by decide +kernel)
noncomputable def node305 : Tree 3062 3084 3 :=
  Tree.join (Tree.leaf leaf306) (node304) (by decide +kernel)
noncomputable def node306 : Tree 3109 3122 2 :=
  Tree.join (Tree.leaf leaf310) (Tree.leaf leaf311) (by decide +kernel)
noncomputable def node307 : Tree 3090 3122 3 :=
  Tree.join (Tree.leaf leaf309) (node306) (by decide +kernel)
noncomputable def node308 : Tree 3062 3122 6 :=
  Tree.join (node305) (node307) (by decide +kernel)
noncomputable def node309 : Tree 3133 3141 2 :=
  Tree.join (Tree.leaf leaf313) (Tree.leaf leaf314) (by decide +kernel)
noncomputable def node310 : Tree 3127 3141 3 :=
  Tree.join (Tree.leaf leaf312) (node309) (by decide +kernel)
noncomputable def node311 : Tree 3170 3180 2 :=
  Tree.join (Tree.leaf leaf316) (Tree.leaf leaf317) (by decide +kernel)
noncomputable def node312 : Tree 3158 3180 3 :=
  Tree.join (Tree.leaf leaf315) (node311) (by decide +kernel)
noncomputable def node313 : Tree 3127 3180 6 :=
  Tree.join (node310) (node312) (by decide +kernel)
noncomputable def node314 : Tree 3062 3180 12 :=
  Tree.join (node308) (node313) (by decide +kernel)
noncomputable def node315 : Tree 3201 3211 2 :=
  Tree.join (Tree.leaf leaf319) (Tree.leaf leaf320) (by decide +kernel)
noncomputable def node316 : Tree 3188 3211 3 :=
  Tree.join (Tree.leaf leaf318) (node315) (by decide +kernel)
noncomputable def node317 : Tree 3233 3245 2 :=
  Tree.join (Tree.leaf leaf322) (Tree.leaf leaf323) (by decide +kernel)
noncomputable def node318 : Tree 3218 3245 3 :=
  Tree.join (Tree.leaf leaf321) (node317) (by decide +kernel)
noncomputable def node319 : Tree 3188 3245 6 :=
  Tree.join (node316) (node318) (by decide +kernel)
noncomputable def node320 : Tree 3259 3271 2 :=
  Tree.join (Tree.leaf leaf325) (Tree.leaf leaf326) (by decide +kernel)
noncomputable def node321 : Tree 3253 3271 3 :=
  Tree.join (Tree.leaf leaf324) (node320) (by decide +kernel)
noncomputable def node322 : Tree 3275 3287 2 :=
  Tree.join (Tree.leaf leaf327) (Tree.leaf leaf328) (by decide +kernel)
noncomputable def node323 : Tree 3299 3304 2 :=
  Tree.join (Tree.leaf leaf329) (Tree.leaf leaf330) (by decide +kernel)
noncomputable def node324 : Tree 3275 3304 4 :=
  Tree.join (node322) (node323) (by decide +kernel)
noncomputable def node325 : Tree 3253 3304 7 :=
  Tree.join (node321) (node324) (by decide +kernel)
noncomputable def node326 : Tree 3188 3304 13 :=
  Tree.join (node319) (node325) (by decide +kernel)
noncomputable def node327 : Tree 3062 3304 25 :=
  Tree.join (node314) (node326) (by decide +kernel)
noncomputable def node328 : Tree 3326 3334 2 :=
  Tree.join (Tree.leaf leaf332) (Tree.leaf leaf333) (by decide +kernel)
noncomputable def node329 : Tree 3318 3334 3 :=
  Tree.join (Tree.leaf leaf331) (node328) (by decide +kernel)
noncomputable def node330 : Tree 3356 3366 2 :=
  Tree.join (Tree.leaf leaf335) (Tree.leaf leaf336) (by decide +kernel)
noncomputable def node331 : Tree 3343 3366 3 :=
  Tree.join (Tree.leaf leaf334) (node330) (by decide +kernel)
noncomputable def node332 : Tree 3318 3366 6 :=
  Tree.join (node329) (node331) (by decide +kernel)
noncomputable def node333 : Tree 3390 3400 2 :=
  Tree.join (Tree.leaf leaf338) (Tree.leaf leaf339) (by decide +kernel)
noncomputable def node334 : Tree 3378 3400 3 :=
  Tree.join (Tree.leaf leaf337) (node333) (by decide +kernel)
noncomputable def node335 : Tree 3409 3417 2 :=
  Tree.join (Tree.leaf leaf340) (Tree.leaf leaf341) (by decide +kernel)
noncomputable def node336 : Tree 3421 3446 2 :=
  Tree.join (Tree.leaf leaf342) (Tree.leaf leaf343) (by decide +kernel)
noncomputable def node337 : Tree 3409 3446 4 :=
  Tree.join (node335) (node336) (by decide +kernel)
noncomputable def node338 : Tree 3378 3446 7 :=
  Tree.join (node334) (node337) (by decide +kernel)
noncomputable def node339 : Tree 3318 3446 13 :=
  Tree.join (node332) (node338) (by decide +kernel)
noncomputable def node340 : Tree 3458 3470 2 :=
  Tree.join (Tree.leaf leaf345) (Tree.leaf leaf346) (by decide +kernel)
noncomputable def node341 : Tree 3448 3470 3 :=
  Tree.join (Tree.leaf leaf344) (node340) (by decide +kernel)
noncomputable def node342 : Tree 3491 3497 2 :=
  Tree.join (Tree.leaf leaf348) (Tree.leaf leaf349) (by decide +kernel)
noncomputable def node343 : Tree 3478 3497 3 :=
  Tree.join (Tree.leaf leaf347) (node342) (by decide +kernel)
noncomputable def node344 : Tree 3448 3497 6 :=
  Tree.join (node341) (node343) (by decide +kernel)
noncomputable def node345 : Tree 3522 3528 2 :=
  Tree.join (Tree.leaf leaf351) (Tree.leaf leaf352) (by decide +kernel)
noncomputable def node346 : Tree 3509 3528 3 :=
  Tree.join (Tree.leaf leaf350) (node345) (by decide +kernel)
noncomputable def node347 : Tree 3539 3553 2 :=
  Tree.join (Tree.leaf leaf353) (Tree.leaf leaf354) (by decide +kernel)
noncomputable def node348 : Tree 3563 3570 2 :=
  Tree.join (Tree.leaf leaf355) (Tree.leaf leaf356) (by decide +kernel)
noncomputable def node349 : Tree 3539 3570 4 :=
  Tree.join (node347) (node348) (by decide +kernel)
noncomputable def node350 : Tree 3509 3570 7 :=
  Tree.join (node346) (node349) (by decide +kernel)
noncomputable def node351 : Tree 3448 3570 13 :=
  Tree.join (node344) (node350) (by decide +kernel)
noncomputable def node352 : Tree 3318 3570 26 :=
  Tree.join (node339) (node351) (by decide +kernel)
noncomputable def node353 : Tree 3062 3570 51 :=
  Tree.join (node327) (node352) (by decide +kernel)
noncomputable def node354 : Tree 3587 3599 2 :=
  Tree.join (Tree.leaf leaf358) (Tree.leaf leaf359) (by decide +kernel)
noncomputable def node355 : Tree 3574 3599 3 :=
  Tree.join (Tree.leaf leaf357) (node354) (by decide +kernel)
noncomputable def node356 : Tree 3621 3631 2 :=
  Tree.join (Tree.leaf leaf361) (Tree.leaf leaf362) (by decide +kernel)
noncomputable def node357 : Tree 3608 3631 3 :=
  Tree.join (Tree.leaf leaf360) (node356) (by decide +kernel)
noncomputable def node358 : Tree 3574 3631 6 :=
  Tree.join (node355) (node357) (by decide +kernel)
noncomputable def node359 : Tree 3649 3658 2 :=
  Tree.join (Tree.leaf leaf364) (Tree.leaf leaf365) (by decide +kernel)
noncomputable def node360 : Tree 3641 3658 3 :=
  Tree.join (Tree.leaf leaf363) (node359) (by decide +kernel)
noncomputable def node361 : Tree 3666 3671 2 :=
  Tree.join (Tree.leaf leaf366) (Tree.leaf leaf367) (by decide +kernel)
noncomputable def node362 : Tree 3685 3690 2 :=
  Tree.join (Tree.leaf leaf368) (Tree.leaf leaf369) (by decide +kernel)
noncomputable def node363 : Tree 3666 3690 4 :=
  Tree.join (node361) (node362) (by decide +kernel)
noncomputable def node364 : Tree 3641 3690 7 :=
  Tree.join (node360) (node363) (by decide +kernel)
noncomputable def node365 : Tree 3574 3690 13 :=
  Tree.join (node358) (node364) (by decide +kernel)
noncomputable def node366 : Tree 3711 3726 2 :=
  Tree.join (Tree.leaf leaf371) (Tree.leaf leaf372) (by decide +kernel)
noncomputable def node367 : Tree 3708 3726 3 :=
  Tree.join (Tree.leaf leaf370) (node366) (by decide +kernel)
noncomputable def node368 : Tree 3756 3762 2 :=
  Tree.join (Tree.leaf leaf374) (Tree.leaf leaf375) (by decide +kernel)
noncomputable def node369 : Tree 3744 3762 3 :=
  Tree.join (Tree.leaf leaf373) (node368) (by decide +kernel)
noncomputable def node370 : Tree 3708 3762 6 :=
  Tree.join (node367) (node369) (by decide +kernel)
noncomputable def node371 : Tree 3784 3796 2 :=
  Tree.join (Tree.leaf leaf377) (Tree.leaf leaf378) (by decide +kernel)
noncomputable def node372 : Tree 3773 3796 3 :=
  Tree.join (Tree.leaf leaf376) (node371) (by decide +kernel)
noncomputable def node373 : Tree 3800 3808 2 :=
  Tree.join (Tree.leaf leaf379) (Tree.leaf leaf380) (by decide +kernel)
noncomputable def node374 : Tree 3822 3825 2 :=
  Tree.join (Tree.leaf leaf381) (Tree.leaf leaf382) (by decide +kernel)
noncomputable def node375 : Tree 3800 3825 4 :=
  Tree.join (node373) (node374) (by decide +kernel)
noncomputable def node376 : Tree 3773 3825 7 :=
  Tree.join (node372) (node375) (by decide +kernel)
noncomputable def node377 : Tree 3708 3825 13 :=
  Tree.join (node370) (node376) (by decide +kernel)
noncomputable def node378 : Tree 3574 3825 26 :=
  Tree.join (node365) (node377) (by decide +kernel)
noncomputable def node379 : Tree 3850 3855 2 :=
  Tree.join (Tree.leaf leaf384) (Tree.leaf leaf385) (by decide +kernel)
noncomputable def node380 : Tree 3840 3855 3 :=
  Tree.join (Tree.leaf leaf383) (node379) (by decide +kernel)
noncomputable def node381 : Tree 3879 3891 2 :=
  Tree.join (Tree.leaf leaf387) (Tree.leaf leaf388) (by decide +kernel)
noncomputable def node382 : Tree 3874 3891 3 :=
  Tree.join (Tree.leaf leaf386) (node381) (by decide +kernel)
noncomputable def node383 : Tree 3840 3891 6 :=
  Tree.join (node380) (node382) (by decide +kernel)
noncomputable def node384 : Tree 3907 3917 2 :=
  Tree.join (Tree.leaf leaf390) (Tree.leaf leaf391) (by decide +kernel)
noncomputable def node385 : Tree 3892 3917 3 :=
  Tree.join (Tree.leaf leaf389) (node384) (by decide +kernel)
noncomputable def node386 : Tree 3925 3939 2 :=
  Tree.join (Tree.leaf leaf392) (Tree.leaf leaf393) (by decide +kernel)
noncomputable def node387 : Tree 3952 3959 2 :=
  Tree.join (Tree.leaf leaf394) (Tree.leaf leaf395) (by decide +kernel)
noncomputable def node388 : Tree 3925 3959 4 :=
  Tree.join (node386) (node387) (by decide +kernel)
noncomputable def node389 : Tree 3892 3959 7 :=
  Tree.join (node385) (node388) (by decide +kernel)
noncomputable def node390 : Tree 3840 3959 13 :=
  Tree.join (node383) (node389) (by decide +kernel)
noncomputable def node391 : Tree 3981 3983 2 :=
  Tree.join (Tree.leaf leaf397) (Tree.leaf leaf398) (by decide +kernel)
noncomputable def node392 : Tree 3970 3983 3 :=
  Tree.join (Tree.leaf leaf396) (node391) (by decide +kernel)
noncomputable def node393 : Tree 4005 4026 2 :=
  Tree.join (Tree.leaf leaf400) (Tree.leaf leaf401) (by decide +kernel)
noncomputable def node394 : Tree 3993 4026 3 :=
  Tree.join (Tree.leaf leaf399) (node393) (by decide +kernel)
noncomputable def node395 : Tree 3970 4026 6 :=
  Tree.join (node392) (node394) (by decide +kernel)
noncomputable def node396 : Tree 4036 4051 2 :=
  Tree.join (Tree.leaf leaf403) (Tree.leaf leaf404) (by decide +kernel)
noncomputable def node397 : Tree 4032 4051 3 :=
  Tree.join (Tree.leaf leaf402) (node396) (by decide +kernel)
noncomputable def node398 : Tree 4066 4071 2 :=
  Tree.join (Tree.leaf leaf405) (Tree.leaf leaf406) (by decide +kernel)
noncomputable def node399 : Tree 4074 4083 2 :=
  Tree.join (Tree.leaf leaf407) (Tree.leaf leaf408) (by decide +kernel)
noncomputable def node400 : Tree 4066 4083 4 :=
  Tree.join (node398) (node399) (by decide +kernel)
noncomputable def node401 : Tree 4032 4083 7 :=
  Tree.join (node397) (node400) (by decide +kernel)
noncomputable def node402 : Tree 3970 4083 13 :=
  Tree.join (node395) (node401) (by decide +kernel)
noncomputable def node403 : Tree 3840 4083 26 :=
  Tree.join (node390) (node402) (by decide +kernel)
noncomputable def node404 : Tree 3574 4083 52 :=
  Tree.join (node378) (node403) (by decide +kernel)
noncomputable def node405 : Tree 3062 4083 103 :=
  Tree.join (node353) (node404) (by decide +kernel)
noncomputable def node406 : Tree 2045 4083 205 :=
  Tree.join (node303) (node405) (by decide +kernel)
noncomputable def node407 : Tree 6 4083 409 :=
  Tree.join (node202) (node406) (by decide +kernel)
noncomputable def certificate : Tree 6 4083 409 := node407
end RHHighHeightBracketData
noncomputable def TaoFivePrimes_RHHighHeightBracketTree := RHHighHeightBracketData.certificate


