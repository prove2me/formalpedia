-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B044
-- name    : CK_CKLaneC2R_EpCells_B044
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:39:49.399686+00:00
-- url     : https://prove2.me/theorems/e2f73cca-25dd-4ae6-8a3f-a1b237f2b25a
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B044` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B044` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B044` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B044 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B044.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B044 =====
section

namespace CKLaneC2R.EpCells.B044

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['67383/409600', '1348509/8192000', '3997/4000', '1599/1600']  interval_lower 270884433/1099511627776
noncomputable def e2640 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491092,0,true,167455375808,167455375872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764460,0,false,-197621860416,-197621860352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441944,0,true,167553224576,167553224640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813608,0,false,-197758256768,-197758256704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280255831194,0,true,167338874304,167338874368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918767424358,0,false,-197459500864,-197459500800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280392320811,0,true,167456088320,167456088384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918630934741,0,false,-197622853504,-197622853440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569282295,0,true,57652992,57653056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453973257,0,false,-57656064,-57656000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580859278,0,true,69229312,69229376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442396274,0,false,-69233728,-69233664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623416,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624753,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280323656911,0,true,167397122944,167397123008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918699598641,0,false,-197540672576,-197540672512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280448890199,0,true,167504665088,167504665152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918574365353,0,false,-197690563584,-197690563520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069736323808,0,false,-30185898496,-30185898432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069777526696,0,false,-30143549568,-30143549504⟩
    { al := (67383/409600), au := (1348509/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨180879863316,180993814168⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329703,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405726,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167338874304,167338874368⟩ : DyadicInterval 40),(⟨-197459500864,-197459500800⟩ : DyadicInterval 40),(⟨747199843063,747199862392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167456088320,167456088384⟩ : DyadicInterval 40),(⟨-197622853504,-197622853440⟩ : DyadicInterval 40),(⟨747177191948,747177211278⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57654519,69231502⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57652992,57653056⟩ : DyadicInterval 40),(⟨-57656064,-57656000⟩ : DyadicInterval 40),(⟨762123382064,762123401393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69229312,69229376⟩ : DyadicInterval 40),(⟨-69233728,-69233664⟩ : DyadicInterval 40),(⟨762123381400,762123400729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180812029135,180937262423⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167397122944,167397123008⟩ : DyadicInterval 40),(⟨-197540672576,-197540672512⟩ : DyadicInterval 40),(⟨747188589246,747188608576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167504665088,167504665152⟩ : DyadicInterval 40),(⟨-197690563584,-197690563520⟩ : DyadicInterval 40),(⟨747167798861,747167818190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30185898496,-30143549504⟩ : DyadicInterval 40),(⟨777195158368,777216352128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167455375808,167553224640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197758256768,-197621860352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2640_ok : ecellOkT e2640 = true := by decide +kernel
theorem e2640_pos {a z : ℝ} (ha1 : ((67383/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1348509/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2640 e2640_ok ha1 ha2 hz1 hz2 hz

-- box ['1348509/8192000', '674679/4096000', '3997/4000', '1599/1600']  interval_lower 272206657/1099511627776
noncomputable def e2641 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441943,0,true,167553224576,167553224640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813609,0,false,-197758256768,-197758256704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392795,0,true,167651064640,167651064704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862757,0,false,-197894670080,-197894670016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280369696582,0,true,167436660032,167436660096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918653558970,0,false,-197595774848,-197595774784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280506200442,0,true,167553875840,167553875904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918517055110,0,false,-197759164736,-197759164672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569320076,0,true,57690752,57690816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453935476,0,false,-57693824,-57693760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580904619,0,true,69274624,69274688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442350933,0,false,-69279040,-69278976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623411,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624749,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280437565030,0,true,167494940224,167494940288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918585690522,0,false,-197677007744,-197677007680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280562805442,0,true,167602478912,167602478976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918460450110,0,false,-197826925888,-197826925824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069698819883,0,false,-30224446976,-30224446912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069740051065,0,false,-30182067520,-30182067456⟩
    { al := (1348509/8192000), au := (674679/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨180993814167,181107765019⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405727,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167436660032,167436660096⟩ : DyadicInterval 40),(⟨-197595774848,-197595774784⟩ : DyadicInterval 40),(⟨747180947759,747180967089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553875840,167553875904⟩ : DyadicInterval 40),(⟨-197759164736,-197759164672⟩ : DyadicInterval 40),(⟨747158279738,747158299067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57692300,69276843⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57690752,57690816⟩ : DyadicInterval 40),(⟨-57693824,-57693760⟩ : DyadicInterval 40),(⟨762123382060,762123401389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69274624,69274688⟩ : DyadicInterval 40),(⟨-69279040,-69278976⟩ : DyadicInterval 40),(⟨762123381394,762123400724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180925937254,181051177666⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167494940224,167494940288⟩ : DyadicInterval 40),(⟨-197677007744,-197677007680⟩ : DyadicInterval 40),(⟨747169679595,747169698924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167602478912,167602478976⟩ : DyadicInterval 40),(⟨-197826925888,-197826925824⟩ : DyadicInterval 40),(⟨747148874702,747148894031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30224446976,-30182067456⟩ : DyadicInterval 40),(⟨777214417344,777235626368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167553224576,167651064704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197894670080,-197758256704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2641_ok : ecellOkT e2641 = true := by decide +kernel
theorem e2641_pos {a z : ℝ} (ha1 : ((1348509/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((674679/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2641 e2641_ok ha1 ha2 hz1 hz2 hz

-- box ['67383/409600', '1348509/8192000', '1599/1600', '1999/2000']  interval_lower 270695895/1099511627776
noncomputable def e2642 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491092,0,true,167455375808,167455375872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764460,0,false,-197621860416,-197621860352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441944,0,true,167553224576,167553224640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813608,0,false,-197758256768,-197758256704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280278441177,0,true,167358292096,167358292160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918744814375,0,false,-197486559104,-197486559040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280414945038,0,true,167475516224,167475516288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918608310514,0,false,-197649932800,-197649932736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557751455,0,true,46122688,46122752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465504097,0,false,-46124672,-46124608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569320882,0,true,57691584,57691648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453934670,0,false,-57694656,-57694592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624748,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625842,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280334961751,0,true,167406831232,167406831296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918688293801,0,false,-197554202432,-197554202368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280460202186,0,true,167514378560,167514378624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918563053366,0,false,-197704103872,-197704103808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069732600657,0,false,-30189725248,-30189725184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069773808472,0,false,-30147371136,-30147371072⟩
    { al := (67383/409600), au := (1348509/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨180879863316,180993814168⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329703,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405726,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167358292096,167358292160⟩ : DyadicInterval 40),(⟨-197486559104,-197486559040⟩ : DyadicInterval 40),(⟨747196092012,747196111341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167475516224,167475516288⟩ : DyadicInterval 40),(⟨-197649932800,-197649932736⟩ : DyadicInterval 40),(⟨747173435671,747173455000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46123679,57693106⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46122688,46122752⟩ : DyadicInterval 40),(⟨-46124672,-46124608⟩ : DyadicInterval 40),(⟨762123382609,762123401938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57691584,57691648⟩ : DyadicInterval 40),(⟨-57694656,-57694592⟩ : DyadicInterval 40),(⟨762123382060,762123401389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180823333975,180948574410⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167406831232,167406831296⟩ : DyadicInterval 40),(⟨-197554202432,-197554202368⟩ : DyadicInterval 40),(⟨747186713094,747186732423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167514378560,167514378624⟩ : DyadicInterval 40),(⟨-197704103872,-197704103808⟩ : DyadicInterval 40),(⟨747165920213,747165939543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30189725248,-30147371072⟩ : DyadicInterval 40),(⟨777197069152,777218265504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167455375808,167553224640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197758256768,-197621860352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2642_ok : ecellOkT e2642 = true := by decide +kernel
theorem e2642_pos {a z : ℝ} (ha1 : ((67383/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1348509/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2642 e2642_ok ha1 ha2 hz1 hz2 hz

-- box ['1348509/8192000', '674679/4096000', '1599/1600', '1999/2000']  interval_lower 272017617/1099511627776
noncomputable def e2643 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441943,0,true,167553224576,167553224640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813609,0,false,-197758256768,-197758256704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392795,0,true,167651064640,167651064704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862757,0,false,-197894670080,-197894670016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280392320809,0,true,167456088320,167456088384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918630934743,0,false,-197622853504,-197622853440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280528838913,0,true,167573314304,167573314368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918494416639,0,false,-197786264448,-197786264384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557781680,0,true,46152896,46152960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465473872,0,false,-46154880,-46154816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569358667,0,true,57729344,57729408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453896885,0,false,-57732416,-57732352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624744,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625839,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280448876992,0,true,167504653760,167504653824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918574378560,0,false,-197690547776,-197690547712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280574124555,0,true,167612197632,167612197696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918449130997,0,false,-197840476352,-197840476288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069695092041,0,false,-30228278720,-30228278656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069736328155,0,false,-30185894016,-30185893952⟩
    { al := (1348509/8192000), au := (674679/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨180993814167,181107765019⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405727,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167456088320,167456088384⟩ : DyadicInterval 40),(⟨-197622853504,-197622853440⟩ : DyadicInterval 40),(⟨747177191948,747177211278⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167573314304,167573314368⟩ : DyadicInterval 40),(⟨-197786264448,-197786264384⟩ : DyadicInterval 40),(⟨747154518656,747154537985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46153904,57730891⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46152896,46152960⟩ : DyadicInterval 40),(⟨-46154880,-46154816⟩ : DyadicInterval 40),(⟨762123382606,762123401935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57729344,57729408⟩ : DyadicInterval 40),(⟨-57732416,-57732352⟩ : DyadicInterval 40),(⟨762123382056,762123401385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180937249216,181062496779⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167504653760,167504653824⟩ : DyadicInterval 40),(⟨-197690547776,-197690547712⟩ : DyadicInterval 40),(⟨747167801047,747167820376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167612197632,167612197696⟩ : DyadicInterval 40),(⟨-197840476352,-197840476288⟩ : DyadicInterval 40),(⟨747146993655,747147012985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30228278720,-30185893952⟩ : DyadicInterval 40),(⟨777216330592,777237542240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167553224576,167651064704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197894670080,-197758256704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2643_ok : ecellOkT e2643 = true := by decide +kernel
theorem e2643_pos {a z : ℝ} (ha1 : ((1348509/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((674679/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2643 e2643_ok ha1 ha2 hz1 hz2 hz

-- box ['674679/4096000', '1350207/8192000', '3997/4000', '1599/1600']  interval_lower 273531707/1099511627776
noncomputable def e2644 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392794,0,true,167651064640,167651064704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862758,0,false,-197894670080,-197894670016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343646,0,true,167748895936,167748896000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911906,0,false,-198031100352,-198031100288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280483561970,0,true,167534437056,167534437120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918539693582,0,false,-197732065664,-197732065600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280620080074,0,true,167651654720,167651654784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918403175478,0,false,-197895492928,-197895492864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569357861,0,true,57728512,57728576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453897691,0,false,-57731648,-57731584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580949965,0,true,69320000,69320064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442305587,0,false,-69324416,-69324352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623405,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624745,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280551473151,0,true,167592748736,167592748800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918471782401,0,false,-197813359808,-197813359744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280676720681,0,true,167700283968,167700284032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918346534871,0,false,-197963305088,-197963305024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069661292356,0,false,-30263021056,-30263020992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069702551833,0,false,-30220611008,-30220610944⟩
    { al := (674679/4096000), au := (1350207/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨181107765018,181221715870⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521437,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167534437056,167534437120⟩ : DyadicInterval 40),(⟨-197732065664,-197732065600⟩ : DyadicInterval 40),(⟨747162040316,747162059646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651654720,167651654784⟩ : DyadicInterval 40),(⟨-197895492928,-197895492864⟩ : DyadicInterval 40),(⟨747139355396,747139374726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57730085,69322189⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57728512,57728576⟩ : DyadicInterval 40),(⟨-57731648,-57731584⟩ : DyadicInterval 40),(⟨762123382088,762123401417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69320000,69320064⟩ : DyadicInterval 40),(⟨-69324416,-69324352⟩ : DyadicInterval 40),(⟨762123381389,762123400718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181039845375,181165092905⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167592748736,167592748800⟩ : DyadicInterval 40),(⟨-197813359808,-197813359744⟩ : DyadicInterval 40),(⟨747150757848,747150777178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167700283968,167700284032⟩ : DyadicInterval 40),(⟨-197963305088,-197963305024⟩ : DyadicInterval 40),(⟨747129938444,747129957774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30263021056,-30220610944⟩ : DyadicInterval 40),(⟨777233689088,777254913408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167651064640,167748896000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198031100352,-197894670016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2644_ok : ecellOkT e2644 = true := by decide +kernel
theorem e2644_pos {a z : ℝ} (ha1 : ((674679/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1350207/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2644 e2644_ok ha1 ha2 hz1 hz2 hz

-- box ['1350207/8192000', '84441/512000', '3997/4000', '1599/1600']  interval_lower 274860001/1099511627776
noncomputable def e2645 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343645,0,true,167748895936,167748896000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911907,0,false,-198031100352,-198031100288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294497,0,true,167846718592,167846718656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961055,0,false,-198167547520,-198167547456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280597427358,0,true,167632205440,167632205504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918425828194,0,false,-197868373440,-197868373376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733959706,0,true,167749424832,167749424896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918289295846,0,false,-198031837952,-198031837888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569395648,0,true,57766336,57766400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453859904,0,false,-57769408,-57769344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580995313,0,true,69365312,69365376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442260239,0,false,-69369728,-69369664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623399,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624741,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280665381266,0,true,167690548608,167690548672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918357874286,0,false,-197949728768,-197949728704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280790635925,0,true,167798080384,167798080448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918232619627,0,false,-198099701184,-198099701120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069623741222,0,false,-30301620800,-30301620736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069665029001,0,false,-30259180160,-30259180096⟩
    { al := (1350207/8192000), au := (84441/512000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨181221715869,181335666721⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521438,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561057,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167632205440,167632205504⟩ : DyadicInterval 40),(⟨-197868373440,-197868373376⟩ : DyadicInterval 40),(⟨747143120748,747143140077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167749424832,167749424896⟩ : DyadicInterval 40),(⟨-198031837952,-198031837888⟩ : DyadicInterval 40),(⟨747120418943,747120438273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57767872,69367537⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57766336,57766400⟩ : DyadicInterval 40),(⟨-57769408,-57769344⟩ : DyadicInterval 40),(⟨762123382052,762123401381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69365312,69365376⟩ : DyadicInterval 40),(⟨-69369728,-69369664⟩ : DyadicInterval 40),(⟨762123381383,762123400712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181153753490,181279008149⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167690548608,167690548672⟩ : DyadicInterval 40),(⟨-197949728768,-197949728704⟩ : DyadicInterval 40),(⟨747131823932,747131843261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167798080384,167798080448⟩ : DyadicInterval 40),(⟨-198099701184,-198099701120⟩ : DyadicInterval 40),(⟨747110990011,747111009340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30301620800,-30259180096⟩ : DyadicInterval 40),(⟨777252973664,777274213280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167748895936,167846718656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198167547520,-198031100288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2645_ok : ecellOkT e2645 = true := by decide +kernel
theorem e2645_pos {a z : ℝ} (ha1 : ((1350207/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84441/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2645 e2645_ok ha1 ha2 hz1 hz2 hz

-- box ['674679/4096000', '1350207/8192000', '1599/1600', '1999/2000']  interval_lower 273342381/1099511627776
noncomputable def e2646 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392794,0,true,167651064640,167651064704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862758,0,false,-197894670080,-197894670016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343646,0,true,167748895936,167748896000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911906,0,false,-198031100352,-198031100288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280506200440,0,true,167553875840,167553875904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918517055112,0,false,-197759164736,-197759164672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280642732789,0,true,167671103616,167671103680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918380522763,0,false,-197922613056,-197922612992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557811908,0,true,46183104,46183168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465443644,0,false,-46185152,-46185088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569396455,0,true,57767104,57767168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453859097,0,false,-57770240,-57770176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624740,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625837,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280562792232,0,true,167602467520,167602467584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918460463320,0,false,-197826910080,-197826910016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280688046911,0,true,167710007936,167710008000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918335208641,0,false,-197976865792,-197976865728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069657559823,0,false,-30266857792,-30266857728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069698824235,0,false,-30224442496,-30224442432⟩
    { al := (674679/4096000), au := (1350207/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨181107765018,181221715870⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521437,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553875840,167553875904⟩ : DyadicInterval 40),(⟨-197759164736,-197759164672⟩ : DyadicInterval 40),(⟨747158279738,747158299068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167671103616,167671103680⟩ : DyadicInterval 40),(⟨-197922613056,-197922612992⟩ : DyadicInterval 40),(⟨747135589577,747135608906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46184132,57768679⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46183104,46183168⟩ : DyadicInterval 40),(⟨-46185152,-46185088⟩ : DyadicInterval 40),(⟨762123382636,762123401965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57767104,57767168⟩ : DyadicInterval 40),(⟨-57770240,-57770176⟩ : DyadicInterval 40),(⟨762123382084,762123401413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181051164456,181176419135⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167602467520,167602467584⟩ : DyadicInterval 40),(⟨-197826910080,-197826910016⟩ : DyadicInterval 40),(⟨747148876929,747148896258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167710007936,167710008000⟩ : DyadicInterval 40),(⟨-197976865792,-197976865728⟩ : DyadicInterval 40),(⟨747128055023,747128074353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30266857792,-30224442432⟩ : DyadicInterval 40),(⟨777235604832,777256831776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167651064640,167748896000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198031100352,-197894670016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2646_ok : ecellOkT e2646 = true := by decide +kernel
theorem e2646_pos {a z : ℝ} (ha1 : ((674679/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1350207/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2646 e2646_ok ha1 ha2 hz1 hz2 hz

-- box ['1350207/8192000', '84441/512000', '1599/1600', '1999/2000']  interval_lower 34333765/137438953472
noncomputable def e2647 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343645,0,true,167748895936,167748896000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911907,0,false,-198031100352,-198031100288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294497,0,true,167846718592,167846718656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961055,0,false,-198167547520,-198167547456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280620080072,0,true,167651654720,167651654784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918403175480,0,false,-197895492928,-197895492864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280756626664,0,true,167768884288,167768884352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918266628888,0,false,-198058978560,-198058978496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557842138,0,true,46213376,46213440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465413414,0,false,-46215360,-46215296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569434246,0,true,57804928,57804992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453821306,0,false,-57808000,-57807936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624736,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625834,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280676707468,0,true,167700272640,167700272704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918346548084,0,false,-197963289280,-197963289216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280801969278,0,true,167807809600,167807809664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918221286274,0,false,-198113272128,-198113272064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069620003993,0,false,-30305462464,-30305462400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069661296711,0,false,-30263016640,-30263016576⟩
    { al := (1350207/8192000), au := (84441/512000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨181221715869,181335666721⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521438,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561057,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651654720,167651654784⟩ : DyadicInterval 40),(⟨-197895492928,-197895492864⟩ : DyadicInterval 40),(⟨747139355397,747139374726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167768884288,167768884352⟩ : DyadicInterval 40),(⟨-198058978560,-198058978496⟩ : DyadicInterval 40),(⟨747116648332,747116667662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46214362,57806470⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46213376,46213440⟩ : DyadicInterval 40),(⟨-46215360,-46215296⟩ : DyadicInterval 40),(⟨762123382601,762123401930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57804928,57804992⟩ : DyadicInterval 40),(⟨-57808000,-57807936⟩ : DyadicInterval 40),(⟨762123382048,762123401377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181165079692,181290341502⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167700272640,167700272704⟩ : DyadicInterval 40),(⟨-197963289280,-197963289216⟩ : DyadicInterval 40),(⟨747129940637,747129959967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167807809600,167807809664⟩ : DyadicInterval 40),(⟨-198113272128,-198113272064⟩ : DyadicInterval 40),(⟨747109104211,747109123540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30305462464,-30263016576⟩ : DyadicInterval 40),(⟨777254891904,777276134112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167748895936,167846718656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198167547520,-198031100288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2647_ok : ecellOkT e2647 = true := by decide +kernel
theorem e2647_pos {a z : ℝ} (ha1 : ((1350207/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84441/512000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2647 e2647_ok ha1 ha2 hz1 hz2 hz

-- box ['168033/1024000', '1345113/8192000', '1999/2000', '7997/8000']  interval_lower 265253123/1099511627776
noncomputable def e2648 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687688,0,true,167063893696,167063893760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567864,0,false,-197076443968,-197076443904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638540,0,true,167161777280,167161777344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617012,0,false,-197212772736,-197212772672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279845475658,0,true,166986395520,166986395584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919177779894,0,false,-196968527936,-196968527872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279981936787,0,true,167103622656,167103622720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919041318765,0,false,-197131773504,-197131773440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546129898,0,true,34501568,34501632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477125654,0,false,-34502720,-34502656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557661539,0,true,46032768,46032832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465594013,0,false,-46034752,-46034688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625848,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626694,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279890577171,0,true,167025141440,167025141504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919132678381,0,false,-197022479232,-197022479168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280015796259,0,true,167132707712,167132707776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919007459293,0,false,-197172282624,-197172282560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069878694374,0,false,-30039574848,-30039574784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069919793945,0,false,-29997337792,-29997337728⟩
    { al := (168033/1024000), au := (1345113/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨180424059912,180538010764⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904118,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166986395520,166986395584⟩ : DyadicInterval 40),(⟨-196968527936,-196968527872⟩ : DyadicInterval 40),(⟨747267838707,747267858037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167103622656,167103622720⟩ : DyadicInterval 40),(⟨-197131773504,-197131773440⟩ : DyadicInterval 40),(⟨747245244633,747245263963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34502122,46033763⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34501568,34501632⟩ : DyadicInterval 40),(⟨-34502720,-34502656⟩ : DyadicInterval 40),(⟨762123383045,762123402374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46032768,46032832⟩ : DyadicInterval 40),(⟨-46034752,-46034688⟩ : DyadicInterval 40),(⟨762123382616,762123401945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180378949395,180504168483⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167025141440,167025141504⟩ : DyadicInterval 40),(⟨-197022479232,-197022479168⟩ : DyadicInterval 40),(⟨747260373094,747260392424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167132707712,167132707776⟩ : DyadicInterval 40),(⟨-197172282624,-197172282560⟩ : DyadicInterval 40),(⟨747239635795,747239655124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30039574848,-29997337728⟩ : DyadicInterval 40),(⟨777122052480,777143190304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167063893696,167161777344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197212772736,-197076443904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2648_ok : ecellOkT e2648 = true := by decide +kernel
theorem e2648_pos {a z : ℝ} (ha1 : ((168033/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1345113/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2648 e2648_ok ha1 ha2 hz1 hz2 hz

-- box ['1345113/8192000', '672981/4096000', '1999/2000', '7997/8000']  interval_lower 33320257/137438953472
noncomputable def e2649 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638539,0,true,167161777280,167161777344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617013,0,false,-197212772736,-197212772672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589391,0,true,167259652160,167259652224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666161,0,false,-197349118336,-197349118272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279959369533,0,true,167084237056,167084237120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919063886019,0,false,-197104775104,-197104775040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280095844906,0,true,167201465984,167201466048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918927410646,0,false,-197268057984,-197268057920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546152560,0,true,34524224,34524288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477102992,0,false,-34525376,-34525312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557691758,0,true,46062976,46063040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465563794,0,false,-46064960,-46064896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625846,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626692,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280004499530,0,true,167123004032,167123004096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919018756022,0,false,-197158767168,-197158767104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280129725744,0,true,167230566848,167230566912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918893529808,0,false,-197308597696,-197308597632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069841275512,0,false,-30078030848,-30078030784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069882403373,0,false,-30035763136,-30035763072⟩
    { al := (1345113/8192000), au := (672981/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨180538010763,180651961615⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167084237056,167084237120⟩ : DyadicInterval 40),(⟨-197104775104,-197104775040⟩ : DyadicInterval 40),(⟨747248982347,747249001676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167201465984,167201466048⟩ : DyadicInterval 40),(⟨-197268057984,-197268057920⟩ : DyadicInterval 40),(⟨747226371408,747226390737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34524784,46063982⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34524224,34524288⟩ : DyadicInterval 40),(⟨-34525376,-34525312⟩ : DyadicInterval 40),(⟨762123383043,762123402372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46062976,46063040⟩ : DyadicInterval 40),(⟨-46064960,-46064896⟩ : DyadicInterval 40),(⟨762123382614,762123401943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180492871754,180618097968⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167123004032,167123004096⟩ : DyadicInterval 40),(⟨-197158767168,-197158767104⟩ : DyadicInterval 40),(⟨747241507195,747241526524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167230566848,167230566912⟩ : DyadicInterval 40),(⟨-197308597696,-197308597632⟩ : DyadicInterval 40),(⟨747220755398,747220774728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30078030848,-30035763072⟩ : DyadicInterval 40),(⟨777141265152,777162418304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167161777280,167259652224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197349118336,-197212772672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2649_ok : ecellOkT e2649 = true := by decide +kernel
theorem e2649_pos {a z : ℝ} (ha1 : ((1345113/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((672981/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2649 e2649_ok ha1 ha2 hz1 hz2 hz

-- box ['168033/1024000', '1345113/8192000', '7997/8000', '3999/4000']  interval_lower 265065951/1099511627776
noncomputable def e2650 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687688,0,true,167063893696,167063893760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567864,0,false,-197076443968,-197076443904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638540,0,true,167161777280,167161777344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617012,0,false,-197212772736,-197212772672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279868028665,0,true,167005770560,167005770624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919155226887,0,false,-196995505920,-196995505856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280004504038,0,true,167123007872,167123007936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919018751514,0,false,-197158772608,-197158772544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534629162,0,true,23001088,23001152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488626390,0,false,-23001664,-23001600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546153249,0,true,34524928,34524992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477102303,0,false,-34526016,-34525952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626691,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627295,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279901853578,0,true,167034828544,167034828608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919121401974,0,false,-197035968704,-197035968640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280027079813,0,true,167142400064,167142400128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918996175739,0,false,-197185782528,-197185782464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069874989471,0,false,-30043382400,-30043382336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069916093957,0,false,-30001140096,-30001140032⟩
    { al := (168033/1024000), au := (1345113/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨180424059912,180538010764⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904118,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167005770560,167005770624⟩ : DyadicInterval 40),(⟨-196995505920,-196995505856⟩ : DyadicInterval 40),(⟨747264105770,747264125099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167123007872,167123007936⟩ : DyadicInterval 40),(⟨-197158772608,-197158772544⟩ : DyadicInterval 40),(⟨747241506486,747241525816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23001386,34525473⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23001088,23001152⟩ : DyadicInterval 40),(⟨-23001664,-23001600⟩ : DyadicInterval 40),(⟨762123383358,762123402687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34524928,34524992⟩ : DyadicInterval 40),(⟨-34526016,-34525952⟩ : DyadicInterval 40),(⟨762123383011,762123402340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180390225802,180515452037⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167034828544,167034828608⟩ : DyadicInterval 40),(⟨-197035968704,-197035968640⟩ : DyadicInterval 40),(⟨747258506252,747258525582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167142400064,167142400128⟩ : DyadicInterval 40),(⟨-197185782528,-197185782464⟩ : DyadicInterval 40),(⟨747237766434,747237785764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30043382400,-30001140032⟩ : DyadicInterval 40),(⟨777123953632,777145094080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167063893696,167161777344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197212772736,-197076443904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2650_ok : ecellOkT e2650 = true := by decide +kernel
theorem e2650_pos {a z : ℝ} (ha1 : ((168033/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1345113/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2650 e2650_ok ha1 ha2 hz1 hz2 hz

-- box ['1345113/8192000', '672981/4096000', '7997/8000', '3999/4000']  interval_lower 266374635/1099511627776
noncomputable def e2651 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638539,0,true,167161777280,167161777344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617013,0,false,-197212772736,-197212772672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589391,0,true,167259652160,167259652224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666161,0,false,-197349118336,-197349118272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279981936784,0,true,167103622656,167103622720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919041318768,0,false,-197131773504,-197131773440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280118426401,0,true,167220861760,167220861824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918904829151,0,false,-197295077440,-197295077376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534644271,0,true,23016192,23016256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488611281,0,false,-23016768,-23016704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546175913,0,true,34547584,34547648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477079639,0,false,-34548736,-34548672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626690,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627295,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280015783060,0,true,167132696384,167132696448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919007472492,0,false,-197172266880,-197172266816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280141016426,0,true,167240264448,167240264512⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918882239126,0,false,-197322107776,-197322107712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069837565929,0,false,-30081843264,-30081843200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069878698709,0,false,-30039570432,-30039570368⟩
    { al := (1345113/8192000), au := (672981/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨180538010763,180651961615⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167103622656,167103622720⟩ : DyadicInterval 40),(⟨-197131773504,-197131773440⟩ : DyadicInterval 40),(⟨747245244634,747245263963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167220861760,167220861824⟩ : DyadicInterval 40),(⟨-197295077440,-197295077376⟩ : DyadicInterval 40),(⟨747222628451,747222647780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23016495,34548137⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23016192,23016256⟩ : DyadicInterval 40),(⟨-23016768,-23016704⟩ : DyadicInterval 40),(⟨762123383358,762123402687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34547584,34547648⟩ : DyadicInterval 40),(⟨-34548736,-34548672⟩ : DyadicInterval 40),(⟨762123383042,762123402371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180504155284,180629388650⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167132696384,167132696448⟩ : DyadicInterval 40),(⟨-197172266880,-197172266816⟩ : DyadicInterval 40),(⟨747239637996,747239657325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167240264448,167240264512⟩ : DyadicInterval 40),(⟨-197322107776,-197322107712⟩ : DyadicInterval 40),(⟨747218883650,747218902979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30081843264,-30039570368⟩ : DyadicInterval 40),(⟨777143168800,777164324512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167161777280,167259652224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197349118336,-197212772672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2651_ok : ecellOkT e2651 = true := by decide +kernel
theorem e2651_pos {a z : ℝ} (ha1 : ((1345113/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((672981/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2651 e2651_ok ha1 ha2 hz1 hz2 hz

-- box ['672981/4096000', '1346811/8192000', '1999/2000', '7997/8000']  interval_lower 267874109/1099511627776
noncomputable def e2652 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589390,0,true,167259652160,167259652224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666162,0,false,-197349118336,-197349118272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540242,0,true,167357518336,167357518400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715310,0,false,-197485480896,-197485480832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280073263409,0,true,167182069952,167182070016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918949992143,0,false,-197241039168,-197241039104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280209753025,0,true,167299300672,167299300736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918813502527,0,false,-197404359360,-197404359296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546175224,0,true,34546880,34546944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477080328,0,false,-34548032,-34547968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557721980,0,true,46093184,46093248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465533572,0,false,-46095232,-46095168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625843,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626691,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280118421898,0,true,167220857856,167220857920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918904833654,0,false,-197295072064,-197295072000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280243655233,0,true,167328417280,167328417344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918779600319,0,false,-197444929664,-197444929600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069803833039,0,false,-30116512384,-30116512320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069844989190,0,false,-30074214144,-30074214080⟩
    { al := (672981/4096000), au := (1346811/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨180651961614,180765912466⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167182069952,167182070016⟩ : DyadicInterval 40),(⟨-197241039168,-197241039104⟩ : DyadicInterval 40),(⟨747230113828,747230133157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167299300672,167299300736⟩ : DyadicInterval 40),(⟨-197404359360,-197404359296⟩ : DyadicInterval 40),(⟨747207486016,747207505346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34547448,46094204⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34546880,34546944⟩ : DyadicInterval 40),(⟨-34548032,-34547968⟩ : DyadicInterval 40),(⟨762123383042,762123402371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46093184,46093248⟩ : DyadicInterval 40),(⟨-46095232,-46095168⟩ : DyadicInterval 40),(⟨762123382643,762123401972⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180606794122,180732027457⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167220857856,167220857920⟩ : DyadicInterval 40),(⟨-197295072064,-197295072000⟩ : DyadicInterval 40),(⟨747222629224,747222648554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167328417280,167328417344⟩ : DyadicInterval 40),(⟨-197444929664,-197444929600⟩ : DyadicInterval 40),(⟨747201862863,747201882193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30116512384,-30074214080⟩ : DyadicInterval 40),(⟨777160490656,777181659072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167259652160,167357518400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197485480896,-197349118272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2652_ok : ecellOkT e2652 = true := by decide +kernel
theorem e2652_pos {a z : ℝ} (ha1 : ((672981/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1346811/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2652 e2652_ok ha1 ha2 hz1 hz2 hz

-- box ['1346811/8192000', '67383/409600', '1999/2000', '7997/8000']  interval_lower 269189201/1099511627776
noncomputable def e2653 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540241,0,true,167357518336,167357518400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715311,0,false,-197485480896,-197485480832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491093,0,true,167455375808,167455375872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764459,0,false,-197621860416,-197621860352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280187157284,0,true,167279894080,167279894144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918836098268,0,false,-197377320192,-197377320128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280323661145,0,true,167397126592,167397126656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918699594407,0,false,-197540677632,-197540677568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546197891,0,true,34569536,34569600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477057661,0,false,-34570688,-34570624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557752202,0,true,46123456,46123520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465503350,0,false,-46125440,-46125376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625841,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626690,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280232344255,0,true,167318703040,167318703104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918790911297,0,false,-197431393792,-197431393728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280357584714,0,true,167426259008,167426259072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918665670838,0,false,-197581278528,-197581278464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069766366957,0,false,-30155019520,-30155019456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069807551403,0,false,-30112690752,-30112690688⟩
    { al := (1346811/8192000), au := (67383/409600), zl := (1999/2000), zu := (7997/8000),
      A := ⟨180765912465,180879863317⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329702,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167279894080,167279894144⟩ : DyadicInterval 40),(⟨-197377320192,-197377320128⟩ : DyadicInterval 40),(⟨747211233251,747211252580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167397126592,167397126656⟩ : DyadicInterval 40),(⟨-197540677632,-197540677568⟩ : DyadicInterval 40),(⟨747188588532,747188607862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34570115,46124426⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34569536,34569600⟩ : DyadicInterval 40),(⟨-34570688,-34570624⟩ : DyadicInterval 40),(⟨762123383041,762123402370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46123456,46123520⟩ : DyadicInterval 40),(⟨-46125440,-46125376⟩ : DyadicInterval 40),(⟨762123382609,762123401938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180720716479,180845956938⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167318703040,167318703104⟩ : DyadicInterval 40),(⟨-197431393792,-197431393728⟩ : DyadicInterval 40),(⟨747203739056,747203758386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167426259008,167426259072⟩ : DyadicInterval 40),(⟨-197581278528,-197581278464⟩ : DyadicInterval 40),(⟨747182958190,747182977520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30155019520,-30112690688⟩ : DyadicInterval 40),(⟨777179728960,777200912640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167357518336,167455375872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197621860416,-197485480832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2653_ok : ecellOkT e2653 = true := by decide +kernel
theorem e2653_pos {a z : ℝ} (ha1 : ((1346811/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((67383/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2653 e2653_ok ha1 ha2 hz1 hz2 hz

-- box ['672981/4096000', '1346811/8192000', '7997/8000', '3999/4000']  interval_lower 267686367/1099511627776
noncomputable def e2654 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589390,0,true,167259652160,167259652224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666162,0,false,-197349118336,-197349118272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540242,0,true,167357518336,167357518400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715310,0,false,-197485480896,-197485480832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280095844904,0,true,167201465984,167201466048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918927410648,0,false,-197268057984,-197268057920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280232348765,0,true,167318706880,167318706944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918790906787,0,false,-197431399232,-197431399168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534659381,0,true,23031360,23031424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488596171,0,false,-23031872,-23031808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546198580,0,true,34570240,34570304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477056972,0,false,-34571392,-34571328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626689,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627294,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280129712544,0,true,167230555520,167230555584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918893543008,0,false,-197308581888,-197308581824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280254953030,0,true,167338120128,167338120192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918768302522,0,false,-197458449920,-197458449856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069800118776,0,false,-30120329792,-30120329728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069841279850,0,false,-30078026368,-30078026304⟩
    { al := (672981/4096000), au := (1346811/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨180651961614,180765912466⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167201465984,167201466048⟩ : DyadicInterval 40),(⟨-197268057984,-197268057920⟩ : DyadicInterval 40),(⟨747226371408,747226390738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167318706880,167318706944⟩ : DyadicInterval 40),(⟨-197431399232,-197431399168⟩ : DyadicInterval 40),(⟨747203738345,747203757675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23031605,34570804⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23031360,23031424⟩ : DyadicInterval 40),(⟨-23031872,-23031808⟩ : DyadicInterval 40),(⟨762123383325,762123402654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34570240,34570304⟩ : DyadicInterval 40),(⟨-34571392,-34571328⟩ : DyadicInterval 40),(⟨762123383041,762123402370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180618084768,180743325254⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167230555520,167230555584⟩ : DyadicInterval 40),(⟨-197308581888,-197308581824⟩ : DyadicInterval 40),(⟨747220757576,747220776905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167338120128,167338120192⟩ : DyadicInterval 40),(⟨-197458449920,-197458449856⟩ : DyadicInterval 40),(⟨747199988726,747200008055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30120329792,-30078026304⟩ : DyadicInterval 40),(⟨777162396768,777183567776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167259652160,167357518400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197485480896,-197349118272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2654_ok : ecellOkT e2654 = true := by decide +kernel
theorem e2654_pos {a z : ℝ} (ha1 : ((672981/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1346811/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2654 e2654_ok ha1 ha2 hz1 hz2 hz

-- box ['1346811/8192000', '67383/409600', '7997/8000', '3999/4000']  interval_lower 269000853/1099511627776
noncomputable def e2655 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540241,0,true,167357518336,167357518400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715311,0,false,-197485480896,-197485480832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491093,0,true,167455375808,167455375872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764459,0,false,-197621860416,-197621860352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280209753023,0,true,167299300672,167299300736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918813502529,0,false,-197404359360,-197404359296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280346271128,0,true,167416543360,167416543424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918676984424,0,false,-197567737856,-197567737792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534674491,0,true,23046464,23046528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488581061,0,false,-23046976,-23046912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546221248,0,true,34592896,34592960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477034304,0,false,-34594048,-34593984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626687,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627293,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280243642029,0,true,167328405952,167328406016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918779613523,0,false,-197444913856,-197444913792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280368889640,0,true,167435967104,167435967168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918654365912,0,false,-197594809024,-197594808960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069762648008,0,false,-30158841920,-30158841856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069803837380,0,false,-30116507904,-30116507840⟩
    { al := (1346811/8192000), au := (67383/409600), zl := (7997/8000), zu := (3999/4000),
      A := ⟨180765912465,180879863317⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329702,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167299300672,167299300736⟩ : DyadicInterval 40),(⟨-197404359360,-197404359296⟩ : DyadicInterval 40),(⟨747207486017,747207505346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167416543360,167416543424⟩ : DyadicInterval 40),(⟨-197567737856,-197567737792⟩ : DyadicInterval 40),(⟨747184836039,747184855369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23046715,34593472⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23046464,23046528⟩ : DyadicInterval 40),(⟨-23046976,-23046912⟩ : DyadicInterval 40),(⟨762123383324,762123402653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34592896,34592960⟩ : DyadicInterval 40),(⟨-34594048,-34593984⟩ : DyadicInterval 40),(⟨762123383039,762123402368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180732014253,180857261864⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167328405952,167328406016⟩ : DyadicInterval 40),(⟨-197444913856,-197444913792⟩ : DyadicInterval 40),(⟨747201865044,747201884373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167435967104,167435967168⟩ : DyadicInterval 40),(⟨-197594809024,-197594808960⟩ : DyadicInterval 40),(⟨747181081685,747181101014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30158841920,-30116507840⟩ : DyadicInterval 40),(⟨777181637536,777202823840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167357518336,167455375872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197621860416,-197485480832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2655_ok : ecellOkT e2655 = true := by decide +kernel
theorem e2655_pos {a z : ℝ} (ha1 : ((1346811/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((67383/409600 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2655 e2655_ok ha1 ha2 hz1 hz2 hz

-- box ['168033/1024000', '1345113/8192000', '3999/4000', '7999/8000']  interval_lower 66219727/274877906944
noncomputable def e2656 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687688,0,true,167063893696,167063893760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567864,0,false,-197076443968,-197076443904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638540,0,true,167161777280,167161777344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617012,0,false,-197212772736,-197212772672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279890581673,0,true,167025145280,167025145344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919132673879,0,false,-197022484608,-197022484544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280027071289,0,true,167142392768,167142392832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918996184263,0,false,-197185772288,-197185772224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523128369,0,true,11500480,11500544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500127183,0,false,-11500672,-11500608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534644902,0,true,23016832,23016896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488610650,0,false,-23017408,-23017344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627294,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279913130013,0,true,167044515648,167044515712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919110125539,0,false,-197049458368,-197049458304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280038363401,0,true,167152092352,167152092416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918984892151,0,false,-197199282560,-197199282496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069871284325,0,false,-30047190208,-30047190144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069912393728,0,false,-30004942656,-30004942592⟩
    { al := (168033/1024000), au := (1345113/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨180424059912,180538010764⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904118,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167025145280,167025145344⟩ : DyadicInterval 40),(⟨-197022484608,-197022484544⟩ : DyadicInterval 40),(⟨747260372361,747260391691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167142392768,167142392832⟩ : DyadicInterval 40),(⟨-197185772288,-197185772224⟩ : DyadicInterval 40),(⟨747237767814,747237787143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11500593,23017126⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11500480,11500544⟩ : DyadicInterval 40),(⟨-11500672,-11500608⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23016832,23016896⟩ : DyadicInterval 40),(⟨-23017408,-23017344⟩ : DyadicInterval 40),(⟨762123383358,762123402687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180401502237,180526735625⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167044515648,167044515712⟩ : DyadicInterval 40),(⟨-197049458368,-197049458304⟩ : DyadicInterval 40),(⟨747256639248,747256658578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167152092352,167152092416⟩ : DyadicInterval 40),(⟨-197199282560,-197199282496⟩ : DyadicInterval 40),(⟨747235896920,747235916250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30047190208,-30004942592⟩ : DyadicInterval 40),(⟨777125854912,777146997984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167063893696,167161777344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197212772736,-197076443904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2656_ok : ecellOkT e2656 = true := by decide +kernel
theorem e2656_pos {a z : ℝ} (ha1 : ((168033/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1345113/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2656 e2656_ok ha1 ha2 hz1 hz2 hz

-- box ['1345113/8192000', '672981/4096000', '3999/4000', '7999/8000']  interval_lower 266187049/1099511627776
noncomputable def e2657 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638539,0,true,167161777280,167161777344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617013,0,false,-197212772736,-197212772672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589391,0,true,167259652160,167259652224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666161,0,false,-197349118336,-197349118272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280004504036,0,true,167123007872,167123007936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919018751516,0,false,-197158772608,-197158772544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280141007896,0,true,167240257152,167240257216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918882247656,0,false,-197322097600,-197322097536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523135923,0,true,11508032,11508096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500119629,0,false,-11508224,-11508160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534660012,0,true,23031936,23032000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488595540,0,false,-23032512,-23032448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627293,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280027066615,0,true,167142388736,167142388800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918996188937,0,false,-197185766720,-197185766656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280152307130,0,true,167249961984,167249962048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918870948422,0,false,-197335618048,-197335617984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069833856106,0,false,-30085656000,-30085655936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069874993806,0,false,-30043377920,-30043377856⟩
    { al := (1345113/8192000), au := (672981/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨180538010763,180651961615⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167123007872,167123007936⟩ : DyadicInterval 40),(⟨-197158772608,-197158772544⟩ : DyadicInterval 40),(⟨747241506487,747241525816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167240257152,167240257216⟩ : DyadicInterval 40),(⟨-197322097600,-197322097536⟩ : DyadicInterval 40),(⟨747218885059,747218904389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11508147,23032236⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11508032,11508096⟩ : DyadicInterval 40),(⟨-11508224,-11508160⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23031936,23032000⟩ : DyadicInterval 40),(⟨-23032512,-23032448⟩ : DyadicInterval 40),(⟨762123383357,762123402686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180515438839,180640679354⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167142388736,167142388800⟩ : DyadicInterval 40),(⟨-197185766720,-197185766656⟩ : DyadicInterval 40),(⟨747237768608,747237787938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167249961984,167249962048⟩ : DyadicInterval 40),(⟨-197335618048,-197335617984⟩ : DyadicInterval 40),(⟨747217011777,747217031106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30085656000,-30043377856⟩ : DyadicInterval 40),(⟨777145072544,777166230880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167161777280,167259652224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197349118336,-197212772672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2657_ok : ecellOkT e2657 = true := by decide +kernel
theorem e2657_pos {a z : ℝ} (ha1 : ((1345113/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((672981/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2657 e2657_ok ha1 ha2 hz1 hz2 hz

-- box ['168033/1024000', '1345113/8192000', '7999/8000', '1']  interval_lower 264692049/1099511627776
noncomputable def e2658 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687688,0,true,167063893696,167063893760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567864,0,false,-197076443968,-197076443904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638540,0,true,167161777280,167161777344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617012,0,false,-197212772736,-197212772672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279913134680,0,true,167044519680,167044519744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919110120872,0,false,-197049463936,-197049463872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523136496,0,true,11508608,11508672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500119056,0,false,-11508800,-11508736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1279924406478,0,true,167054202688,167054202752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨919098849074,0,false,-197062948224,-197062948160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049647008,0,true,167161784576,167161784640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨918973608544,0,false,-197212782848,-197212782784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069867578941,0,false,-30050998272,-30050998208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069908693258,0,false,-30008745536,-30008745472⟩
    { al := (168033/1024000), au := (1345113/8192000), zl := (7999/8000), zu := 1,
      A := ⟨180424059912,180538010764⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904118,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167044519680,167044519744⟩ : DyadicInterval 40),(⟨-197049463936,-197049463872⟩ : DyadicInterval 40),(⟨747256638456,747256657786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11508720⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11508608,11508672⟩ : DyadicInterval 40),(⟨-11508800,-11508736⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨180412778702,180538019232⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167054202688,167054202752⟩ : DyadicInterval 40),(⟨-197062948224,-197062948160⟩ : DyadicInterval 40),(⟨747254772119,747254791449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161784576,167161784640⟩ : DyadicInterval 40),(⟨-197212782848,-197212782784⟩ : DyadicInterval 40),(⟨747234027310,747234046639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30050998272,-30008745472⟩ : DyadicInterval 40),(⟨777127756352,777148902016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167063893696,167161777344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197212772736,-197076443904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2658_ok : ecellOkT e2658 = true := by decide +kernel
theorem e2658_pos {a z : ℝ} (ha1 : ((168033/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1345113/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2658 e2658_ok ha1 ha2 hz1 hz2 hz

-- box ['1345113/8192000', '672981/4096000', '7999/8000', '1']  interval_lower 265999609/1099511627776
noncomputable def e2659 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638539,0,true,167161777280,167161777344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617013,0,false,-197212772736,-197212772672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589391,0,true,167259652160,167259652224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666161,0,false,-197349118336,-197349118272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280027071287,0,true,167142392768,167142392832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918996184265,0,false,-197185772288,-197185772224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523144051,0,true,11516160,11516224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500111501,0,false,-11516352,-11516288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1280038350203,0,true,167152081024,167152081088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨918984905349,0,false,-197199266816,-197199266752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163597863,0,true,167259659456,167259659520⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨918859657689,0,false,-197349128512,-197349128448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069830146041,0,false,-30089468992,-30089468928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069871288660,0,false,-30047185728,-30047185664⟩
    { al := (1345113/8192000), au := (672981/4096000), zl := (7999/8000), zu := 1,
      A := ⟨180538010763,180651961615⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167142392768,167142392832⟩ : DyadicInterval 40),(⟨-197185772288,-197185772224⟩ : DyadicInterval 40),(⟨747237767814,747237787144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11516275⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11516160,11516224⟩ : DyadicInterval 40),(⟨-11516352,-11516288⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨180526722427,180651970087⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167152081024,167152081088⟩ : DyadicInterval 40),(⟨-197199266816,-197199266752⟩ : DyadicInterval 40),(⟨747235899122,747235918451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259659456,167259659520⟩ : DyadicInterval 40),(⟨-197349128512,-197349128448⟩ : DyadicInterval 40),(⟨747215139778,747215159108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30089468992,-30047185664⟩ : DyadicInterval 40),(⟨777146976448,777168137376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167161777280,167259652224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197349118336,-197212772672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2659_ok : ecellOkT e2659 = true := by decide +kernel
theorem e2659_pos {a z : ℝ} (ha1 : ((1345113/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((672981/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2659 e2659_ok ha1 ha2 hz1 hz2 hz

-- box ['672981/4096000', '1346811/8192000', '3999/4000', '7999/8000']  interval_lower 66874563/274877906944
noncomputable def e2660 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589390,0,true,167259652160,167259652224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666162,0,false,-197349118336,-197349118272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540242,0,true,167357518336,167357518400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715310,0,false,-197485480896,-197485480832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280118426399,0,true,167220861760,167220861824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918904829153,0,false,-197295077440,-197295077376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280254944504,0,true,167338112768,167338112832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918768311048,0,false,-197458439744,-197458439680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523143479,0,true,11515584,11515648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500112073,0,false,-11515776,-11515712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534675122,0,true,23047104,23047168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488580430,0,false,-23047616,-23047552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627292,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280141003225,0,true,167240253120,167240253184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918882252327,0,false,-197322091968,-197322091904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280266250857,0,true,167347822912,167347822976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918757004695,0,false,-197471970368,-197471970304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069796404271,0,false,-30124147456,-30124147392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069837570267,0,false,-30081838848,-30081838784⟩
    { al := (672981/4096000), au := (1346811/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨180651961614,180765912466⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167220861760,167220861824⟩ : DyadicInterval 40),(⟨-197295077440,-197295077376⟩ : DyadicInterval 40),(⟨747222628451,747222647781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167338112768,167338112832⟩ : DyadicInterval 40),(⟨-197458439744,-197458439680⟩ : DyadicInterval 40),(⟨747199990174,747200009503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11515703,23047346⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11515584,11515648⟩ : DyadicInterval 40),(⟨-11515776,-11515712⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23047104,23047168⟩ : DyadicInterval 40),(⟨-23047616,-23047552⟩ : DyadicInterval 40),(⟨762123383324,762123402653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180629375449,180754623081⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167240253120,167240253184⟩ : DyadicInterval 40),(⟨-197322091968,-197322091904⟩ : DyadicInterval 40),(⟨747218885827,747218905157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167347822912,167347822976⟩ : DyadicInterval 40),(⟨-197471970368,-197471970304⟩ : DyadicInterval 40),(⟨747198114462,747198133792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30124147456,-30081838784⟩ : DyadicInterval 40),(⟨777164303008,777185476608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167259652160,167357518400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197485480896,-197349118272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2660_ok : ecellOkT e2660 = true := by decide +kernel
theorem e2660_pos {a z : ℝ} (ha1 : ((672981/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1346811/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2660 e2660_ok ha1 ha2 hz1 hz2 hz

-- box ['1346811/8192000', '67383/409600', '3999/4000', '7999/8000']  interval_lower 134406213/549755813888
noncomputable def e2661 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540241,0,true,167357518336,167357518400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715311,0,false,-197485480896,-197485480832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491093,0,true,167455375808,167455375872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764459,0,false,-197621860416,-197621860352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280232348762,0,true,167318706880,167318706944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918790906790,0,false,-197431399232,-197431399168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280368881111,0,true,167435959744,167435959808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918654374441,0,false,-197594798784,-197594798720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523151034,0,true,11523136,11523200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500104518,0,false,-11523328,-11523264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534690233,0,true,23062208,23062272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488565319,0,false,-23062720,-23062656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627292,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280254939826,0,true,167338108800,167338108864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918768315726,0,false,-197458434112,-197458434048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280380194588,0,true,167445675136,167445675200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918643060964,0,false,-197608339648,-197608339584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069758928819,0,false,-30162664512,-30162664448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069800123118,0,false,-30120325312,-30120325248⟩
    { al := (1346811/8192000), au := (67383/409600), zl := (3999/4000), zu := (7999/8000),
      A := ⟨180765912465,180879863317⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329702,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167318706880,167318706944⟩ : DyadicInterval 40),(⟨-197431399232,-197431399168⟩ : DyadicInterval 40),(⟨747203738346,747203757675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167435959744,167435959808⟩ : DyadicInterval 40),(⟨-197594798784,-197594798720⟩ : DyadicInterval 40),(⟨747181083108,747181102438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11523258,23062457⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11523136,11523200⟩ : DyadicInterval 40),(⟨-11523328,-11523264⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23062208,23062272⟩ : DyadicInterval 40),(⟨-23062720,-23062656⟩ : DyadicInterval 40),(⟨762123383324,762123402653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180743312050,180868566812⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167338108800,167338108864⟩ : DyadicInterval 40),(⟨-197458434112,-197458434048⟩ : DyadicInterval 40),(⟨747199990907,747200010236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167445675136,167445675200⟩ : DyadicInterval 40),(⟨-197608339648,-197608339584⟩ : DyadicInterval 40),(⟨747179205028,747179224358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30162664512,-30120325248⟩ : DyadicInterval 40),(⟨777183546240,777204735136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167357518336,167455375872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197621860416,-197485480832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2661_ok : ecellOkT e2661 = true := by decide +kernel
theorem e2661_pos {a z : ℝ} (ha1 : ((1346811/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((67383/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2661 e2661_ok ha1 ha2 hz1 hz2 hz

-- box ['672981/4096000', '1346811/8192000', '7999/8000', '1']  interval_lower 133655235/549755813888
noncomputable def e2662 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589390,0,true,167259652160,167259652224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666162,0,false,-197349118336,-197349118272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540242,0,true,167357518336,167357518400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715310,0,false,-197485480896,-197485480832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280141007894,0,true,167240257152,167240257216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918882247658,0,false,-197322097600,-197322097536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523151606,0,true,11523712,11523776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500103946,0,false,-11523904,-11523840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1280152293929,0,true,167249950656,167249950720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨918870961623,0,false,-197335602240,-197335602176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277548715,0,true,167357525632,167357525696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨918745706837,0,false,-197485491072,-197485491008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069792689524,0,false,-30127965376,-30127965312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069833860444,0,false,-30085651584,-30085651520⟩
    { al := (672981/4096000), au := (1346811/8192000), zl := (7999/8000), zu := 1,
      A := ⟨180651961614,180765912466⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167240257152,167240257216⟩ : DyadicInterval 40),(⟨-197322097600,-197322097536⟩ : DyadicInterval 40),(⟨747218885060,747218904389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11523830⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11523712,11523776⟩ : DyadicInterval 40),(⟨-11523904,-11523840⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨180640666153,180765920939⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167249950656,167249950720⟩ : DyadicInterval 40),(⟨-197335602240,-197335602176⟩ : DyadicInterval 40),(⟨747217013955,747217033284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357525632,167357525696⟩ : DyadicInterval 40),(⟨-197485491072,-197485491008⟩ : DyadicInterval 40),(⟨747196240099,747196259429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30127965376,-30085651520⟩ : DyadicInterval 40),(⟨777166209376,777187385568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167259652160,167357518400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197485480896,-197349118272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2662_ok : ecellOkT e2662 = true := by decide +kernel
theorem e2662_pos {a z : ℝ} (ha1 : ((672981/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1346811/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2662 e2662_ok ha1 ha2 hz1 hz2 hz

-- box ['1346811/8192000', '67383/409600', '7999/8000', '1']  interval_lower 67156025/274877906944
noncomputable def e2663 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540241,0,true,167357518336,167357518400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715311,0,false,-197485480896,-197485480832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491093,0,true,167455375808,167455375872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764459,0,false,-197621860416,-197621860352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280254944501,0,true,167338112768,167338112832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918768311051,0,false,-197458439744,-197458439680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523159162,0,true,11531264,11531328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500096390,0,false,-11531456,-11531392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1280266237653,0,true,167347811584,167347811648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨918757017899,0,false,-197471954624,-197471954560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391499562,0,true,167455383104,167455383168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨918631755990,0,false,-197621870528,-197621870464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069755209389,0,false,-30166487424,-30166487360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069796408613,0,false,-30124142976,-30124142912⟩
    { al := (1346811/8192000), au := (67383/409600), zl := (7999/8000), zu := 1,
      A := ⟨180765912465,180879863317⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329702,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167338112768,167338112832⟩ : DyadicInterval 40),(⟨-197458439744,-197458439680⟩ : DyadicInterval 40),(⟨747199990174,747200009504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329702,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11531386⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11531264,11531328⟩ : DyadicInterval 40),(⟨-11531456,-11531392⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨180754609877,180879871786⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167347811584,167347811648⟩ : DyadicInterval 40),(⟨-197471954624,-197471954560⟩ : DyadicInterval 40),(⟨747198116670,747198135999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455383104,167455383168⟩ : DyadicInterval 40),(⟨-197621870528,-197621870464⟩ : DyadicInterval 40),(⟨747177328272,747177347602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30166487424,-30124142912⟩ : DyadicInterval 40),(⟨777185455072,777206646592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167357518336,167455375872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197621860416,-197485480832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2663_ok : ecellOkT e2663 = true := by decide +kernel
theorem e2663_pos {a z : ℝ} (ha1 : ((1346811/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((67383/409600 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2663 e2663_ok ha1 ha2 hz1 hz2 hz

-- box ['67383/409600', '1348509/8192000', '1999/2000', '7997/8000']  interval_lower 8453349/34359738368
noncomputable def e2664 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491092,0,true,167455375808,167455375872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764460,0,false,-197621860416,-197621860352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441944,0,true,167553224576,167553224640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813608,0,false,-197758256768,-197758256704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280301051160,0,true,167377709504,167377709568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918722204392,0,false,-197513618048,-197513617984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280437569264,0,true,167494943872,167494943936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918585686288,0,false,-197677012800,-197677012736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546220558,0,true,34592192,34592256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477034994,0,false,-34593344,-34593280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557782428,0,true,46153664,46153728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465473124,0,false,-46155648,-46155584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625838,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626688,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280346266615,0,true,167416539456,167416539520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918676988937,0,false,-197567732480,-197567732416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280471514205,0,true,167524091968,167524092032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918551741347,0,false,-197717644352,-197717644288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069728877262,0,false,-30193552320,-30193552256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069770090008,0,false,-30151192960,-30151192896⟩
    { al := (67383/409600), au := (1348509/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨180879863316,180993814168⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329703,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405726,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167377709504,167377709568⟩ : DyadicInterval 40),(⟨-197513618048,-197513617984⟩ : DyadicInterval 40),(⟨747192340523,747192359853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167494943872,167494943936⟩ : DyadicInterval 40),(⟨-197677012800,-197677012736⟩ : DyadicInterval 40),(⟨747169678880,747169698209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34592782,46154652⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34592192,34592256⟩ : DyadicInterval 40),(⟨-34593344,-34593280⟩ : DyadicInterval 40),(⟨762123383039,762123402368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46153664,46153728⟩ : DyadicInterval 40),(⟨-46155648,-46155584⟩ : DyadicInterval 40),(⟨762123382606,762123401935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180834638839,180959886429⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167416539456,167416539520⟩ : DyadicInterval 40),(⟨-197567732480,-197567732416⟩ : DyadicInterval 40),(⟨747184836815,747184856145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167524091968,167524092032⟩ : DyadicInterval 40),(⟨-197717644352,-197717644288⟩ : DyadicInterval 40),(⟨747164041438,747164060768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30193552320,-30151192896⟩ : DyadicInterval 40),(⟨777198980064,777220179040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167455375808,167553224640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197758256768,-197621860352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2664_ok : ecellOkT e2664 = true := by decide +kernel
theorem e2664_pos {a z : ℝ} (ha1 : ((67383/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1348509/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2664 e2664_ok ha1 ha2 hz1 hz2 hz

-- box ['1348509/8192000', '674679/4096000', '1999/2000', '7997/8000']  interval_lower 135914265/549755813888
noncomputable def e2665 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441943,0,true,167553224576,167553224640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813609,0,false,-197758256768,-197758256704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392795,0,true,167651064640,167651064704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862757,0,false,-197894670080,-197894670016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280414945035,0,true,167475516224,167475516288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918608310517,0,false,-197649932800,-197649932736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280551477384,0,true,167592752384,167592752448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918471778168,0,false,-197813364864,-197813364800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546243227,0,true,34614848,34614912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477012325,0,false,-34616000,-34615936⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557812657,0,true,46183872,46183936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465442895,0,false,-46185856,-46185792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625836,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626687,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280460188978,0,true,167514367232,167514367296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918563066574,0,false,-197704088064,-197704088000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280585443692,0,true,167621916288,167621916352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918437811860,0,false,-197854027008,-197854026944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069691363958,0,false,-30232110720,-30232110656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069732605005,0,false,-30189720832,-30189720768⟩
    { al := (1348509/8192000), au := (674679/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨180993814167,181107765019⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405727,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167475516224,167475516288⟩ : DyadicInterval 40),(⟨-197649932800,-197649932736⟩ : DyadicInterval 40),(⟨747173435671,747173455001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167592752384,167592752448⟩ : DyadicInterval 40),(⟨-197813364864,-197813364800⟩ : DyadicInterval 40),(⟨747150757132,747150776462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34615451,46184881⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34614848,34614912⟩ : DyadicInterval 40),(⟨-34616000,-34615936⟩ : DyadicInterval 40),(⟨762123383038,762123402367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46183872,46183936⟩ : DyadicInterval 40),(⟨-46185856,-46185792⟩ : DyadicInterval 40),(⟨762123382603,762123401933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180948561202,181073815916⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167514367232,167514367296⟩ : DyadicInterval 40),(⟨-197704088064,-197704088000⟩ : DyadicInterval 40),(⟨747165922400,747165941729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167621916288,167621916352⟩ : DyadicInterval 40),(⟨-197854027008,-197854026944⟩ : DyadicInterval 40),(⟨747145112482,747145131812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30232110720,-30189720768⟩ : DyadicInterval 40),(⟨777218244000,777239458240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167553224576,167651064704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197894670080,-197758256704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2665_ok : ecellOkT e2665 = true := by decide +kernel
theorem e2665_pos {a z : ℝ} (ha1 : ((1348509/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((674679/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2665 e2665_ok ha1 ha2 hz1 hz2 hz

-- box ['67383/409600', '1348509/8192000', '7997/8000', '3999/4000']  interval_lower 270318527/1099511627776
noncomputable def e2666 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491092,0,true,167455375808,167455375872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764460,0,false,-197621860416,-197621860352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441944,0,true,167553224576,167553224640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813608,0,false,-197758256768,-197758256704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280323661143,0,true,167397126592,167397126656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918699594409,0,false,-197540677632,-197540677568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280460193491,0,true,167514371072,167514371136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918563062061,0,false,-197704093440,-197704093376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534689603,0,true,23061568,23061632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488565949,0,false,-23062080,-23062016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546243917,0,true,34615552,34615616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477011635,0,false,-34616704,-34616640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626686,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627293,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280357571508,0,true,167426247616,167426247680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918665684044,0,false,-197581262720,-197581262656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280482826247,0,true,167533805312,167533805376⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918540429305,0,false,-197731185024,-197731184960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069725153628,0,false,-30197379648,-30197379584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069766371303,0,false,-30155015104,-30155015040⟩
    { al := (67383/409600), au := (1348509/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨180879863316,180993814168⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329703,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405726,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167397126592,167397126656⟩ : DyadicInterval 40),(⟨-197540677632,-197540677568⟩ : DyadicInterval 40),(⟨747188588533,747188607862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167514371072,167514371136⟩ : DyadicInterval 40),(⟨-197704093440,-197704093376⟩ : DyadicInterval 40),(⟨747165921660,747165940989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23061827,34616141⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23061568,23061632⟩ : DyadicInterval 40),(⟨-23062080,-23062016⟩ : DyadicInterval 40),(⟨762123383324,762123402653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34615552,34615616⟩ : DyadicInterval 40),(⟨-34616704,-34616640⟩ : DyadicInterval 40),(⟨762123383038,762123402367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180845943732,180971198471⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167426247616,167426247680⟩ : DyadicInterval 40),(⟨-197581262720,-197581262656⟩ : DyadicInterval 40),(⟨747182960411,747182979740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167533805312,167533805376⟩ : DyadicInterval 40),(⟨-197731185024,-197731184960⟩ : DyadicInterval 40),(⟨747162162538,747162181868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30197379648,-30155015040⟩ : DyadicInterval 40),(⟨777200891136,777222092704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167455375808,167553224640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197758256768,-197621860352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2666_ok : ecellOkT e2666 = true := by decide +kernel
theorem e2666_pos {a z : ℝ} (ha1 : ((67383/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1348509/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2666 e2666_ok ha1 ha2 hz1 hz2 hz

-- box ['1348509/8192000', '674679/4096000', '7997/8000', '3999/4000']  interval_lower 135819599/549755813888
noncomputable def e2667 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441943,0,true,167553224576,167553224640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813609,0,false,-197758256768,-197758256704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392795,0,true,167651064640,167651064704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862757,0,false,-197894670080,-197894670016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280437569262,0,true,167494943872,167494943936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918585686290,0,false,-197677012800,-197677012736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280574115854,0,true,167612190144,167612190208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918449139698,0,false,-197840465920,-197840465856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534704715,0,true,23076672,23076736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488550837,0,false,-23077184,-23077120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546266588,0,true,34638208,34638272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476988964,0,false,-34639360,-34639296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626684,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627292,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280471500997,0,true,167524080640,167524080704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918551754555,0,false,-197717628544,-197717628480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280596762858,0,true,167631634880,167631634944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918426492694,0,false,-197867577920,-197867577856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069687635633,0,false,-30235942976,-30235942912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069728881611,0,false,-30193547840,-30193547776⟩
    { al := (1348509/8192000), au := (674679/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨180993814167,181107765019⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405727,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167494943872,167494943936⟩ : DyadicInterval 40),(⟨-197677012800,-197677012736⟩ : DyadicInterval 40),(⟨747169678880,747169698209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167612190144,167612190208⟩ : DyadicInterval 40),(⟨-197840465920,-197840465856⟩ : DyadicInterval 40),(⟨747146995105,747147014434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23076939,34638812⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23076672,23076736⟩ : DyadicInterval 40),(⟨-23077184,-23077120⟩ : DyadicInterval 40),(⟨762123383323,762123402652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34638208,34638272⟩ : DyadicInterval 40),(⟨-34639360,-34639296⟩ : DyadicInterval 40),(⟨762123383036,762123402365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180959873221,181085135082⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167524080640,167524080704⟩ : DyadicInterval 40),(⟨-197717628544,-197717628480⟩ : DyadicInterval 40),(⟨747164043625,747164062955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167631634880,167631634944⟩ : DyadicInterval 40),(⟨-197867577920,-197867577856⟩ : DyadicInterval 40),(⟨747143231209,747143250538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30235942976,-30193547776⟩ : DyadicInterval 40),(⟨777220157504,777241374368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167553224576,167651064704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197894670080,-197758256704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2667_ok : ecellOkT e2667 = true := by decide +kernel
theorem e2667_pos {a z : ℝ} (ha1 : ((1348509/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((674679/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2667 e2667_ok ha1 ha2 hz1 hz2 hz

-- box ['674679/4096000', '1350207/8192000', '1999/2000', '7997/8000']  interval_lower 273152877/1099511627776
noncomputable def e2668 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392794,0,true,167651064640,167651064704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862758,0,false,-197894670080,-197894670016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343646,0,true,167748895936,167748896000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911906,0,false,-198031100352,-198031100288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280528838911,0,true,167573314304,167573314368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918494416641,0,false,-197786264448,-197786264384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280665385503,0,true,167690552256,167690552320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918357870049,0,false,-197949733888,-197949733824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546265897,0,true,34637568,34637632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476989655,0,false,-34638720,-34638656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557842887,0,true,46214080,46214144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465412665,0,false,-46216128,-46216064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625833,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626685,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280574111344,0,true,167612186240,167612186304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918449144208,0,false,-197840460544,-197840460480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280699373173,0,true,167719731840,167719731904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918323882379,0,false,-197990426624,-197990426560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069653827046,0,false,-30270694720,-30270694656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069695096393,0,false,-30228274240,-30228274176⟩
    { al := (674679/4096000), au := (1350207/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨181107765018,181221715870⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521437,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167573314304,167573314368⟩ : DyadicInterval 40),(⟨-197786264448,-197786264384⟩ : DyadicInterval 40),(⟨747154518656,747154537985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167690552256,167690552320⟩ : DyadicInterval 40),(⟨-197949733888,-197949733824⟩ : DyadicInterval 40),(⟨747131823241,747131842570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34638121,46215111⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34637568,34637632⟩ : DyadicInterval 40),(⟨-34638720,-34638656⟩ : DyadicInterval 40),(⟨762123383036,762123402365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46214080,46214144⟩ : DyadicInterval 40),(⟨-46216128,-46216064⟩ : DyadicInterval 40),(⟨762123382633,762123401962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181062483568,181187745397⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167612186240,167612186304⟩ : DyadicInterval 40),(⟨-197840460544,-197840460480⟩ : DyadicInterval 40),(⟨747146995882,747147015212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167719731840,167719731904⟩ : DyadicInterval 40),(⟨-197990426624,-197990426560⟩ : DyadicInterval 40),(⟨747126171447,747126190777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30270694720,-30228274176⟩ : DyadicInterval 40),(⟨777237520704,777258750240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167651064640,167748896000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198031100352,-197894670016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2668_ok : ecellOkT e2668 = true := by decide +kernel
theorem e2668_pos {a z : ℝ} (ha1 : ((674679/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1350207/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2668 e2668_ok ha1 ha2 hz1 hz2 hz

-- box ['1350207/8192000', '84441/512000', '1999/2000', '7997/8000']  interval_lower 274480127/1099511627776
noncomputable def e2669 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343645,0,true,167748895936,167748896000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911907,0,false,-198031100352,-198031100288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294497,0,true,167846718592,167846718656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961055,0,false,-198167547520,-198167547456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280642732787,0,true,167671103616,167671103680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918380522765,0,false,-197922613056,-197922612992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280779293623,0,true,167788343360,167788343424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918243961929,0,false,-198086119744,-198086119680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546288570,0,true,34660224,34660288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476966982,0,false,-34661376,-34661312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557873120,0,true,46244352,46244416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465382432,0,false,-46246336,-46246272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625830,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626684,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280688033698,0,true,167709996608,167709996672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918335221854,0,false,-197976849920,-197976849856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280813302659,0,true,167817538752,167817538816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918209952893,0,false,-198126843200,-198126843136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069616266521,0,false,-30309304384,-30309304320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069657564178,0,false,-30266853312,-30266853248⟩
    { al := (1350207/8192000), au := (84441/512000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨181221715869,181335666721⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521438,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561057,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167671103616,167671103680⟩ : DyadicInterval 40),(⟨-197922613056,-197922612992⟩ : DyadicInterval 40),(⟨747135589577,747135608907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167788343360,167788343424⟩ : DyadicInterval 40),(⟨-198086119744,-198086119680⟩ : DyadicInterval 40),(⟨747112877225,747112896554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34660794,46245344⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34660224,34660288⟩ : DyadicInterval 40),(⟨-34661376,-34661312⟩ : DyadicInterval 40),(⟨762123383035,762123402364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46244352,46244416⟩ : DyadicInterval 40),(⟨-46246336,-46246272⟩ : DyadicInterval 40),(⟨762123382598,762123401927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181176405922,181301674883⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167709996608,167709996672⟩ : DyadicInterval 40),(⟨-197976849920,-197976849856⟩ : DyadicInterval 40),(⟨747128057190,747128076519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167817538752,167817538816⟩ : DyadicInterval 40),(⟨-198126843200,-198126843136⟩ : DyadicInterval 40),(⟨747107218257,747107237587⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30309304384,-30266853248⟩ : DyadicInterval 40),(⟨777256810240,777278055072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167748895936,167846718656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198167547520,-198031100288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2669_ok : ecellOkT e2669 = true := by decide +kernel
theorem e2669_pos {a z : ℝ} (ha1 : ((1350207/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84441/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2669 e2669_ok ha1 ha2 hz1 hz2 hz

-- box ['674679/4096000', '1350207/8192000', '7997/8000', '3999/4000']  interval_lower 68240801/274877906944
noncomputable def e2670 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392794,0,true,167651064640,167651064704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862758,0,false,-197894670080,-197894670016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343646,0,true,167748895936,167748896000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911906,0,false,-198031100352,-198031100288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280551477382,0,true,167592752384,167592752448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918471778170,0,false,-197813364864,-197813364800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280688038218,0,true,167710000512,167710000576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918335217334,0,false,-197976855360,-197976855296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534719829,0,true,23091776,23091840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488535723,0,false,-23092352,-23092288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546289261,0,true,34660928,34660992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476966291,0,false,-34662080,-34662016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626683,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627292,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280585430481,0,true,167621904960,167621905024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918437825071,0,false,-197854011200,-197854011136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280710699461,0,true,167729455744,167729455808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918312556091,0,false,-198003987712,-198003987648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069650094027,0,false,-30274531968,-30274531904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069691368311,0,false,-30232106240,-30232106176⟩
    { al := (674679/4096000), au := (1350207/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨181107765018,181221715870⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521437,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167592752384,167592752448⟩ : DyadicInterval 40),(⟨-197813364864,-197813364800⟩ : DyadicInterval 40),(⟨747150757133,747150776462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167710000512,167710000576⟩ : DyadicInterval 40),(⟨-197976855360,-197976855296⟩ : DyadicInterval 40),(⟨747128056436,747128075766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23092053,34661485⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23091776,23091840⟩ : DyadicInterval 40),(⟨-23092352,-23092288⟩ : DyadicInterval 40),(⟨762123383355,762123402684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34660928,34660992⟩ : DyadicInterval 40),(⟨-34662080,-34662016⟩ : DyadicInterval 40),(⟨762123383035,762123402364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181073802705,181199071685⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167621904960,167621905024⟩ : DyadicInterval 40),(⟨-197854011200,-197854011136⟩ : DyadicInterval 40),(⟨747145114672,747145134001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167729455744,167729455808⟩ : DyadicInterval 40),(⟨-198003987712,-198003987648⟩ : DyadicInterval 40),(⟨747124287734,747124307064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30274531968,-30232106176⟩ : DyadicInterval 40),(⟨777239436704,777260668864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167651064640,167748896000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198031100352,-197894670016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2670_ok : ecellOkT e2670 = true := by decide +kernel
theorem e2670_pos {a z : ℝ} (ha1 : ((674679/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1350207/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2670 e2670_ok ha1 ha2 hz1 hz2 hz

-- box ['1350207/8192000', '84441/512000', '7997/8000', '3999/4000']  interval_lower 8571565/34359738368
noncomputable def e2671 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343645,0,true,167748895936,167748896000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911907,0,false,-198031100352,-198031100288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294497,0,true,167846718592,167846718656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961055,0,false,-198167547520,-198167547456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280665385501,0,true,167690552256,167690552320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918357870051,0,false,-197949733888,-197949733824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280801960581,0,true,167807802112,167807802176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918221294971,0,false,-198113261696,-198113261632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534734945,0,true,23106880,23106944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488520607,0,false,-23107456,-23107392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546311936,0,true,34683584,34683648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476943616,0,false,-34684736,-34684672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626681,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627291,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280699359959,0,true,167719720512,167719720576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918323895593,0,false,-197990410816,-197990410752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280824636067,0,true,167827267840,167827267904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918198619485,0,false,-198140414464,-198140414400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069612528807,0,false,-30313146560,-30313146496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069653831402,0,false,-30270690304,-30270690240⟩
    { al := (1350207/8192000), au := (84441/512000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨181221715869,181335666721⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521438,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561057,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167690552256,167690552320⟩ : DyadicInterval 40),(⟨-197949733888,-197949733824⟩ : DyadicInterval 40),(⟨747131823241,747131842570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167807802112,167807802176⟩ : DyadicInterval 40),(⟨-198113261696,-198113261632⟩ : DyadicInterval 40),(⟨747109105664,747109124993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23107169,34684160⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23106880,23106944⟩ : DyadicInterval 40),(⟨-23107456,-23107392⟩ : DyadicInterval 40),(⟨762123383354,762123402683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34683584,34683648⟩ : DyadicInterval 40),(⟨-34684736,-34684672⟩ : DyadicInterval 40),(⟨762123383033,762123402362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181187732183,181313008291⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167719720512,167719720576⟩ : DyadicInterval 40),(⟨-197990410816,-197990410752⟩ : DyadicInterval 40),(⟨747126173641,747126192970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167827267840,167827267904⟩ : DyadicInterval 40),(⟨-198140414464,-198140414400⟩ : DyadicInterval 40),(⟨747105332176,747105351505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30313146560,-30270690240⟩ : DyadicInterval 40),(⟨777258728736,777279976160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167748895936,167846718656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198167547520,-198031100288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2671_ok : ecellOkT e2671 = true := by decide +kernel
theorem e2671_pos {a z : ℝ} (ha1 : ((1350207/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84441/512000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2671 e2671_ok ha1 ha2 hz1 hz2 hz

-- box ['67383/409600', '1348509/8192000', '3999/4000', '7999/8000']  interval_lower 270129519/1099511627776
noncomputable def e2672 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491092,0,true,167455375808,167455375872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764460,0,false,-197621860416,-197621860352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441944,0,true,167553224576,167553224640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813608,0,false,-197758256768,-197758256704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280346271126,0,true,167416543360,167416543424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918676984426,0,false,-197567737856,-197567737792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280482817718,0,true,167533798016,167533798080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918540437834,0,false,-197731174784,-197731174720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523158590,0,true,11530752,11530816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500096962,0,false,-11530880,-11530816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534705347,0,true,23077312,23077376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488550205,0,false,-23077824,-23077760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627291,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280368876434,0,true,167435955712,167435955776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918654379118,0,false,-197594793216,-197594793152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280494138320,0,true,167543518592,167543518656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918529117232,0,false,-197744725888,-197744725824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069721429750,0,false,-30201207232,-30201207168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069762652353,0,false,-30158837440,-30158837376⟩
    { al := (67383/409600), au := (1348509/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨180879863316,180993814168⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329703,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405726,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167416543360,167416543424⟩ : DyadicInterval 40),(⟨-197567737856,-197567737792⟩ : DyadicInterval 40),(⟨747184836039,747184855369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167533798016,167533798080⟩ : DyadicInterval 40),(⟨-197731174784,-197731174720⟩ : DyadicInterval 40),(⟨747162163926,747162183256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11530814,23077571⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11530752,11530816⟩ : DyadicInterval 40),(⟨-11530880,-11530816⟩ : DyadicInterval 40),(⟨762123383495,762123402824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23077312,23077376⟩ : DyadicInterval 40),(⟨-23077824,-23077760⟩ : DyadicInterval 40),(⟨762123383323,762123402652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180857248658,180982510544⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167435955712,167435955776⟩ : DyadicInterval 40),(⟨-197594793216,-197594793152⟩ : DyadicInterval 40),(⟨747181083906,747181103236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167543518592,167543518656⟩ : DyadicInterval 40),(⟨-197744725888,-197744725824⟩ : DyadicInterval 40),(⟨747160283511,747160302841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30201207232,-30158837376⟩ : DyadicInterval 40),(⟨777202802304,777224006496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167455375808,167553224640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197758256768,-197621860352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2672_ok : ecellOkT e2672 = true := by decide +kernel
theorem e2672_pos {a z : ℝ} (ha1 : ((67383/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1348509/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2672 e2672_ok ha1 ha2 hz1 hz2 hz

-- box ['1348509/8192000', '674679/4096000', '3999/4000', '7999/8000']  interval_lower 271449871/1099511627776
noncomputable def e2673 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441943,0,true,167553224576,167553224640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813609,0,false,-197758256768,-197758256704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392795,0,true,167651064640,167651064704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862757,0,false,-197894670080,-197894670016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280460193489,0,true,167514371072,167514371136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918563062063,0,false,-197704093440,-197704093376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280596754325,0,true,167631627520,167631627584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918426501227,0,false,-197867567680,-197867567616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523166147,0,true,11538304,11538368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500089405,0,false,-11538432,-11538368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534720461,0,true,23092416,23092480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488535091,0,false,-23092928,-23092864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627290,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280482813039,0,true,167533793984,167533794048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918540442513,0,false,-197731169216,-197731169152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280608082048,0,true,167641353408,167641353472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918415173504,0,false,-197881128960,-197881128896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069683907066,0,false,-30239775552,-30239775488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069725157977,0,false,-30197375168,-30197375104⟩
    { al := (1348509/8192000), au := (674679/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨180993814167,181107765019⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405727,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167514371072,167514371136⟩ : DyadicInterval 40),(⟨-197704093440,-197704093376⟩ : DyadicInterval 40),(⟨747165921660,747165940990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167631627520,167631627584⟩ : DyadicInterval 40),(⟨-197867567680,-197867567616⟩ : DyadicInterval 40),(⟨747143232636,747143251966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11538371,23092685⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11538304,11538368⟩ : DyadicInterval 40),(⟨-11538432,-11538368⟩ : DyadicInterval 40),(⟨762123383494,762123402823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23092416,23092480⟩ : DyadicInterval 40),(⟨-23092928,-23092864⟩ : DyadicInterval 40),(⟨762123383322,762123402651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180971185263,181096454272⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167533793984,167533794048⟩ : DyadicInterval 40),(⟨-197731169216,-197731169152⟩ : DyadicInterval 40),(⟨747162164726,747162184055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167641353408,167641353472⟩ : DyadicInterval 40),(⟨-197881128960,-197881128896⟩ : DyadicInterval 40),(⟨747141349782,747141369112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30239775552,-30197375104⟩ : DyadicInterval 40),(⟨777222071168,777243290656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167553224576,167651064704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197894670080,-197758256704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2673_ok : ecellOkT e2673 = true := by decide +kernel
theorem e2673_pos {a z : ℝ} (ha1 : ((1348509/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((674679/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2673 e2673_ok ha1 ha2 hz1 hz2 hz

-- box ['67383/409600', '1348509/8192000', '7999/8000', '1']  interval_lower 269940713/1099511627776
noncomputable def e2674 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491092,0,true,167455375808,167455375872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764460,0,false,-197621860416,-197621860352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441944,0,true,167553224576,167553224640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813608,0,false,-197758256768,-197758256704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280368881108,0,true,167435959744,167435959808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918654374444,0,false,-197594798784,-197594798720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523166719,0,true,11538880,11538944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500088833,0,false,-11539008,-11538944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1280380181381,0,true,167445663744,167445663808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨918643074171,0,false,-197608323840,-197608323776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505450419,0,true,167553231872,167553231936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨918517805133,0,false,-197758266944,-197758266880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069717705631,0,false,-30205035072,-30205035008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069758933165,0,false,-30162660032,-30162659968⟩
    { al := (67383/409600), au := (1348509/8192000), zl := (7999/8000), zu := 1,
      A := ⟨180879863316,180993814168⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329703,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405726,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167435959744,167435959808⟩ : DyadicInterval 40),(⟨-197594798784,-197594798720⟩ : DyadicInterval 40),(⟨747181083109,747181102438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405726,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11538943⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11538880,11538944⟩ : DyadicInterval 40),(⟨-11539008,-11538944⟩ : DyadicInterval 40),(⟨762123383494,762123402823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨180868553605,180993822643⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167445663744,167445663808⟩ : DyadicInterval 40),(⟨-197608323840,-197608323776⟩ : DyadicInterval 40),(⟨747179207250,747179226579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553231872,167553231936⟩ : DyadicInterval 40),(⟨-197758266944,-197758266880⟩ : DyadicInterval 40),(⟨747158404321,747158423650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30205035072,-30162659968⟩ : DyadicInterval 40),(⟨777204713600,777225920416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167455375808,167553224640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197758256768,-197621860352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2674_ok : ecellOkT e2674 = true := by decide +kernel
theorem e2674_pos {a z : ℝ} (ha1 : ((67383/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1348509/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2674 e2674_ok ha1 ha2 hz1 hz2 hz

-- box ['1348509/8192000', '674679/4096000', '7999/8000', '1']  interval_lower 271260791/1099511627776
noncomputable def e2675 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441943,0,true,167553224576,167553224640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813609,0,false,-197758256768,-197758256704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392795,0,true,167651064640,167651064704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862757,0,false,-197894670080,-197894670016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280482817716,0,true,167533798016,167533798080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918540437836,0,false,-197731174784,-197731174720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523174277,0,true,11546432,11546496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500081275,0,false,-11546624,-11546560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1280494125111,0,true,167543507264,167543507328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨918529130441,0,false,-197744710080,-197744710016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619401273,0,true,167651071872,167651071936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨918403854279,0,false,-197894680256,-197894680192⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069680178255,0,false,-30243608320,-30243608256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069721434099,0,false,-30201202752,-30201202688⟩
    { al := (1348509/8192000), au := (674679/4096000), zl := (7999/8000), zu := 1,
      A := ⟨180993814167,181107765019⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405727,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167533798016,167533798080⟩ : DyadicInterval 40),(⟨-197731174784,-197731174720⟩ : DyadicInterval 40),(⟨747162163926,747162183256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11546501⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11546432,11546496⟩ : DyadicInterval 40),(⟨-11546624,-11546560⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨180982497335,181107773497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167543507264,167543507328⟩ : DyadicInterval 40),(⟨-197744710080,-197744710016⟩ : DyadicInterval 40),(⟨747160285699,747160305028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651071872,167651071936⟩ : DyadicInterval 40),(⟨-197894680256,-197894680192⟩ : DyadicInterval 40),(⟨747139468255,747139487585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30243608320,-30201202688⟩ : DyadicInterval 40),(⟨777223984960,777245207040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167553224576,167651064704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197894670080,-197758256704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2675_ok : ecellOkT e2675 = true := by decide +kernel
theorem e2675_pos {a z : ℝ} (ha1 : ((1348509/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((674679/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2675 e2675_ok ha1 ha2 hz1 hz2 hz

-- box ['674679/4096000', '1350207/8192000', '3999/4000', '7999/8000']  interval_lower 272773499/1099511627776
noncomputable def e2676 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392794,0,true,167651064640,167651064704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862758,0,false,-197894670080,-197894670016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343646,0,true,167748895936,167748896000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911906,0,false,-198031100352,-198031100288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280574115852,0,true,167612190144,167612190208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918449139700,0,false,-197840465920,-197840465856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280710690932,0,true,167729448384,167729448448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918312564620,0,false,-198003977536,-198003977472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523173703,0,true,11545856,11545920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500081849,0,false,-11546048,-11545984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534735577,0,true,23107520,23107584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488519975,0,false,-23108096,-23108032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627290,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280596749647,0,true,167631623552,167631623616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918426505905,0,false,-197867562112,-197867562048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280722025773,0,true,167739179520,167739179584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918301229779,0,false,-198017548992,-198017548928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069646360767,0,false,-30278369472,-30278369408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069687639985,0,false,-30235938496,-30235938432⟩
    { al := (674679/4096000), au := (1350207/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨181107765018,181221715870⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521437,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167612190144,167612190208⟩ : DyadicInterval 40),(⟨-197840465920,-197840465856⟩ : DyadicInterval 40),(⟨747146995105,747147014434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167729448384,167729448448⟩ : DyadicInterval 40),(⟨-198003977536,-198003977472⟩ : DyadicInterval 40),(⟨747124289189,747124308519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11545927,23107801⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11545856,11545920⟩ : DyadicInterval 40),(⟨-11546048,-11545984⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23107520,23107584⟩ : DyadicInterval 40),(⟨-23108096,-23108032⟩ : DyadicInterval 40),(⟨762123383354,762123402683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181085121871,181210397997⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167631623552,167631623616⟩ : DyadicInterval 40),(⟨-197867562112,-197867562048⟩ : DyadicInterval 40),(⟨747143233399,747143252729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167739179520,167739179584⟩ : DyadicInterval 40),(⟨-198017548992,-198017548928⟩ : DyadicInterval 40),(⟨747122403932,747122423261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30278369472,-30235938432⟩ : DyadicInterval 40),(⟨777241352832,777262587616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167651064640,167748896000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198031100352,-197894670016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2676_ok : ecellOkT e2676 = true := by decide +kernel
theorem e2676_pos {a z : ℝ} (ha1 : ((674679/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1350207/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2676 e2676_ok ha1 ha2 hz1 hz2 hz

-- box ['1350207/8192000', '84441/512000', '3999/4000', '7999/8000']  interval_lower 34262483/137438953472
noncomputable def e2677 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343645,0,true,167748895936,167748896000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911907,0,false,-198031100352,-198031100288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294497,0,true,167846718592,167846718656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961055,0,false,-198167547520,-198167547456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280688038216,0,true,167710000512,167710000576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918335217336,0,false,-197976855360,-197976855296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280824627539,0,true,167827260544,167827260608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918198628013,0,false,-198140404288,-198140404224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523181261,0,true,11553408,11553472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500074291,0,false,-11553600,-11553536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534750693,0,true,23122624,23122688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488504859,0,false,-23123200,-23123136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627289,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280710686247,0,true,167729444352,167729444416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918312569305,0,false,-198003971904,-198003971840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280835969504,0,true,167836996864,167836996928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918187286048,0,false,-198153985984,-198153985920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069608790850,0,false,-30316989056,-30316988992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069650098384,0,false,-30274527488,-30274527424⟩
    { al := (1350207/8192000), au := (84441/512000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨181221715869,181335666721⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521438,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561057,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167710000512,167710000576⟩ : DyadicInterval 40),(⟨-197976855360,-197976855296⟩ : DyadicInterval 40),(⟨747128056436,747128075766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167827260544,167827260608⟩ : DyadicInterval 40),(⟨-198140404288,-198140404224⟩ : DyadicInterval 40),(⟨747105333595,747105352925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11553485,23122917⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11553408,11553472⟩ : DyadicInterval 40),(⟨-11553600,-11553536⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23122624,23122688⟩ : DyadicInterval 40),(⟨-23123200,-23123136⟩ : DyadicInterval 40),(⟨762123383353,762123402682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181199058471,181324341728⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167729444352,167729444416⟩ : DyadicInterval 40),(⟨-198003971904,-198003971840⟩ : DyadicInterval 40),(⟨747124289965,747124309295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167836996864,167836996928⟩ : DyadicInterval 40),(⟨-198153985984,-198153985920⟩ : DyadicInterval 40),(⟨747103445994,747103465323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30316989056,-30274527424⟩ : DyadicInterval 40),(⟨777260647328,777281897408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167748895936,167846718656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198167547520,-198031100288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2677_ok : ecellOkT e2677 = true := by decide +kernel
theorem e2677_pos {a z : ℝ} (ha1 : ((1350207/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84441/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2677 e2677_ok ha1 ha2 hz1 hz2 hz

-- box ['674679/4096000', '1350207/8192000', '7999/8000', '1']  interval_lower 272583951/1099511627776
noncomputable def e2678 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392794,0,true,167651064640,167651064704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862758,0,false,-197894670080,-197894670016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343646,0,true,167748895936,167748896000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911906,0,false,-198031100352,-198031100288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280596754323,0,true,167631627520,167631627584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918426501229,0,false,-197867567680,-197867567616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523181835,0,true,11553984,11554048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500073717,0,false,-11554176,-11554112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1280608068837,0,true,167641342080,167641342144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨918415186715,0,false,-197881113152,-197881113088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733352115,0,true,167748903232,167748903296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨918289903437,0,false,-198031110464,-198031110400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069642627264,0,false,-30282207232,-30282207168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069683911419,0,false,-30239771072,-30239771008⟩
    { al := (674679/4096000), au := (1350207/8192000), zl := (7999/8000), zu := 1,
      A := ⟨181107765018,181221715870⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521437,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167631627520,167631627584⟩ : DyadicInterval 40),(⟨-197867567680,-197867567616⟩ : DyadicInterval 40),(⟨747143232637,747143251966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521437,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11554059⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11553984,11554048⟩ : DyadicInterval 40),(⟨-11554176,-11554112⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨181096441061,181221724339⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167641342080,167641342144⟩ : DyadicInterval 40),(⟨-197881113152,-197881113088⟩ : DyadicInterval 40),(⟨747141351973,747141371303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748903232,167748903296⟩ : DyadicInterval 40),(⟨-198031110464,-198031110400⟩ : DyadicInterval 40),(⟨747120520002,747120539331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30282207232,-30239771008⟩ : DyadicInterval 40),(⟨777243269120,777264506496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167651064640,167748896000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198031100352,-197894670016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2678_ok : ecellOkT e2678 = true := by decide +kernel
theorem e2678_pos {a z : ℝ} (ha1 : ((674679/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1350207/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2678 e2678_ok ha1 ha2 hz1 hz2 hz

-- box ['1350207/8192000', '84441/512000', '7999/8000', '1']  interval_lower 17119361/68719476736
noncomputable def e2679 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343645,0,true,167748895936,167748896000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911907,0,false,-198031100352,-198031100288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294497,0,true,167846718592,167846718656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961055,0,false,-198167547520,-198167547456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280710690930,0,true,167729448384,167729448448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918312564622,0,false,-198003977536,-198003977472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523189393,0,true,11561536,11561600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500066159,0,false,-11561728,-11561664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1280722012558,0,true,167739168128,167739168192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨918301242994,0,false,-198017533184,-198017533120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847302969,0,true,167846725888,167846725952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨918175952583,0,false,-198167557632,-198167557568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069605052650,0,false,-30320831744,-30320831680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069646365124,0,false,-30278364992,-30278364928⟩
    { al := (1350207/8192000), au := (84441/512000), zl := (7999/8000), zu := 1,
      A := ⟨181221715869,181335666721⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521438,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561057,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167729448384,167729448448⟩ : DyadicInterval 40),(⟨-198003977536,-198003977472⟩ : DyadicInterval 40),(⟨747124289190,747124308519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561057,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11561617⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11561536,11561600⟩ : DyadicInterval 40),(⟨-11561728,-11561664⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨181210384782,181335675193⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167739168128,167739168192⟩ : DyadicInterval 40),(⟨-198017533184,-198017533120⟩ : DyadicInterval 40),(⟨747122406163,747122425493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846725888,167846725952⟩ : DyadicInterval 40),(⟨-198167557632,-198167557568⟩ : DyadicInterval 40),(⟨747101559620,747101578949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30320831744,-30278364928⟩ : DyadicInterval 40),(⟨777262566080,777283818752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167748895936,167846718656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198167547520,-198031100288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2679_ok : ecellOkT e2679 = true := by decide +kernel
theorem e2679_pos {a z : ℝ} (ha1 : ((1350207/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84441/512000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2679 e2679_ok ha1 ha2 hz1 hz2 hz

-- box ['84441/512000', '270381/1638400', '999/1000', '7993/8000']  interval_lower 276571673/1099511627776
noncomputable def e2680 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294496,0,true,167846718592,167846718656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961056,0,false,-198167547520,-198167547456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245348,0,true,167944532544,167944532608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010204,0,false,-198304011584,-198304011520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280665958829,0,true,167691044480,167691044544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918357296723,0,false,-197950420288,-197950420224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280802476933,0,true,167808245376,167808245440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918220778619,0,false,-198113880000,-198113879936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592555397,0,true,80924608,80924672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430700155,0,false,-80930624,-80930560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604177740,0,true,92546048,92546112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419077812,0,false,-92553920,-92553856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619985,0,false,-7808,-7744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621820,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280756622819,0,true,167768880960,167768881024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918266632733,0,false,-198058973952,-198058973888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280881870303,0,true,167876398912,167876398976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918141385249,0,false,-198208952640,-198208952576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069593649608,0,false,-30332553664,-30332553600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069634955808,0,false,-30290092928,-30290092864⟩
    { al := (84441/512000), au := (270381/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨181335666720,181449617572⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561058,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588522,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167691044480,167691044544⟩ : DyadicInterval 40),(⟨-197950420288,-197950420224⟩ : DyadicInterval 40),(⟨747131727905,747131747235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167808245376,167808245440⟩ : DyadicInterval 40),(⟨-198113880000,-198113879936⟩ : DyadicInterval 40),(⟨747109019744,747109039074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80927621,92549964⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80924608,80924672⟩ : DyadicInterval 40),(⟨-80930624,-80930560⟩ : DyadicInterval 40),(⟨762123380603,762123399932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92546048,92546112⟩ : DyadicInterval 40),(⟨-92553920,-92553856⟩ : DyadicInterval 40),(⟨762123379697,762123399027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7808,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123406784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181244995043,181370242527⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167768880960,167768881024⟩ : DyadicInterval 40),(⟨-198058973952,-198058973888⟩ : DyadicInterval 40),(⟨747116648986,747116668315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167876398912,167876398976⟩ : DyadicInterval 40),(⟨-198208952640,-198208952576⟩ : DyadicInterval 40),(⟨747095805562,747095824892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30332553664,-30290092864⟩ : DyadicInterval 40),(⟨777268430048,777289679712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167846718592,167944532608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198304011584,-198167547456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2680_ok : ecellOkT e2680 = true := by decide +kernel
theorem e2680_pos {a z : ℝ} (ha1 : ((84441/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((270381/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2680 e2680_ok ha1 ha2 hz1 hz2 hz

-- box ['270381/1638400', '676377/4096000', '999/1000', '7993/8000']  interval_lower 277906921/1099511627776
noncomputable def e2681 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245347,0,true,167944532544,167944532608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010205,0,false,-198304011584,-198304011520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196199,0,true,168042337728,168042337792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059353,0,false,-198440492672,-198440492608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280779795729,0,true,167788774400,167788774464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918243459823,0,false,-198086721024,-198086720960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280916328077,0,true,167905977152,167905977216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918106927475,0,false,-198250218048,-198250217984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592608306,0,true,80977536,80977600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430647246,0,false,-80983552,-80983488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604238214,0,true,92606528,92606592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419017338,0,false,-92614400,-92614336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619975,0,false,-7808,-7744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621812,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280870516694,0,true,167866652928,167866652992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918152738858,0,false,-198195356352,-198195356288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280995771295,0,true,167974167424,167974167488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918027484257,0,false,-198345362176,-198345362112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069556060670,0,false,-30371194752,-30371194688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069597395168,0,false,-30328703360,-30328703296⟩
    { al := (270381/1638400), au := (676377/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨181449617571,181563568423⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588523,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167788774400,167788774464⟩ : DyadicInterval 40),(⟨-198086721024,-198086720960⟩ : DyadicInterval 40),(⟨747112793709,747112813038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167905977152,167905977216⟩ : DyadicInterval 40),(⟨-198250218048,-198250217984⟩ : DyadicInterval 40),(⟨747090068615,747090087945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80980530,92610438⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80977536,80977600⟩ : DyadicInterval 40),(⟨-80983552,-80983488⟩ : DyadicInterval 40),(⟨762123380595,762123399924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92606528,92606592⟩ : DyadicInterval 40),(⟨-92614400,-92614336⟩ : DyadicInterval 40),(⟨762123379687,762123399016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7808,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123406784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181358888918,181484143519⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167866652928,167866652992⟩ : DyadicInterval 40),(⟨-198195356352,-198195356288⟩ : DyadicInterval 40),(⟨747097695613,747097714942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167974167424,167974167488⟩ : DyadicInterval 40),(⟨-198345362176,-198345362112⟩ : DyadicInterval 40),(⟨747076837672,747076857002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30371194752,-30328703296⟩ : DyadicInterval 40),(⟨777287735264,777309000256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167944532544,168042337792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198440492672,-198304011520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2681_ok : ecellOkT e2681 = true := by decide +kernel
theorem e2681_pos {a z : ℝ} (ha1 : ((270381/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((676377/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2681 e2681_ok ha1 ha2 hz1 hz2 hz

-- box ['84441/512000', '270381/1638400', '7993/8000', '3997/4000']  interval_lower 138190731/549755813888
noncomputable def e2682 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294496,0,true,167846718592,167846718656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961056,0,false,-198167547520,-198167547456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245348,0,true,167944532544,167944532608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010204,0,false,-198304011584,-198304011520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280688625787,0,true,167710504960,167710505024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918334629765,0,false,-197977558848,-197977558784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280825158135,0,true,167827716032,167827716096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918198097417,0,false,-198141039616,-198141039552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580994446,0,true,69364480,69364544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442261106,0,false,-69368896,-69368832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592609232,0,true,80978432,80978496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430646320,0,false,-80984448,-80984384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621811,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623400,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280767956088,0,true,167778610368,167778610432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918255299464,0,false,-198072544192,-198072544128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280893210725,0,true,167886133504,167886133568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918130044827,0,false,-198222533376,-198222533312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069589908167,0,false,-30336399808,-30336399744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069631219309,0,false,-30293933824,-30293933760⟩
    { al := (84441/512000), au := (270381/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨181335666720,181449617572⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561058,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588522,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167710504960,167710505024⟩ : DyadicInterval 40),(⟨-197977558848,-197977558784⟩ : DyadicInterval 40),(⟨747127958725,747127978054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167827716032,167827716096⟩ : DyadicInterval 40),(⟨-198141039616,-198141039552⟩ : DyadicInterval 40),(⟨747105245272,747105264602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69366670,80981456⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69364480,69364544⟩ : DyadicInterval 40),(⟨-69368896,-69368832⟩ : DyadicInterval 40),(⟨762123381383,762123400712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80978432,80978496⟩ : DyadicInterval 40),(⟨-80984448,-80984384⟩ : DyadicInterval 40),(⟨762123380595,762123399924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181256328312,181381582949⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167778610368,167778610432⟩ : DyadicInterval 40),(⟨-198072544192,-198072544128⟩ : DyadicInterval 40),(⟨747114763515,747114782844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167886133504,167886133568⟩ : DyadicInterval 40),(⟨-198222533376,-198222533312⟩ : DyadicInterval 40),(⟨747093917609,747093936938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30336399808,-30293933760⟩ : DyadicInterval 40),(⟨777270350496,777291602784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167846718592,167944532608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198304011584,-198167547456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2682_ok : ecellOkT e2682 = true := by decide +kernel
theorem e2682_pos {a z : ℝ} (ha1 : ((84441/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((270381/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2682 e2682_ok ha1 ha2 hz1 hz2 hz

-- box ['270381/1638400', '676377/4096000', '7993/8000', '3997/4000']  interval_lower 277716151/1099511627776
noncomputable def e2683 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245347,0,true,167944532544,167944532608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010205,0,false,-198304011584,-198304011520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196199,0,true,168042337728,168042337792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059353,0,false,-198440492672,-198440492608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280802476931,0,true,167808245376,167808245440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918220778621,0,false,-198113880000,-198113879936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280939023523,0,true,167925458304,167925458368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918084232029,0,false,-198277398080,-198277398016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581039797,0,true,69409792,69409856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442215755,0,false,-69414272,-69414208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592662147,0,true,81031360,81031424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430593405,0,false,-81037376,-81037312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621803,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623395,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280881857085,0,true,167876387584,167876387648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918141398467,0,false,-198208936832,-198208936768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281007118840,0,true,167983907264,167983907328⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918016136712,0,false,-198358953088,-198358953024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069552314527,0,false,-30375045824,-30375045760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069593653970,0,false,-30332549184,-30332549120⟩
    { al := (270381/1638400), au := (676377/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨181449617571,181563568423⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588523,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167808245376,167808245440⟩ : DyadicInterval 40),(⟨-198113880000,-198113879936⟩ : DyadicInterval 40),(⟨747109019745,747109039074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167925458304,167925458368⟩ : DyadicInterval 40),(⟨-198277398080,-198277398016⟩ : DyadicInterval 40),(⟨747086289352,747086308682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69412021,81034371⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69409792,69409856⟩ : DyadicInterval 40),(⟨-69414272,-69414208⟩ : DyadicInterval 40),(⟨762123381409,762123400739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81031360,81031424⟩ : DyadicInterval 40),(⟨-81037376,-81037312⟩ : DyadicInterval 40),(⟨762123380587,762123399916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181370229309,181495491064⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167876387584,167876387648⟩ : DyadicInterval 40),(⟨-198208936832,-198208936768⟩ : DyadicInterval 40),(⟨747095807761,747095827091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167983907264,167983907328⟩ : DyadicInterval 40),(⟨-198358953088,-198358953024⟩ : DyadicInterval 40),(⟨747074947308,747074966637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30375045824,-30332549120⟩ : DyadicInterval 40),(⟨777289658176,777310925792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167944532544,168042337792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198440492672,-198304011520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2683_ok : ecellOkT e2683 = true := by decide +kernel
theorem e2683_pos {a z : ℝ} (ha1 : ((270381/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((676377/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2683 e2683_ok ha1 ha2 hz1 hz2 hz

-- box ['676377/4096000', '1353603/8192000', '999/1000', '7993/8000']  interval_lower 69811307/274877906944
noncomputable def e2684 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196198,0,true,168042337728,168042337792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059354,0,false,-198440492672,-198440492608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147050,0,true,168140134272,168140134336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108502,0,false,-198576990656,-198576990592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280893632629,0,true,167886495680,167886495744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918129622923,0,false,-198223038592,-198223038528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281030179221,0,true,168003700224,168003700288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917993076331,0,false,-198386572992,-198386572928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592661220,0,true,81030400,81030464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430594332,0,false,-81036480,-81036416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604298690,0,true,92667008,92667072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418956862,0,false,-92674880,-92674816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619965,0,false,-7872,-7808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621804,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280984410565,0,true,167964416192,167964416256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918038844987,0,false,-198331755648,-198331755584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281109672295,0,true,168071927232,168071927296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917913583257,0,false,-198481788672,-198481788608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069518448131,0,false,-30409861376,-30409861312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069559810932,0,false,-30367339456,-30367339392⟩
    { al := (676377/4096000), au := (1353603/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨181563568422,181677519274⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167886495680,167886495744⟩ : DyadicInterval 40),(⟨-198223038592,-198223038528⟩ : DyadicInterval 40),(⟨747093847342,747093866672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168003700224,168003700288⟩ : DyadicInterval 40),(⟨-198386572992,-198386572928⟩ : DyadicInterval 40),(⟨747071105373,747071124702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81033444,92670914⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81030400,81030464⟩ : DyadicInterval 40),(⟨-81036480,-81036416⟩ : DyadicInterval 40),(⟨762123380619,762123399949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92667008,92667072⟩ : DyadicInterval 40),(⟨-92674880,-92674816⟩ : DyadicInterval 40),(⟨762123379677,762123399006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7872,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123406816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181472782789,181598044519⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167964416192,167964416256⟩ : DyadicInterval 40),(⟨-198331755648,-198331755584⟩ : DyadicInterval 40),(⟨747078730109,747078749438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168071927232,168071927296⟩ : DyadicInterval 40),(⟨-198481788672,-198481788608⟩ : DyadicInterval 40),(⟨747057857671,747057877001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30409861376,-30367339392⟩ : DyadicInterval 40),(⟨777307053312,777328333568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168042337728,168140134336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198576990656,-198440492608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2684_ok : ecellOkT e2684 = true := by decide +kernel
theorem e2684_pos {a z : ℝ} (ha1 : ((676377/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1353603/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2684 e2684_ok ha1 ha2 hz1 hz2 hz

-- box ['1353603/8192000', '338613/2048000', '999/1000', '7993/8000']  interval_lower 280586585/1099511627776
noncomputable def e2685 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147049,0,true,168140134272,168140134336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108503,0,false,-198576990656,-198576990592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097902,0,true,168237922112,168237922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157650,0,false,-198713505600,-198713505536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281007469529,0,true,167984208256,167984208320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918015786023,0,false,-198359373120,-198359373056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281144030366,0,true,168101414656,168101414720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917879225186,0,false,-198522944832,-198522944768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592714136,0,true,81083328,81083392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430541416,0,false,-81089408,-81089344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604359173,0,true,92727424,92727488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418896379,0,false,-92735360,-92735296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619955,0,false,-7872,-7808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621797,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281098304439,0,true,168062170752,168062170816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917924951113,0,false,-198468171904,-198468171840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281223573297,0,true,168169678336,168169678400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917799682255,0,false,-198618232064,-198618232000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069480811992,0,false,-30448553664,-30448553600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069522203101,0,false,-30406001088,-30406001024⟩
    { al := (1353603/8192000), au := (338613/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨181677519273,181791470126⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167984208256,167984208320⟩ : DyadicInterval 40),(⟨-198359373120,-198359373056⟩ : DyadicInterval 40),(⟨747074888896,747074908225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168101414656,168101414720⟩ : DyadicInterval 40),(⟨-198522944832,-198522944768⟩ : DyadicInterval 40),(⟨747052129978,747052149307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81086360,92731397⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81083328,81083392⟩ : DyadicInterval 40),(⟨-81089408,-81089344⟩ : DyadicInterval 40),(⟨762123380611,762123399941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92727424,92727488⟩ : DyadicInterval 40),(⟨-92735360,-92735296⟩ : DyadicInterval 40),(⟨762123379698,762123399028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7872,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123406816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181586676663,181711945521⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168062170752,168062170816⟩ : DyadicInterval 40),(⟨-198468171904,-198468171840⟩ : DyadicInterval 40),(⟨747059752499,747059771828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168169678336,168169678400⟩ : DyadicInterval 40),(⟨-198618232064,-198618232000⟩ : DyadicInterval 40),(⟨747038865534,747038884863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30448553664,-30406001024⟩ : DyadicInterval 40),(⟨777326384128,777347679712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168140134272,168237922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198713505600,-198576990592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2685_ok : ecellOkT e2685 = true := by decide +kernel
theorem e2685_pos {a z : ℝ} (ha1 : ((1353603/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((338613/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2685 e2685_ok ha1 ha2 hz1 hz2 hz

-- box ['676377/4096000', '1353603/8192000', '7993/8000', '3997/4000']  interval_lower 69763505/274877906944
noncomputable def e2686 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196198,0,true,168042337728,168042337792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059354,0,false,-198440492672,-198440492608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147050,0,true,168140134272,168140134336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108502,0,false,-198576990656,-198576990592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280916328075,0,true,167905977152,167905977216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918106927477,0,false,-198250217984,-198250217920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281052888911,0,true,168023191872,168023191936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917970366641,0,false,-198413773440,-198413773376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581085153,0,true,69455168,69455232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442170399,0,false,-69459584,-69459520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592715064,0,true,81084288,81084352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430540488,0,false,-81090304,-81090240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621795,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623389,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280995758078,0,true,167974156096,167974156160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918027497474,0,false,-198345346368,-198345346304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281121026962,0,true,168081672320,168081672384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917902228590,0,false,-198495389760,-198495389696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069514697284,0,false,-30413717440,-30413717376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069556065034,0,false,-30371190208,-30371190144⟩
    { al := (676377/4096000), au := (1353603/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨181563568422,181677519274⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167905977152,167905977216⟩ : DyadicInterval 40),(⟨-198250217984,-198250217920⟩ : DyadicInterval 40),(⟨747090068589,747090087918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168023191872,168023191936⟩ : DyadicInterval 40),(⟨-198413773440,-198413773376⟩ : DyadicInterval 40),(⟨747067321312,747067340642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69457377,81087288⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69455168,69455232⟩ : DyadicInterval 40),(⟨-69459584,-69459520⟩ : DyadicInterval 40),(⟨762123381372,762123400701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81084288,81084352⟩ : DyadicInterval 40),(⟨-81090304,-81090240⟩ : DyadicInterval 40),(⟨762123380579,762123399909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181484130302,181609399186⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167974156096,167974156160⟩ : DyadicInterval 40),(⟨-198345346368,-198345346304⟩ : DyadicInterval 40),(⟨747076839873,747076859202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168081672320,168081672384⟩ : DyadicInterval 40),(⟨-198495389760,-198495389696⟩ : DyadicInterval 40),(⟨747055964893,747055984223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30413717440,-30371190144⟩ : DyadicInterval 40),(⟨777308978688,777330261600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168042337728,168140134336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198576990656,-198440492608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2686_ok : ecellOkT e2686 = true := by decide +kernel
theorem e2686_pos {a z : ℝ} (ha1 : ((676377/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1353603/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2686 e2686_ok ha1 ha2 hz1 hz2 hz

-- box ['1353603/8192000', '338613/2048000', '7993/8000', '3997/4000']  interval_lower 280395165/1099511627776
noncomputable def e2687 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147049,0,true,168140134272,168140134336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108503,0,false,-198576990656,-198576990592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097902,0,true,168237922112,168237922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157650,0,false,-198713505600,-198713505536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281030179219,0,true,168003700224,168003700288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917993076333,0,false,-198386572928,-198386572864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281166754300,0,true,168120916736,168120916800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917856501252,0,false,-198550165760,-198550165696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581130510,0,true,69500480,69500544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442125042,0,false,-69504960,-69504896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592767987,0,true,81137216,81137280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430487565,0,false,-81143232,-81143168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621788,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623383,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281109659075,0,true,168071915904,168071915968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917913596477,0,false,-198481772800,-198481772736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281234935080,0,true,168179428672,168179428736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917788320472,0,false,-198631843392,-198631843328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069477056441,0,false,-30452414656,-30452414592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069518452499,0,false,-30409856896,-30409856832⟩
    { al := (1353603/8192000), au := (338613/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨181677519273,181791470126⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168003700224,168003700288⟩ : DyadicInterval 40),(⟨-198386572928,-198386572864⟩ : DyadicInterval 40),(⟨747071105346,747071124676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168120916736,168120916800⟩ : DyadicInterval 40),(⟨-198550165760,-198550165696⟩ : DyadicInterval 40),(⟨747048341178,747048360508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69502734,81140211⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69500480,69500544⟩ : DyadicInterval 40),(⟨-69504960,-69504896⟩ : DyadicInterval 40),(⟨762123381398,762123400727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81137216,81137280⟩ : DyadicInterval 40),(⟨-81143232,-81143168⟩ : DyadicInterval 40),(⟨762123380571,762123399901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181598031299,181723307304⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168071915904,168071915968⟩ : DyadicInterval 40),(⟨-198481772800,-198481772736⟩ : DyadicInterval 40),(⟨747057859849,747057879179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168179428672,168179428736⟩ : DyadicInterval 40),(⟨-198631843392,-198631843328⟩ : DyadicInterval 40),(⟨747036970366,747036989696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30452414656,-30409856832⟩ : DyadicInterval 40),(⟨777328312032,777349610208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168140134272,168237922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198713505600,-198576990592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2687_ok : ecellOkT e2687 = true := by decide +kernel
theorem e2687_pos {a z : ℝ} (ha1 : ((1353603/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((338613/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2687 e2687_ok ha1 ha2 hz1 hz2 hz

-- box ['84441/512000', '270381/1638400', '3997/4000', '1599/1600']  interval_lower 276191105/1099511627776
noncomputable def e2688 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294496,0,true,167846718592,167846718656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961056,0,false,-198167547520,-198167547456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245348,0,true,167944532544,167944532608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010204,0,false,-198304011584,-198304011520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280711292745,0,true,167729965056,167729965120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918311962807,0,false,-198004698048,-198004697984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847839338,0,true,167847186304,167847186368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918175416214,0,false,-198168199936,-198168199872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569433437,0,true,57804096,57804160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453822115,0,false,-57807232,-57807168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581040664,0,true,69410688,69410752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442214888,0,false,-69415104,-69415040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623393,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624737,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280779289384,0,true,167788339712,167788339776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918243966168,0,false,-198086114688,-198086114624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280904551171,0,true,167895868096,167895868160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918118704381,0,false,-198236114240,-198236114176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069586166483,0,false,-30340246144,-30340246080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069627482566,0,false,-30297774912,-30297774848⟩
    { al := (84441/512000), au := (270381/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨181335666720,181449617572⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561058,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588522,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167729965056,167729965120⟩ : DyadicInterval 40),(⟨-198004698048,-198004697984⟩ : DyadicInterval 40),(⟨747124189074,747124208404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167847186304,167847186368⟩ : DyadicInterval 40),(⟨-198168199936,-198168199872⟩ : DyadicInterval 40),(⟨747101470356,747101489685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57805661,69412888⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57804096,57804160⟩ : DyadicInterval 40),(⟨-57807232,-57807168⟩ : DyadicInterval 40),(⟨762123382080,762123401410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69410688,69410752⟩ : DyadicInterval 40),(⟨-69415104,-69415040⟩ : DyadicInterval 40),(⟨762123381377,762123400707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181267661608,181392923395⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167788339712,167788339776⟩ : DyadicInterval 40),(⟨-198086114688,-198086114624⟩ : DyadicInterval 40),(⟨747112877943,747112897273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167895868096,167895868160⟩ : DyadicInterval 40),(⟨-198236114240,-198236114176⟩ : DyadicInterval 40),(⟨747092029464,747092048794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30340246144,-30297774848⟩ : DyadicInterval 40),(⟨777272271040,777293525952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167846718592,167944532608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198304011584,-198167547456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2688_ok : ecellOkT e2688 = true := by decide +kernel
theorem e2688_pos {a z : ℝ} (ha1 : ((84441/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((270381/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2688 e2688_ok ha1 ha2 hz1 hz2 hz

-- box ['270381/1638400', '676377/4096000', '3997/4000', '1599/1600']  interval_lower 277525799/1099511627776
noncomputable def e2689 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245347,0,true,167944532544,167944532608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010205,0,false,-198304011584,-198304011520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196199,0,true,168042337728,168042337792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059353,0,false,-198440492672,-198440492608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280825158133,0,true,167827716032,167827716096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918198097419,0,false,-198141039616,-198141039552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961718969,0,true,167944939072,167944939136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918061536583,0,false,-198304578816,-198304578752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569471230,0,true,57841920,57841984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453784322,0,false,-57844992,-57844928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581086020,0,true,69456000,69456064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442169532,0,false,-69460480,-69460416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623388,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624733,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280893197507,0,true,167886122176,167886122240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918130058045,0,false,-198222517504,-198222517440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281018466408,0,true,167993647040,167993647104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918004789144,0,false,-198372544192,-198372544128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069548568143,0,false,-30378897152,-30378897088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069589912529,0,false,-30336395328,-30336395264⟩
    { al := (270381/1638400), au := (676377/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨181449617571,181563568423⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588523,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167827716032,167827716096⟩ : DyadicInterval 40),(⟨-198141039616,-198141039552⟩ : DyadicInterval 40),(⟨747105245273,747105264602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944939072,167944939136⟩ : DyadicInterval 40),(⟨-198304578816,-198304578752⟩ : DyadicInterval 40),(⟨747082509644,747082528973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57843454,69458244⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57841920,57841984⟩ : DyadicInterval 40),(⟨-57844992,-57844928⟩ : DyadicInterval 40),(⟨762123382044,762123401374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69456000,69456064⟩ : DyadicInterval 40),(⟨-69460480,-69460416⟩ : DyadicInterval 40),(⟨762123381404,762123400733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181381569731,181506838632⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167886122176,167886122240⟩ : DyadicInterval 40),(⟨-198222517504,-198222517440⟩ : DyadicInterval 40),(⟨747093919781,747093939111⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167993647040,167993647104⟩ : DyadicInterval 40),(⟨-198372544192,-198372544128⟩ : DyadicInterval 40),(⟨747073056816,747073076145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30378897152,-30336395264⟩ : DyadicInterval 40),(⟨777291581248,777312851456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167944532544,168042337792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198440492672,-198304011520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2689_ok : ecellOkT e2689 = true := by decide +kernel
theorem e2689_pos {a z : ℝ} (ha1 : ((270381/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((676377/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2689 e2689_ok ha1 ha2 hz1 hz2 hz

-- box ['84441/512000', '270381/1638400', '1599/1600', '1999/2000']  interval_lower 138000453/549755813888
noncomputable def e2690 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294496,0,true,167846718592,167846718656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961056,0,false,-198167547520,-198167547456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245348,0,true,167944532544,167944532608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010204,0,false,-198304011584,-198304011520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733959704,0,true,167749424832,167749424896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918289295848,0,false,-198031837952,-198031837888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280870520540,0,true,167866656256,167866656320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918152735012,0,false,-198195360960,-198195360896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557872370,0,true,46243584,46243648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465383182,0,false,-46245568,-46245504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569472039,0,true,57842688,57842752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453783513,0,false,-57845824,-57845760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624732,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625831,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280790622709,0,true,167798068992,167798069056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918232632843,0,false,-198099685376,-198099685312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280915891645,0,true,167905602560,167905602624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918107363907,0,false,-198249695360,-198249695296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069582424556,0,false,-30344092800,-30344092736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069623745581,0,false,-30301616320,-30301616256⟩
    { al := (84441/512000), au := (270381/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨181335666720,181449617572⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561058,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588522,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167749424832,167749424896⟩ : DyadicInterval 40),(⟨-198031837952,-198031837888⟩ : DyadicInterval 40),(⟨747120418943,747120438273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167866656256,167866656320⟩ : DyadicInterval 40),(⟨-198195360960,-198195360896⟩ : DyadicInterval 40),(⟨747097694958,747097714287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46244594,57844263⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46243584,46243648⟩ : DyadicInterval 40),(⟨-46245568,-46245504⟩ : DyadicInterval 40),(⟨762123382598,762123401928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57842688,57842752⟩ : DyadicInterval 40),(⟨-57845824,-57845760⟩ : DyadicInterval 40),(⟨762123382076,762123401405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181278994933,181404263869⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167798068992,167798069056⟩ : DyadicInterval 40),(⟨-198099685376,-198099685312⟩ : DyadicInterval 40),(⟨747110992244,747111011574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167905602560,167905602624⟩ : DyadicInterval 40),(⟨-198249695360,-198249695296⟩ : DyadicInterval 40),(⟨747090141256,747090160586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30344092800,-30301616256⟩ : DyadicInterval 40),(⟨777274191744,777295449280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167846718592,167944532608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198304011584,-198167547456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2690_ok : ecellOkT e2690 = true := by decide +kernel
theorem e2690_pos {a z : ℝ} (ha1 : ((84441/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((270381/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2690 e2690_ok ha1 ha2 hz1 hz2 hz

-- box ['270381/1638400', '676377/4096000', '1599/1600', '1999/2000']  interval_lower 138667403/549755813888
noncomputable def e2691 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245347,0,true,167944532544,167944532608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010205,0,false,-198304011584,-198304011520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196199,0,true,168042337728,168042337792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059353,0,false,-198440492672,-198440492608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847839335,0,true,167847186304,167847186368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918175416217,0,false,-198168199936,-198168199872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280984414415,0,true,167964419456,167964419520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918038841137,0,false,-198331760256,-198331760192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557902605,0,true,46273792,46273856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465352947,0,false,-46275840,-46275776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569509836,0,true,57880512,57880576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453745716,0,false,-57883584,-57883520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624728,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625829,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280904537953,0,true,167895856704,167895856768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918118717599,0,false,-198236098432,-198236098368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281029814001,0,true,168003386752,168003386816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917993441551,0,false,-198386135552,-198386135488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069544821515,0,false,-30382748736,-30382748672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069586170845,0,false,-30340241664,-30340241600⟩
    { al := (270381/1638400), au := (676377/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨181449617571,181563568423⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588523,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167847186304,167847186368⟩ : DyadicInterval 40),(⟨-198168199936,-198168199872⟩ : DyadicInterval 40),(⟨747101470356,747101489686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167964419456,167964419520⟩ : DyadicInterval 40),(⟨-198331760256,-198331760192⟩ : DyadicInterval 40),(⟨747078729490,747078748819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46274829,57882060⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46273792,46273856⟩ : DyadicInterval 40),(⟨-46275840,-46275776⟩ : DyadicInterval 40),(⟨762123382628,762123401957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57880512,57880576⟩ : DyadicInterval 40),(⟨-57883584,-57883520⟩ : DyadicInterval 40),(⟨762123382040,762123401369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181392910177,181518186225⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167895856704,167895856768⟩ : DyadicInterval 40),(⟨-198236098432,-198236098368⟩ : DyadicInterval 40),(⟨747092031701,747092051030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168003386752,168003386816⟩ : DyadicInterval 40),(⟨-198386135552,-198386135488⟩ : DyadicInterval 40),(⟨747071166224,747071185553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30382748736,-30340241600⟩ : DyadicInterval 40),(⟨777293504416,777314777248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167944532544,168042337792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198440492672,-198304011520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2691_ok : ecellOkT e2691 = true := by decide +kernel
theorem e2691_pos {a z : ℝ} (ha1 : ((270381/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((676377/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2691 e2691_ok ha1 ha2 hz1 hz2 hz

-- box ['676377/4096000', '1353603/8192000', '3997/4000', '1599/1600']  interval_lower 17428945/68719476736
noncomputable def e2692 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196198,0,true,168042337728,168042337792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059354,0,false,-198440492672,-198440492608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147050,0,true,168140134272,168140134336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108502,0,false,-198576990656,-198576990592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280939023521,0,true,167925458304,167925458368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918084232031,0,false,-198277398080,-198277398016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075598601,0,true,168042683136,168042683200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917947656951,0,false,-198440974656,-198440974592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569509026,0,true,57879680,57879744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453746526,0,false,-57882816,-57882752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581131379,0,true,69501376,69501440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442124173,0,false,-69505856,-69505792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623382,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624729,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281007105619,0,true,167983895936,167983896000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918016149933,0,false,-198358937280,-198358937216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281132381650,0,true,168091417344,168091417408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917890873902,0,false,-198508991104,-198508991040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069510946196,0,false,-30417573696,-30417573632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069552318893,0,false,-30375041280,-30375041216⟩
    { al := (676377/4096000), au := (1353603/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨181563568422,181677519274⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167925458304,167925458368⟩ : DyadicInterval 40),(⟨-198277398080,-198277398016⟩ : DyadicInterval 40),(⟨747086289352,747086308682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042683136,168042683200⟩ : DyadicInterval 40),(⟨-198440974656,-198440974592⟩ : DyadicInterval 40),(⟨747063536832,747063556162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57881250,69503603⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57879680,57879744⟩ : DyadicInterval 40),(⟨-57882816,-57882752⟩ : DyadicInterval 40),(⟨762123382072,762123401402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69501376,69501440⟩ : DyadicInterval 40),(⟨-69505856,-69505792⟩ : DyadicInterval 40),(⟨762123381398,762123400727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181495477843,181620753874⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167983895936,167983896000⟩ : DyadicInterval 40),(⟨-198358937280,-198358937216⟩ : DyadicInterval 40),(⟨747074949510,747074968839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168091417344,168091417408⟩ : DyadicInterval 40),(⟨-198508991104,-198508991040⟩ : DyadicInterval 40),(⟨747054072015,747054091344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30417573696,-30375041216⟩ : DyadicInterval 40),(⟨777310904224,777332189728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168042337728,168140134336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198576990656,-198440492608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2692_ok : ecellOkT e2692 = true := by decide +kernel
theorem e2692_pos {a z : ℝ} (ha1 : ((676377/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1353603/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2692 e2692_ok ha1 ha2 hz1 hz2 hz

-- box ['1353603/8192000', '338613/2048000', '3997/4000', '1599/1600']  interval_lower 35025437/137438953472
noncomputable def e2693 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147049,0,true,168140134272,168140134336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108503,0,false,-198576990656,-198576990592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097902,0,true,168237922112,168237922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157650,0,false,-198713505600,-198713505536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281052888909,0,true,168023191872,168023191936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917970366643,0,false,-198413773440,-198413773376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189478234,0,true,168140418496,168140418560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917833777318,0,false,-198577387392,-198577387328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569546824,0,true,57917504,57917568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453708728,0,false,-57920576,-57920512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581176741,0,true,69546752,69546816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442078811,0,false,-69551168,-69551104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623376,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624725,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281121013739,0,true,168081660992,168081661056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917902241813,0,false,-198495373952,-198495373888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281246296891,0,true,168189178944,168189179008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917776958661,0,false,-198645454912,-198645454848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069473300646,0,false,-30456275968,-30456275904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069514701653,0,false,-30413712896,-30413712832⟩
    { al := (1353603/8192000), au := (338613/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨181677519273,181791470126⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168023191872,168023191936⟩ : DyadicInterval 40),(⟨-198413773440,-198413773376⟩ : DyadicInterval 40),(⟨747067321313,747067340642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140418496,168140418560⟩ : DyadicInterval 40),(⟨-198577387392,-198577387328⟩ : DyadicInterval 40),(⟨747044551893,747044571223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57919048,69548965⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57917504,57917568⟩ : DyadicInterval 40),(⟨-57920576,-57920512⟩ : DyadicInterval 40),(⟨762123382036,762123401366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69546752,69546816⟩ : DyadicInterval 40),(⟨-69551168,-69551104⟩ : DyadicInterval 40),(⟨762123381360,762123400689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181609385963,181734669115⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168081660992,168081661056⟩ : DyadicInterval 40),(⟨-198495373952,-198495373888⟩ : DyadicInterval 40),(⟨747055967099,747055986428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168189178944,168189179008⟩ : DyadicInterval 40),(⟨-198645454912,-198645454848⟩ : DyadicInterval 40),(⟨747035075069,747035094399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30456275968,-30413712832⟩ : DyadicInterval 40),(⟨777330240032,777351540864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168140134272,168237922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198713505600,-198576990592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2693_ok : ecellOkT e2693 = true := by decide +kernel
theorem e2693_pos {a z : ℝ} (ha1 : ((1353603/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((338613/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2693 e2693_ok ha1 ha2 hz1 hz2 hz

-- box ['676377/4096000', '1353603/8192000', '1599/1600', '1999/2000']  interval_lower 278671911/1099511627776
noncomputable def e2694 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196198,0,true,168042337728,168042337792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059354,0,false,-198440492672,-198440492608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147050,0,true,168140134272,168140134336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108502,0,false,-198576990656,-198576990592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961718967,0,true,167944939072,167944939136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918061536585,0,false,-198304578816,-198304578752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281098308291,0,true,168062174080,168062174144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917924947261,0,false,-198468176512,-198468176448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557932843,0,true,46304064,46304128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465322709,0,false,-46306048,-46305984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569547634,0,true,57918272,57918336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453707918,0,false,-57921408,-57921344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624724,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625826,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281018453188,0,true,167993635712,167993635776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918004802364,0,false,-198372528384,-198372528320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281143736369,0,true,168101162304,168101162368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917879519183,0,false,-198522592640,-198522592576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069507194863,0,false,-30421430272,-30421430208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069548572508,0,false,-30378892608,-30378892544⟩
    { al := (676377/4096000), au := (1353603/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨181563568422,181677519274⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944939072,167944939136⟩ : DyadicInterval 40),(⟨-198304578816,-198304578752⟩ : DyadicInterval 40),(⟨747082509644,747082528973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168062174080,168062174144⟩ : DyadicInterval 40),(⟨-198468176512,-198468176448⟩ : DyadicInterval 40),(⟨747059751841,747059771171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46305067,57919858⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46304064,46304128⟩ : DyadicInterval 40),(⟨-46306048,-46305984⟩ : DyadicInterval 40),(⟨762123382593,762123401922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57918272,57918336⟩ : DyadicInterval 40),(⟨-57921408,-57921344⟩ : DyadicInterval 40),(⟨762123382068,762123401397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181506825412,181632108593⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167993635712,167993635776⟩ : DyadicInterval 40),(⟨-198372528384,-198372528320⟩ : DyadicInterval 40),(⟨747073059018,747073078348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168101162304,168101162368⟩ : DyadicInterval 40),(⟨-198522592640,-198522592576⟩ : DyadicInterval 40),(⟨747052179006,747052198336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30421430272,-30378892544⟩ : DyadicInterval 40),(⟨777312829888,777334118016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168042337728,168140134336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198576990656,-198440492608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2694_ok : ecellOkT e2694 = true := by decide +kernel
theorem e2694_pos {a z : ℝ} (ha1 : ((676377/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1353603/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2694 e2694_ok ha1 ha2 hz1 hz2 hz

-- box ['1353603/8192000', '338613/2048000', '1599/1600', '1999/2000']  interval_lower 8750375/34359738368
noncomputable def e2695 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147049,0,true,168140134272,168140134336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108503,0,false,-198576990656,-198576990592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097902,0,true,168237922112,168237922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157650,0,false,-198713505600,-198713505536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075598599,0,true,168042683136,168042683200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917947656953,0,false,-198440974656,-198440974592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281212202168,0,true,168159919936,168159920000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917811053384,0,false,-198604609664,-198604609600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557963080,0,true,46334272,46334336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465292472,0,false,-46336320,-46336256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569585437,0,true,57956096,57956160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453670115,0,false,-57959232,-57959168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624720,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625824,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281132368426,0,true,168091406016,168091406080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917890887126,0,false,-198508975296,-198508975232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281257658734,0,true,168198929216,168198929280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917765596818,0,false,-198659066688,-198659066624⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069469544605,0,false,-30460137472,-30460137408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069510950566,0,false,-30417569216,-30417569152⟩
    { al := (1353603/8192000), au := (338613/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨181677519273,181791470126⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042683136,168042683200⟩ : DyadicInterval 40),(⟨-198440974656,-198440974592⟩ : DyadicInterval 40),(⟨747063536833,747063556162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168159919936,168159920000⟩ : DyadicInterval 40),(⟨-198604609664,-198604609600⟩ : DyadicInterval 40),(⟨747040762096,747040781425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46335304,57957661⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46334272,46334336⟩ : DyadicInterval 40),(⟨-46336320,-46336256⟩ : DyadicInterval 40),(⟨762123382623,762123401952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57956096,57956160⟩ : DyadicInterval 40),(⟨-57959232,-57959168⟩ : DyadicInterval 40),(⟨762123382064,762123401394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181620740650,181746030958⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168091406016,168091406080⟩ : DyadicInterval 40),(⟨-198508975296,-198508975232⟩ : DyadicInterval 40),(⟨747054074220,747054093550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168198929216,168198929280⟩ : DyadicInterval 40),(⟨-198659066688,-198659066624⟩ : DyadicInterval 40),(⟨747033179633,747033198963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30460137472,-30417569152⟩ : DyadicInterval 40),(⟨777332168192,777353471616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168140134272,168237922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198713505600,-198576990592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2695_ok : ecellOkT e2695 = true := by decide +kernel
theorem e2695_pos {a z : ℝ} (ha1 : ((1353603/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((338613/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2695 e2695_ok ha1 ha2 hz1 hz2 hz

-- box ['338613/2048000', '1355301/8192000', '999/1000', '7993/8000']  interval_lower 35241385/137438953472
noncomputable def e2696 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097901,0,true,168237922112,168237922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157651,0,false,-198713505600,-198713505536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048753,0,true,168335701248,168335701312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206799,0,false,-198850037440,-198850037376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281121306430,0,true,168081912192,168081912256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917901949122,0,false,-198495724544,-198495724480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281257881510,0,true,168199120384,168199120448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917765374042,0,false,-198659333568,-198659333504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592767058,0,true,81136256,81136320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430488494,0,false,-81142336,-81142272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604419659,0,true,92787904,92787968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418835893,0,false,-92795840,-92795776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619944,0,false,-7872,-7808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621789,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281212198316,0,true,168159916608,168159916672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917811057236,0,false,-198604605056,-198604604992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281337474301,0,true,168267420800,168267420864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917685781251,0,false,-198754692352,-198754692288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069443152255,0,false,-30487271552,-30487271488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069484571672,0,false,-30444688384,-30444688320⟩
    { al := (338613/2048000), au := (1355301/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨181791470125,181905420977⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168081912192,168081912256⟩ : DyadicInterval 40),(⟨-198495724544,-198495724480⟩ : DyadicInterval 40),(⟨747055918303,747055937632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168199120384,168199120448⟩ : DyadicInterval 40),(⟨-198659333568,-198659333504⟩ : DyadicInterval 40),(⟨747033142467,747033161797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81139282,92791883⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81136256,81136320⟩ : DyadicInterval 40),(⟨-81142336,-81142272⟩ : DyadicInterval 40),(⟨762123380604,762123399933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92787904,92787968⟩ : DyadicInterval 40),(⟨-92795840,-92795776⟩ : DyadicInterval 40),(⟨762123379688,762123399018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7872,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123406816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181700570540,181825846525⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168159916608,168159916672⟩ : DyadicInterval 40),(⟨-198604605056,-198604604992⟩ : DyadicInterval 40),(⟨747040762754,747040782083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168267420800,168267420864⟩ : DyadicInterval 40),(⟨-198754692352,-198754692288⟩ : DyadicInterval 40),(⟨747019861220,747019880550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30487271552,-30444688320⟩ : DyadicInterval 40),(⟨777345727776,777367038656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168237922112,168335701312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198850037440,-198713505536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2696_ok : ecellOkT e2696 = true := by decide +kernel
theorem e2696_pos {a z : ℝ} (ha1 : ((338613/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1355301/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2696 e2696_ok ha1 ha2 hz1 hz2 hz

-- box ['1355301/8192000', '27123/163840', '999/1000', '7993/8000']  interval_lower 283278721/1099511627776
noncomputable def e2697 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048752,0,true,168335701248,168335701312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206800,0,false,-198850037440,-198850037376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999604,0,true,168433471744,168433471808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255948,0,false,-198986586304,-198986586240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281235143330,0,true,168179607424,168179607488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917788112222,0,false,-198632092864,-198632092800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281371732654,0,true,168296817408,168296817472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917651522898,0,false,-198795739264,-198795739200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592819983,0,true,81189184,81189248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430435569,0,false,-81195264,-81195200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604480150,0,true,92848448,92848512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418775402,0,false,-92856320,-92856256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619934,0,false,-7872,-7808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621781,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281326092194,0,true,168257653824,168257653888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917697163358,0,false,-198741055168,-198741055104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281451375302,0,true,168365154560,168365154624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917571880250,0,false,-198891169664,-198891169600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069405468920,0,false,-30526015040,-30526014976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069446916648,0,false,-30483401344,-30483401280⟩
    { al := (1355301/8192000), au := (27123/163840), zl := (999/1000), zu := (7993/8000),
      A := ⟨181905420976,182019371828⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471744,168433471808⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543875,746987563205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168179607424,168179607488⟩ : DyadicInterval 40),(⟨-198632092864,-198632092800⟩ : DyadicInterval 40),(⟨747036935601,747036954931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168296817408,168296817472⟩ : DyadicInterval 40),(⟨-198795739264,-198795739200⟩ : DyadicInterval 40),(⟨747014142866,747014162195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81192207,92852374⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81189184,81189248⟩ : DyadicInterval 40),(⟨-81195264,-81195200⟩ : DyadicInterval 40),(⟨762123380596,762123399925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92848448,92848512⟩ : DyadicInterval 40),(⟨-92856320,-92856256⟩ : DyadicInterval 40),(⟨762123379646,762123398976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7872,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123406816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181814464418,181939747526⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168257653824,168257653888⟩ : DyadicInterval 40),(⟨-198741055168,-198741055104⟩ : DyadicInterval 40),(⟨747021760864,747021780194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168365154560,168365154624⟩ : DyadicInterval 40),(⟨-198891169664,-198891169600⟩ : DyadicInterval 40),(⟨747000844821,747000864151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30526015040,-30483401280⟩ : DyadicInterval 40),(⟨777365084256,777386410400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168335701248,168433471808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198986586304,-198850037376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2697_ok : ecellOkT e2697 = true := by decide +kernel
theorem e2697_pos {a z : ℝ} (ha1 : ((1355301/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((27123/163840 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2697 e2697_ok ha1 ha2 hz1 hz2 hz

-- box ['338613/2048000', '1355301/8192000', '7993/8000', '3997/4000']  interval_lower 140869677/549755813888
noncomputable def e2698 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097901,0,true,168237922112,168237922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157651,0,false,-198713505600,-198713505536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048753,0,true,168335701248,168335701312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206799,0,false,-198850037440,-198850037376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281144030364,0,true,168101414656,168101414720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917879225188,0,false,-198522944832,-198522944768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281280619688,0,true,168218632960,168218633024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917742635864,0,false,-198686574976,-198686574912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581175872,0,true,69545856,69545920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442079680,0,false,-69550336,-69550272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592820912,0,true,81190080,81190144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430434640,0,false,-81196160,-81196096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621780,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623377,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281223560071,0,true,168169667008,168169667072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917799695481,0,false,-198618216192,-198618216128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281348843205,0,true,168277176384,168277176448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917674412347,0,false,-198768313920,-198768313856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069439391994,0,false,-30491137536,-30491137472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069480816365,0,false,-30448549184,-30448549120⟩
    { al := (338613/2048000), au := (1355301/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨181791470125,181905420977⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168101414656,168101414720⟩ : DyadicInterval 40),(⟨-198522944832,-198522944768⟩ : DyadicInterval 40),(⟨747052129978,747052149308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168218632960,168218633024⟩ : DyadicInterval 40),(⟨-198686574976,-198686574912⟩ : DyadicInterval 40),(⟨747029348884,747029368214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69548096,81193136⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69545856,69545920⟩ : DyadicInterval 40),(⟨-69550336,-69550272⟩ : DyadicInterval 40),(⟨762123381392,762123400721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81190080,81190144⟩ : DyadicInterval 40),(⟨-81196160,-81196096⟩ : DyadicInterval 40),(⟨762123380596,762123399925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181711932295,181837215429⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168169667008,168169667072⟩ : DyadicInterval 40),(⟨-198618216192,-198618216128⟩ : DyadicInterval 40),(⟨747038867715,747038887045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168277176384,168277176448⟩ : DyadicInterval 40),(⟨-198768313920,-198768313856⟩ : DyadicInterval 40),(⟨747017963659,747017982989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30491137536,-30448549120⟩ : DyadicInterval 40),(⟨777347658176,777368971648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168237922112,168335701312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198850037440,-198713505536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2698_ok : ecellOkT e2698 = true := by decide +kernel
theorem e2698_pos {a z : ℝ} (ha1 : ((338613/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1355301/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2698 e2698_ok ha1 ha2 hz1 hz2 hz

-- box ['1355301/8192000', '27123/163840', '7993/8000', '3997/4000']  interval_lower 283086549/1099511627776
noncomputable def e2699 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048752,0,true,168335701248,168335701312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206800,0,false,-198850037440,-198850037376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999604,0,true,168433471744,168433471808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255948,0,false,-198986586304,-198986586240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281257881508,0,true,168199120384,168199120448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917765374044,0,false,-198659333568,-198659333504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281394485076,0,true,168316340480,168316340544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917628770476,0,false,-198823001088,-198823001024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581221236,0,true,69591232,69591296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442034316,0,false,-69595712,-69595648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592873843,0,true,81243008,81243072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430381709,0,false,-81249088,-81249024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621772,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623372,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281337461072,0,true,168267409472,168267409536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917685794480,0,false,-198754676544,-198754676480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281462751328,0,true,168374915392,168374915456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917560504224,0,false,-198904801472,-198904801408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069401703946,0,false,-30529886016,-30529885952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069443156631,0,false,-30487267072,-30487267008⟩
    { al := (1355301/8192000), au := (27123/163840), zl := (7993/8000), zu := (3997/4000),
      A := ⟨181905420976,182019371828⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471744,168433471808⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543875,746987563205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168199120384,168199120448⟩ : DyadicInterval 40),(⟨-198659333568,-198659333504⟩ : DyadicInterval 40),(⟨747033142468,747033161797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168316340480,168316340544⟩ : DyadicInterval 40),(⟨-198823001088,-198823001024⟩ : DyadicInterval 40),(⟨747010344467,747010363797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69593460,81246067⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69591232,69591296⟩ : DyadicInterval 40),(⟨-69595712,-69595648⟩ : DyadicInterval 40),(⟨762123381386,762123400716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81243008,81243072⟩ : DyadicInterval 40),(⟨-81249088,-81249024⟩ : DyadicInterval 40),(⟨762123380588,762123399917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181825833296,181951123552⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168267409472,168267409536⟩ : DyadicInterval 40),(⟨-198754676544,-198754676480⟩ : DyadicInterval 40),(⟨747019863432,747019882762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168374915392,168374915456⟩ : DyadicInterval 40),(⟨-198904801472,-198904801408⟩ : DyadicInterval 40),(⟨746998944863,746998964193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30529886016,-30487267008⟩ : DyadicInterval 40),(⟨777367017120,777388345888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168335701248,168433471808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198986586304,-198850037376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2699_ok : ecellOkT e2699 = true := by decide +kernel
theorem e2699_pos {a z : ℝ} (ha1 : ((1355301/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((27123/163840 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2699 e2699_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B044

end


