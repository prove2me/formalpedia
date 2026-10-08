-- Prove2me | Definitions.Def_CK_CKLaneC_RST2_U_0065_q02
-- name    : CK_CKLaneC_RST2_U_0065_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T17:01:35.515+00:00
-- url     : https://prove2.me/theorems/c5de723b-d1ca-4b3a-afc7-042cb27f842e
-- title:
--   Courtade–Kumar proof module `CKLaneC.RST2.U_0065 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RST2.U_0065 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RST2.U_0065 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RST2.U_0065 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RST2/U_0065 (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneC_RST2_U_0065_q01

namespace CKLaneC.RST2.U_0065
open CKLaneR2.TM3 CKLaneR2.Cell CKLaneR2.Tail CKLaneC.RSTail
set_option maxHeartbeats 0 in
theorem leaf_2 : TailPosI 1688849860263936 1970324836974592 9223372036854775808 13835058055282163712 288230376151711744 576460752303423488 :=
  (ofR2 (CKLaneR2.Tail.leafS c2 q2 false 1688849860263936 1970324836974592 9223372036854775808 13835058055282163712 288230376151711744 576460752303423488 (by decide +kernel)))
noncomputable def c3 : SCell := { bch := { bexp := true, bc := 2106365851602944, bh := 0, bN := 69, bD := 1024 }, tc := 11529215046068469760, th := 2305843009213693952, sc := 407619307041718272, shN := 361, shD := 1024 }
noncomputable def q3 : TCert := { V0 := [[[1497925856282139791]], [[26166281140259270, 296742506020948485], [(-9840737129738022)]], [[(-4169665653857653), 5084539999517835, (-843268978585022)], [(-188773115669363), (-1912217532659871)], [64359922257218]], [[416552412551640, (-812821572793798), (-43784578084263), (-53079255387930)], [28666698714469, (-34736045499663), 16466708469353], [1334268639476, 12140323379485], [(-419316724031)]], [[(-27048930088105), 81752614152997, 6230036235357, (-2646863492856), 457603483046], [(-2680777665513), 5314390238550, 877862267542, 995444775352], [(-194244599471), 226226308145, (-213371628389)], [(-9272605560), (-75906911395)], [2725656160]]], r0 := 281474976710656, V1 := [[[2379171512024965624]], [[40957834199732570, 0], [(-15403613436790186)]], [[(-6542199524283413), 0, 0], [(-283855477244012), 0], [98555179767110]], [[656872232175070, 0, 0, 0], [43332864809308, 0, 0], [1894253062613, 0], [(-623447386621)]], [[(-43185534914233), 0, 0, 0, 0], [(-4107986227864), 0, 0, 0], [(-277919105733), 0, 0], [(-12205031575), 0], [3904436843]]], r1 := 70368744177664, V2 := [[[18444720695388871686]], [[21558097120182, 31121974261], [135457567522722]], [[(-3516938462144), (-86772258), (-458808)], [(-1487039241575), (-4200313919)], [(-4528137923459)]], [[381043836145, 8254000, (-2347), 6], [241154889268, 12430300, 93021], [51486943356, 283480201], [100738520004]], [[(-30901917032), 118281, 528, 0, 0], [(-25953292684), (-1203644), 465, (-2)], [(-8293142214), (-892678), (-9432)], [(-1194194604), (-12756704)], [(-1677086482)]]], r2 := 68719476736, Vm := [[[18444720804419210988]], [[21558290638936, 0], [135442745180801]], [[(-3516968377143), 0, 0], [(-1487065834712), 0], [(-4527129596088)]], [[381048087010, 0, 0, 0], [241158983690, 0, 0], [51488768839, 0], [100692749297]], [[(-30902545837), 0, 0, 0, 0], [(-25953874117), 0, 0, 0], [(-8293422268), 0, 0], [(-1194278030), 0], [(-1675526628)]]], rm := 17179869184, rhoP := [[[18448408934530618072]], [[9985474154786, (-555002029665040)], [(-112819365578789)]], [[(-2274454445143), (-3329110632362), 16142272126], [(-643704428498), 37613010573016], [3826093066949]], [[277609132005, 758282454995, 206443487, (-463757)], [153034948069, 214650396858, (-2185409003)], [20467161771, (-1275808254391)], [(-86606103637)]], [[(-24833415978), (-92551637703), (-43663319), (-9225), 14], [(-18820927207), (-51029336848), (-27423563), 94115], [(-5141438438), (-6827838095), 147994901], [(-425314858), 28888749235], [1472620369]]], rhoR := 274877906944 }
set_option maxHeartbeats 0 in
theorem leaf_3 : TailPosI 1970324836974592 2251799813685248 9223372036854775808 13835058055282163712 288230376151711744 576460752303423488 :=
  (ofR2 (CKLaneR2.Tail.leafS c3 q3 false 1970324836974592 2251799813685248 9223372036854775808 13835058055282163712 288230376151711744 576460752303423488 (by decide +kernel)))

end CKLaneC.RST2.U_0065


