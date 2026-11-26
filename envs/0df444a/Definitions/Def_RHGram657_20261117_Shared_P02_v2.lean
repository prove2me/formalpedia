-- Prove2me | Definitions.Def_RHGram657_20261117_Shared_P02_v2
-- name    : RHGram657_20261117_Shared_P02_v2
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T17:22:42.649544+00:00
-- url     : https://prove2.me/theorems/235584bd-48f0-410b-a161-0534f637c55b
-- title:
--   Gram 657 ordinary support part 2 of 2
-- statement:
--   Part 2 of a sequential partition of the exact ordinary Gram 657 certificate support. All terms are preserved verbatim; dependencies are proved in the preceding published module.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; Apache-2.0. Ordinary proof export by Desenvolvimento RH. Full expanded split certificate checked by AXLE ca6ded48-f988-40ff-9efe-406723815373. Exact sequential partition checked in AXLE prefixes bfd8e913-036a-4e18-9ae7-65fa01df1212, 826dd42f-9fa6-463b-8aaf-7273935dc269.

import Definitions.Def_RHGram657_20261117_Shared_P01_v2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def Gram657ProofSharing.c250 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram657ProofSharing.c251 := (@Enclosure.Complex.IsNear.mk Gram657ProofSharing.c249 Gram657ProofSharing.c59 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 202323236) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c250 Gram657ProofSharing.c61)

noncomputable def Gram657ProofSharing.c252 := (@Enclosure.Complex.IsNear.of_eq Gram657ProofSharing.c234 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 202323236) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 202323236) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c248 Gram657ProofSharing.c251)

noncomputable def Gram657ProofSharing.c253 := (@Enclosure.Complex.IsNear.re_isNear Gram657ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 202323236) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c252)

noncomputable def Gram657ProofSharing.c254 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 202323236) (nat_lit 400000) })

noncomputable def Gram657ProofSharing.c255 := (@congrArg.{1, 1} Complex Complex Gram657ProofSharing.c47 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 202323236) (nat_lit 400000) } Complex.log Gram657ProofSharing.c57)

noncomputable def Gram657ProofSharing.c256 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram657ProofSharing.c257 := (Enclosure.sfrac Bool.false (nat_lit 40934701825511696) (nat_lit 160000000000))

noncomputable def Gram657ProofSharing.c258 := (Real.log Gram657ProofSharing.c257)

noncomputable def Gram657ProofSharing.c259 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram657ProofSharing.c256 Gram657ProofSharing.c258)

noncomputable def Gram657ProofSharing.c260 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 202323236) (nat_lit 400000) (nat_lit 40934701825511696) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c261 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram657ProofSharing.c262 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40934701825511696))

noncomputable def Gram657ProofSharing.c263 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 160000000000))

noncomputable def Gram657ProofSharing.c264 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram657ProofSharing.c15 Gram657ProofSharing.c262 Gram657ProofSharing.c263)

noncomputable def Gram657ProofSharing.c265 := (Real.log Gram657ProofSharing.c264)

noncomputable def Gram657ProofSharing.c266 := (nat_lit 9396517207089488297353124094004105410102951243985382522439189444006156138834978741528121479693754504888043859162867403251491672869952647799503293462636429998827277154503238724889136792215497615596417863698274831955337179439675860391991034022113641840917581668387109675156626090096047604202190540490612404551220634224482372082861169673808065331200)

noncomputable def Gram657ProofSharing.c267 := (nat_lit 347679709441065926729893280390020887224232987260331239895357729413928282324412859620987880519972767811574732197149959762604915765969803988105019574596228185143385759103852351209183472853163083941781260814808986647625472461309952658226454848186061686467305884219085580215645330167731717959282424118420022655794351847948709259788314585973726904320)

noncomputable def Gram657ProofSharing.c268 := (nat_lit 66169350924723387020168265345265873509128985488887036216952390849566776420257388105950925969999477567227838335257347323182408925228719584041530599269997771906197585275734229531625041491086087519906403138878814436568633761566393815566311986721106216123788259998491287574559200045587364865662252743826532503907946149763504567324193587200)

noncomputable def Gram657ProofSharing.c269 := (BSN.artanhP (nat_lit 19963181825511696))

noncomputable def Gram657ProofSharing.c270 := (BSN.artanhQ (nat_lit 61906221825511696))

noncomputable def Gram657ProofSharing.c271 := (@BSN.binarySplit_of_base10 Gram657ProofSharing.c269 Gram657ProofSharing.c270 (nat_lit 0) (nat_lit 10) Gram657ProofSharing.c267 Gram657ProofSharing.c266 Gram657ProofSharing.c268 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c272 := (BSN.log_dyadic_bound (nat_lit 19963181825511696) (nat_lit 61906221825511696) (nat_lit 11) (nat_lit 10) Gram657ProofSharing.c266 (nat_lit 17179869184) (nat_lit 6600000000) Gram657ProofSharing.c267 Gram657ProofSharing.c268 (nat_lit 11490116960) (nat_lit 81869403651023392) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram657ProofSharing.c271 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c273 := (BSN.log_rat_reduce_isNear (nat_lit 40934701825511696) (nat_lit 160000000000) (nat_lit 17) (nat_lit 81869403651023392) (nat_lit 41943040000000000) (nat_lit 11490116960) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram657ProofSharing.c272 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c274 := (@Enclosure.Real.IsNear.recentre' Gram657ProofSharing.c265 Bool.false (nat_lit 7707609599105892722541592576) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56080240749767783) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram657ProofSharing.c273 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c275 := (BSN.isNear_log_sfrac (nat_lit 40934701825511696) (nat_lit 160000000000) (nat_lit 56080240749767783) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram657ProofSharing.c274)

noncomputable def Gram657ProofSharing.c276 := (@Enclosure.Real.IsNear.mulLit_ff Gram657ProofSharing.c256 Gram657ProofSharing.c258 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56080240749767783) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56080240749767783) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram657ProofSharing.c261 Gram657ProofSharing.c275 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c277 := (@Enclosure.Real.IsNear.of_eq (Gram657ProofSharing.c254 : ℂ).re Gram657ProofSharing.c259 Bool.false (nat_lit 56080240749767783) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram657ProofSharing.c260 Gram657ProofSharing.c276)

noncomputable def Gram657ProofSharing.c278 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 202323236))

noncomputable def Gram657ProofSharing.c279 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 100000))

noncomputable def Gram657ProofSharing.c280 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram657ProofSharing.c15 Gram657ProofSharing.c278 Gram657ProofSharing.c279)

noncomputable def Gram657ProofSharing.c281 := (Real.arctan Gram657ProofSharing.c280)

noncomputable def Gram657ProofSharing.c282 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 202323236) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c283 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram657ProofSharing.c256 Real.pi)

noncomputable def Gram657ProofSharing.c284 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram657ProofSharing.c15 Gram657ProofSharing.c279 Gram657ProofSharing.c278)

noncomputable def Gram657ProofSharing.c285 := (Real.arctan Gram657ProofSharing.c284)

noncomputable def Gram657ProofSharing.c286 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram657ProofSharing.c283 Gram657ProofSharing.c285)

noncomputable def Gram657ProofSharing.c287 := (BSN.arctan_recip (nat_lit 202323236) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c288 := (@Enclosure.Real.IsNear.mulLit_ff Gram657ProofSharing.c256 Real.pi (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 226375608064910080) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) Gram657ProofSharing.c261 BSN.pi_near_15 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c289 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 202323236)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c290 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 202323236)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c291 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 202323236) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8491297) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram657ProofSharing.c289 Gram657ProofSharing.c290 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c292 := (@Enclosure.Real.IsNear.subLit_ff_p Gram657ProofSharing.c283 Gram657ProofSharing.c285 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8491297) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187029719294717204627456) (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c288 Gram657ProofSharing.c291 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c293 := (@Enclosure.Real.IsNear.of_eq Gram657ProofSharing.c281 Gram657ProofSharing.c286 Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c287 Gram657ProofSharing.c292)

noncomputable def Gram657ProofSharing.c294 := (@Enclosure.Real.IsNear.of_eq (Gram657ProofSharing.c254 : ℂ).im Gram657ProofSharing.c281 Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c282 Gram657ProofSharing.c293)

noncomputable def Gram657ProofSharing.c295 := (@Enclosure.Complex.IsNear.of_parts Gram657ProofSharing.c254 Bool.false (nat_lit 56080240749767783) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c277 Gram657ProofSharing.c294)

noncomputable def Gram657ProofSharing.c296 := (@Enclosure.Complex.IsNear.of_eq Gram657ProofSharing.c235 Gram657ProofSharing.c254 Bool.false (nat_lit 56080240749767783) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c255 Gram657ProofSharing.c295)

noncomputable def Gram657ProofSharing.c297 := (@Enclosure.Complex.IsNear.re_isNear Gram657ProofSharing.c235 Bool.false (nat_lit 56080240749767783) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c296)

noncomputable def Gram657ProofSharing.c298 := (@Enclosure.Complex.IsNear.im_isNear Gram657ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 202323236) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c252)

noncomputable def Gram657ProofSharing.c299 := (@Enclosure.Complex.IsNear.im_isNear Gram657ProofSharing.c235 Bool.false (nat_lit 56080240749767783) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c296)

noncomputable def Gram657ProofSharing.c300 := (↑Gram657ProofSharing.c8)

noncomputable def Gram657ProofSharing.c301 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c233 : ℂ).re (Gram657ProofSharing.c300 : ℂ).re)

noncomputable def Gram657ProofSharing.c302 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c233 : ℂ).im (Gram657ProofSharing.c300 : ℂ).im)

noncomputable def Gram657ProofSharing.c303 := (Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram657ProofSharing.c304 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram657ProofSharing.c305 := (@Enclosure.Complex.IsNear.mk Gram657ProofSharing.c256 Gram657ProofSharing.c303 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c261 Gram657ProofSharing.c304)

noncomputable def Gram657ProofSharing.c306 := (@Enclosure.Complex.IsNear.of_eq Gram657ProofSharing.c233 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) BSN.half_c_mk Gram657ProofSharing.c305)

noncomputable def Gram657ProofSharing.c307 := (@Enclosure.Complex.IsNear.re_isNear Gram657ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c306)

noncomputable def Gram657ProofSharing.c308 := (Complex.ofReal_re Gram657ProofSharing.c8)

noncomputable def Gram657ProofSharing.c309 := (@Enclosure.Real.IsNear.of_eq (Gram657ProofSharing.c300 : ℂ).re Gram657ProofSharing.c8 Bool.false (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) Gram657ProofSharing.c308 Zeta.Certificates.Gram.gp3_cert._proof_1)

noncomputable def Gram657ProofSharing.c310 := (@Enclosure.Real.IsNear.mulLit_ff (Gram657ProofSharing.c233 : ℂ).re (Gram657ProofSharing.c300 : ℂ).re (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram657ProofSharing.c307 Gram657ProofSharing.c309 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c311 := (@Enclosure.Complex.IsNear.im_isNear Gram657ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c306)

noncomputable def Gram657ProofSharing.c312 := (Complex.ofReal_im Gram657ProofSharing.c8)

noncomputable def Gram657ProofSharing.c313 := (@Eq.trans.{1} Real (Gram657ProofSharing.c300 : ℂ).im Gram657ProofSharing.c147 Gram657ProofSharing.c303 Gram657ProofSharing.c312 Enclosure.sfrac_zero_eq)

noncomputable def Gram657ProofSharing.c314 := (@Enclosure.Real.IsNear.of_eq (Gram657ProofSharing.c300 : ℂ).im Gram657ProofSharing.c303 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c313 Gram657ProofSharing.c304)

noncomputable def Gram657ProofSharing.c315 := (@Enclosure.Real.IsNear.mulLit_ff (Gram657ProofSharing.c233 : ℂ).im (Gram657ProofSharing.c300 : ℂ).im (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c311 Gram657ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c316 := (@Enclosure.Real.IsNear.subLit_ff_p Gram657ProofSharing.c301 Gram657ProofSharing.c302 (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram657ProofSharing.c310 Gram657ProofSharing.c315 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c317 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c233 : ℂ).re (Gram657ProofSharing.c300 : ℂ).im)

noncomputable def Gram657ProofSharing.c318 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c233 : ℂ).im (Gram657ProofSharing.c300 : ℂ).re)

noncomputable def Gram657ProofSharing.c319 := (@Enclosure.Real.IsNear.mulLit_ff (Gram657ProofSharing.c233 : ℂ).re (Gram657ProofSharing.c300 : ℂ).im (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c307 Gram657ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c320 := (@Enclosure.Real.IsNear.mulLit_ff (Gram657ProofSharing.c233 : ℂ).im (Gram657ProofSharing.c300 : ℂ).re (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c311 Gram657ProofSharing.c309 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c321 := (@Enclosure.Real.IsNear.addLit_ff Gram657ProofSharing.c317 Gram657ProofSharing.c318 (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c319 Gram657ProofSharing.c320 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c322 := (@Enclosure.Complex.IsNear.mul Gram657ProofSharing.c233 Gram657ProofSharing.c300 Bool.false (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c316 Gram657ProofSharing.c321)

noncomputable def Gram657ProofSharing.c323 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram657ProofSharing.c32 (nat_lit 2))

noncomputable def Gram657ProofSharing.c324 := (bernoulli Gram657ProofSharing.c323)

noncomputable def Gram657ProofSharing.c325 := (@Rat.cast.{0} Complex Complex.instRatCast Gram657ProofSharing.c324)

noncomputable def Gram657ProofSharing.c326 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2))

noncomputable def Gram657ProofSharing.c327 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram657ProofSharing.c42 Gram657ProofSharing.c326)

noncomputable def Gram657ProofSharing.c328 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram657ProofSharing.c327 Gram657ProofSharing.c30)

noncomputable def Gram657ProofSharing.c329 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram657ProofSharing.c327 Gram657ProofSharing.c328)

noncomputable def Gram657ProofSharing.c330 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram657ProofSharing.c28 Gram657ProofSharing.c325 Gram657ProofSharing.c329)

noncomputable def Gram657ProofSharing.c331 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 2))

noncomputable def Gram657ProofSharing.c332 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram657ProofSharing.c244 Gram657ProofSharing.c331)

noncomputable def Gram657ProofSharing.c333 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram657ProofSharing.c243 Gram657ProofSharing.c332)

noncomputable def Gram657ProofSharing.c334 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram657ProofSharing.c242 Gram657ProofSharing.c47 Gram657ProofSharing.c333)

noncomputable def Gram657ProofSharing.c335 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram657ProofSharing.c330 Gram657ProofSharing.c334)

noncomputable def Gram657ProofSharing.c336 := (nat_lit 2391562131438346959245669407733897)

noncomputable def Gram657ProofSharing.c337 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram657ProofSharing.c32 (nat_lit 1))

noncomputable def Gram657ProofSharing.c338 := (bernoulli Gram657ProofSharing.c337)

noncomputable def Gram657ProofSharing.c339 := (@Rat.cast.{0} Complex Complex.instRatCast Gram657ProofSharing.c338)

noncomputable def Gram657ProofSharing.c340 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 1))

noncomputable def Gram657ProofSharing.c341 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram657ProofSharing.c42 Gram657ProofSharing.c340)

noncomputable def Gram657ProofSharing.c342 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram657ProofSharing.c341 Gram657ProofSharing.c30)

noncomputable def Gram657ProofSharing.c343 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram657ProofSharing.c341 Gram657ProofSharing.c342)

noncomputable def Gram657ProofSharing.c344 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram657ProofSharing.c28 Gram657ProofSharing.c339 Gram657ProofSharing.c343)

noncomputable def Gram657ProofSharing.c345 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 1))

noncomputable def Gram657ProofSharing.c346 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram657ProofSharing.c244 Gram657ProofSharing.c345)

noncomputable def Gram657ProofSharing.c347 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram657ProofSharing.c243 Gram657ProofSharing.c346)

noncomputable def Gram657ProofSharing.c348 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram657ProofSharing.c242 Gram657ProofSharing.c47 Gram657ProofSharing.c347)

noncomputable def Gram657ProofSharing.c349 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram657ProofSharing.c344 Gram657ProofSharing.c348)

noncomputable def Gram657ProofSharing.c350 := (@Enclosure.Complex.IsNear.mk Gram657ProofSharing.c303 Gram657ProofSharing.c303 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c304 Gram657ProofSharing.c304)

noncomputable def Gram657ProofSharing.c351 := (BSN.stirling_coeff_mk (nat_lit 1) (nat_lit 1) (nat_lit 6) Bool.false BSN.bern_real_1 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c352 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram657ProofSharing.c353 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram657ProofSharing.c354 := (@Enclosure.Complex.IsNear.mk Gram657ProofSharing.c352 Gram657ProofSharing.c303 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c353 Gram657ProofSharing.c304)

noncomputable def Gram657ProofSharing.c355 := (@Enclosure.Complex.IsNear.of_eq Gram657ProofSharing.c344 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c351 Gram657ProofSharing.c354)

noncomputable def Gram657ProofSharing.c356 := (@Enclosure.Complex.IsNear.re_isNear Gram657ProofSharing.c344 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c355)

noncomputable def Gram657ProofSharing.c357 := (@Inv.inv.{0} Complex Complex.instInv Gram657ProofSharing.c50)

noncomputable def Gram657ProofSharing.c358 := (BSN.zpow_one_sub_two_mul Gram657ProofSharing.c47 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c359 := (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)

noncomputable def Gram657ProofSharing.c360 := (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring)

noncomputable def Gram657ProofSharing.c361 := (@MonoidWithZeroHom.{0, 0} Complex Real Gram657ProofSharing.c359 Gram657ProofSharing.c360)

noncomputable def Gram657ProofSharing.c362 := (@MonoidWithZeroHom.funLike.{0, 0} Complex Real Gram657ProofSharing.c359 Gram657ProofSharing.c360)

noncomputable def Gram657ProofSharing.c363 := (Enclosure.Complex.inv_re_eq_mul Gram657ProofSharing.c50)

noncomputable def Gram657ProofSharing.c364 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c50 : ℂ).re (Gram657ProofSharing.c50 : ℂ).re)

noncomputable def Gram657ProofSharing.c365 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c50 : ℂ).im (Gram657ProofSharing.c50 : ℂ).im)

noncomputable def Gram657ProofSharing.c366 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram657ProofSharing.c364 Gram657ProofSharing.c365)

noncomputable def Gram657ProofSharing.c367 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram657ProofSharing.c50)

noncomputable def Gram657ProofSharing.c368 := (@Enclosure.Real.IsNear.mulLit_ff (Gram657ProofSharing.c50 : ℂ).re (Gram657ProofSharing.c50 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c65 Gram657ProofSharing.c65 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c369 := (@Enclosure.Real.IsNear.mulLit_ff (Gram657ProofSharing.c50 : ℂ).im (Gram657ProofSharing.c50 : ℂ).im (nat_lit 202323236) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 202323236) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 2558418239094481) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c68 Gram657ProofSharing.c68 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c370 := (@Enclosure.Real.IsNear.addLit_ff Gram657ProofSharing.c364 Gram657ProofSharing.c365 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 2558418239094481) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) (nat_lit 40934701825511696) (nat_lit 2558418864094481) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c368 Gram657ProofSharing.c369 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c371 := (@Neg.neg.{0} Real Real.instNeg (Gram657ProofSharing.c50 : ℂ).im)

noncomputable def Gram657ProofSharing.c372 := (Enclosure.Complex.inv_im_eq_mul Gram657ProofSharing.c50)

noncomputable def Gram657ProofSharing.c373 := (@Enclosure.Real.IsNear.neg (Gram657ProofSharing.c50 : ℂ).im Bool.false (nat_lit 202323236) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c68)

noncomputable def Gram657ProofSharing.c374 := (@Enclosure.Complex.IsNear.im_isNear Gram657ProofSharing.c344 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c355)

noncomputable def Gram657ProofSharing.c375 := (nat_lit 12379400392853802748991242240000000000)

noncomputable def Gram657ProofSharing.c376 := (BSN.stirling_coeff_mk (nat_lit 2) (nat_lit 1) (nat_lit 30) Bool.true BSN.bern_real_2 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c377 := (Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram657ProofSharing.c378 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram657ProofSharing.c379 := (@Enclosure.Complex.IsNear.mk Gram657ProofSharing.c377 Gram657ProofSharing.c303 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c378 Gram657ProofSharing.c304)

noncomputable def Gram657ProofSharing.c380 := (@Enclosure.Complex.IsNear.of_eq Gram657ProofSharing.c330 { re := Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c376 Gram657ProofSharing.c379)

noncomputable def Gram657ProofSharing.c381 := (@Enclosure.Complex.IsNear.re_isNear Gram657ProofSharing.c330 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c380)

noncomputable def Gram657ProofSharing.c382 := (nat_lit 309485009821345068724781056000000000000000)

noncomputable def Gram657ProofSharing.c383 := (@Inv.inv.{0} Complex Complex.instInv Gram657ProofSharing.c48)

noncomputable def Gram657ProofSharing.c384 := (BSN.zpow_one_sub_two_mul Gram657ProofSharing.c47 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c385 := (Enclosure.Complex.inv_re_eq_mul Gram657ProofSharing.c48)

noncomputable def Gram657ProofSharing.c386 := (@Enclosure.Complex.IsNear.re_isNear Gram657ProofSharing.c48 Bool.true (nat_lit 7675254092283443) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 129406769454737401415129) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp3_cert._proof_2)

noncomputable def Gram657ProofSharing.c387 := (nat_lit 16746148799164920124048444510843625157415086641)

noncomputable def Gram657ProofSharing.c388 := (nat_lit 1000000000000000000000000000000)

noncomputable def Gram657ProofSharing.c389 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c48 : ℂ).re (Gram657ProofSharing.c48 : ℂ).re)

noncomputable def Gram657ProofSharing.c390 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c48 : ℂ).im (Gram657ProofSharing.c48 : ℂ).im)

noncomputable def Gram657ProofSharing.c391 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram657ProofSharing.c389 Gram657ProofSharing.c390)

noncomputable def Gram657ProofSharing.c392 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram657ProofSharing.c48)

noncomputable def Gram657ProofSharing.c393 := (nat_lit 58909525381113738555277851934249)

noncomputable def Gram657ProofSharing.c394 := (nat_lit 16746111980711556927961847462186166251790086641)

noncomputable def Gram657ProofSharing.c395 := (nat_lit 26793838078663872198477511217349800251864138625600000000000000000000)

noncomputable def Gram657ProofSharing.c396 := (@Enclosure.Real.IsNear.mulLit_tt (Gram657ProofSharing.c48 : ℂ).re (Gram657ProofSharing.c48 : ℂ).re (nat_lit 7675254092283443) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 7675254092283443) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c393 (nat_lit 1600000000000000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c386 Gram657ProofSharing.c386 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c397 := (@Enclosure.Complex.IsNear.im_isNear Gram657ProofSharing.c48 Bool.true (nat_lit 7675254092283443) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 129406769454737401415129) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp3_cert._proof_2)

noncomputable def Gram657ProofSharing.c398 := (@Enclosure.Real.IsNear.mulLit_tt (Gram657ProofSharing.c48 : ℂ).im (Gram657ProofSharing.c48 : ℂ).im (nat_lit 129406769454737401415129) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 129406769454737401415129) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c394 Gram657ProofSharing.c388 (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c397 Gram657ProofSharing.c397 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c399 := (@Enclosure.Real.IsNear.addLit_ff Gram657ProofSharing.c389 Gram657ProofSharing.c390 Gram657ProofSharing.c393 (nat_lit 1600000000000000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c394 Gram657ProofSharing.c388 (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c395 Gram657ProofSharing.c387 Gram657ProofSharing.c388 (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c396 Gram657ProofSharing.c398 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c400 := (@Neg.neg.{0} Real Real.instNeg (Gram657ProofSharing.c48 : ℂ).im)

noncomputable def Gram657ProofSharing.c401 := (Enclosure.Complex.inv_im_eq_mul Gram657ProofSharing.c48)

noncomputable def Gram657ProofSharing.c402 := (@Enclosure.Real.IsNear.neg (Gram657ProofSharing.c48 : ℂ).im Bool.true (nat_lit 129406769454737401415129) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c397)

noncomputable def Gram657ProofSharing.c403 := (@Enclosure.Complex.IsNear.im_isNear Gram657ProofSharing.c330 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c380)

noncomputable def Gram657ProofSharing.c404 := (BSN.logSumC Gram657ProofSharing.c39 (nat_lit 0))

noncomputable def Gram657ProofSharing.c405 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram657ProofSharing.c106)

noncomputable def Gram657ProofSharing.c406 := (@Monoid.toNPow.{0} Real Real.instMonoid)

noncomputable def Gram657ProofSharing.c407 := (@NPow.toPow.{0} Real Gram657ProofSharing.c406)

noncomputable def Gram657ProofSharing.c408 := (@instHPow.{0, 0} Real Nat Gram657ProofSharing.c407)

noncomputable def Gram657ProofSharing.c409 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram657ProofSharing.c408 Gram657ProofSharing.c7 (nat_lit 4))

noncomputable def Gram657ProofSharing.c410 := (@Inv.inv.{0} Real Real.instInv Gram657ProofSharing.c409)

noncomputable def Gram657ProofSharing.c411 := (nat_lit 611446774371975769155682509262542103857872115376664175900625)

noncomputable def Gram657ProofSharing.c412 := (nat_lit 392318858461667547739736838950479151006397215279002157056)

noncomputable def Gram657ProofSharing.c413 := (nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047)

noncomputable def Gram657ProofSharing.c414 := (nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram657ProofSharing.c415 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram657ProofSharing.c408 Gram657ProofSharing.c7 (nat_lit 3))

noncomputable def Gram657ProofSharing.c416 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram657ProofSharing.c415 Gram657ProofSharing.c7)

noncomputable def Gram657ProofSharing.c417 := (BSN.pow_succ_r Gram657ProofSharing.c7 (nat_lit 3) (nat_lit 4) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c418 := (nat_lit 691463075802508163054686763366652189853178875)

noncomputable def Gram657ProofSharing.c419 := (nat_lit 2787593149816327892691964784081045188247552)

noncomputable def Gram657ProofSharing.c420 := (nat_lit 2184744797947834540264818678394244808492865883128339)

noncomputable def Gram657ProofSharing.c421 := (nat_lit 9223372036854775808000000000000000000000000000000000000000000000)

noncomputable def Gram657ProofSharing.c422 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram657ProofSharing.c408 Gram657ProofSharing.c7 (nat_lit 2))

noncomputable def Gram657ProofSharing.c423 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram657ProofSharing.c422 Gram657ProofSharing.c7)

noncomputable def Gram657ProofSharing.c424 := (BSN.pow_succ_r Gram657ProofSharing.c7 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c425 := (nat_lit 1073741824000000000000000000000000000000)

noncomputable def Gram657ProofSharing.c426 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram657ProofSharing.c408 Gram657ProofSharing.c7 (nat_lit 1))

noncomputable def Gram657ProofSharing.c427 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram657ProofSharing.c426 Gram657ProofSharing.c7)

noncomputable def Gram657ProofSharing.c428 := (BSN.pow_succ_r Gram657ProofSharing.c7 (nat_lit 1) (nat_lit 2) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c429 := (BSN.pow_one_r Gram657ProofSharing.c7)

noncomputable def Gram657ProofSharing.c430 := (@Enclosure.Real.IsNear.of_eq Gram657ProofSharing.c7 Gram657ProofSharing.c10 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) BSN.two_pi_eq Gram657ProofSharing.c13)

noncomputable def Gram657ProofSharing.c431 := (@Enclosure.Real.IsNear.of_eq Gram657ProofSharing.c426 Gram657ProofSharing.c7 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram657ProofSharing.c429 Gram657ProofSharing.c430)

noncomputable def Gram657ProofSharing.c432 := (@Enclosure.Real.IsNear.mulLit_ff Gram657ProofSharing.c426 Gram657ProofSharing.c7 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram657ProofSharing.c425 Gram657ProofSharing.c431 Gram657ProofSharing.c430 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c433 := (@Enclosure.Real.IsNear.of_eq Gram657ProofSharing.c422 Gram657ProofSharing.c427 Bool.false (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram657ProofSharing.c425 Gram657ProofSharing.c428 Gram657ProofSharing.c432)

noncomputable def Gram657ProofSharing.c434 := (@Enclosure.Real.IsNear.mulLit_ff Gram657ProofSharing.c422 Gram657ProofSharing.c7 (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram657ProofSharing.c425 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram657ProofSharing.c418 Gram657ProofSharing.c419 Gram657ProofSharing.c420 Gram657ProofSharing.c421 Gram657ProofSharing.c433 Gram657ProofSharing.c430 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c435 := (@Enclosure.Real.IsNear.of_eq Gram657ProofSharing.c415 Gram657ProofSharing.c423 Bool.false Gram657ProofSharing.c418 Gram657ProofSharing.c419 Gram657ProofSharing.c420 Gram657ProofSharing.c421 Gram657ProofSharing.c424 Gram657ProofSharing.c434)

noncomputable def Gram657ProofSharing.c436 := (@Enclosure.Real.IsNear.mulLit_ff Gram657ProofSharing.c415 Gram657ProofSharing.c7 Gram657ProofSharing.c418 Gram657ProofSharing.c419 Gram657ProofSharing.c420 Gram657ProofSharing.c421 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram657ProofSharing.c411 Gram657ProofSharing.c412 Gram657ProofSharing.c413 Gram657ProofSharing.c414 Gram657ProofSharing.c435 Gram657ProofSharing.c430 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c437 := (@Enclosure.Real.IsNear.of_eq Gram657ProofSharing.c409 Gram657ProofSharing.c416 Bool.false Gram657ProofSharing.c411 Gram657ProofSharing.c412 Gram657ProofSharing.c413 Gram657ProofSharing.c414 Gram657ProofSharing.c417 Gram657ProofSharing.c436)

noncomputable def Gram657ProofSharing.c438 := (@Enclosure.Real.IsNear.inv_image Gram657ProofSharing.c409 Gram657ProofSharing.c411 Gram657ProofSharing.c412 Gram657ProofSharing.c413 Gram657ProofSharing.c414 (nat_lit 5511507) (nat_lit 5511508) (nat_lit 8589934592) Gram657ProofSharing.c437 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c439 := (@Enclosure.Real.IsNear.recentre' Gram657ProofSharing.c410 Bool.false (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) Gram657ProofSharing.c438 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c440 := (nat_lit 7780469705413838346251907407016920286559)

noncomputable def Gram657ProofSharing.c441 := (nat_lit 178263365657094759585473888256000000000000000)

noncomputable def Gram657ProofSharing.c442 := (nat_lit 956729421849510854359037802967568442938879)

noncomputable def Gram657ProofSharing.c443 := (nat_lit 6127803194462632360750664908800000000000000000000)

noncomputable def Gram657ProofSharing.c444 := (nat_lit 1675650012312551531672889924238096)

noncomputable def Gram657ProofSharing.c445 := (riemannSiegelThetaApproximant (nat_lit 2) (nat_lit 0) Gram657ProofSharing.c107)

noncomputable def Gram657ProofSharing.c446 := (nat_lit 367940295909275292812912738561667407016920286559)

noncomputable def Gram657ProofSharing.c447 := (nat_lit 956725395882812092409576789780723361338879)

noncomputable def Gram657ProofSharing.c448 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram657ProofSharing.c112)

noncomputable def Gram657ProofSharing.c449 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram657ProofSharing.c15 Gram657ProofSharing.c107 Gram657ProofSharing.c6)

noncomputable def Gram657ProofSharing.c450 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram657ProofSharing.c449 (Real.log Real.pi))

noncomputable def Gram657ProofSharing.c451 := (nat_lit 471157218675899270100240342849568939176920286559)

noncomputable def Gram657ProofSharing.c452 := (nat_lit 235068557077376269202095445780723361338879)

noncomputable def Gram657ProofSharing.c453 := (nat_lit 2834954798528721087932448597250315539045737)

noncomputable def Gram657ProofSharing.c454 := (nat_lit 3565267313141895191709477765120000000000)

noncomputable def Gram657ProofSharing.c455 := (nat_lit 29403191805423168077559576951830741094557)

noncomputable def Gram657ProofSharing.c456 := (nat_lit 382987699653914522546916556800000000000000000000)

noncomputable def Gram657ProofSharing.c457 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram657ProofSharing.c112 Gram657ProofSharing.c233)

noncomputable def Gram657ProofSharing.c458 := (Complex.log Gram657ProofSharing.c112)

noncomputable def Gram657ProofSharing.c459 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram657ProofSharing.c457 Gram657ProofSharing.c458)

noncomputable def Gram657ProofSharing.c460 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram657ProofSharing.c459 Gram657ProofSharing.c112)

noncomputable def Gram657ProofSharing.c461 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram657ProofSharing.c460 Gram657ProofSharing.c238)

noncomputable def Gram657ProofSharing.c462 := (nat_lit 290321604597473540574060064154263)

noncomputable def Gram657ProofSharing.c463 := (nat_lit 17826336565709475958547388825600000000000)

noncomputable def Gram657ProofSharing.c464 := (nat_lit 29369396479395857714853067318103079713441)

noncomputable def Gram657ProofSharing.c465 := (nat_lit 8342129428316906608136050086061)

noncomputable def Gram657ProofSharing.c466 := (nat_lit 891316828285473797927369441280000000000000000)

noncomputable def Gram657ProofSharing.c467 := (BSN.w_sub_half_zero_mk Gram657ProofSharing.c107 Bool.false (nat_lit 101161621) (nat_lit 100000) Gram657ProofSharing.c121 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c468 := (@Enclosure.Complex.IsNear.mk Gram657ProofSharing.c249 Gram657ProofSharing.c123 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 202323242) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c250 Gram657ProofSharing.c124)

noncomputable def Gram657ProofSharing.c469 := (@Enclosure.Complex.IsNear.of_eq Gram657ProofSharing.c457 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 202323242) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 202323242) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c467 Gram657ProofSharing.c468)

noncomputable def Gram657ProofSharing.c470 := (@Enclosure.Complex.IsNear.re_isNear Gram657ProofSharing.c457 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 202323242) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c469)

noncomputable def Gram657ProofSharing.c471 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 202323242) (nat_lit 400000) })

noncomputable def Gram657ProofSharing.c472 := (@congrArg.{1, 1} Complex Complex Gram657ProofSharing.c112 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 202323242) (nat_lit 400000) } Complex.log Gram657ProofSharing.c122)

noncomputable def Gram657ProofSharing.c473 := (Enclosure.sfrac Bool.false (nat_lit 40934704253390564) (nat_lit 160000000000))

noncomputable def Gram657ProofSharing.c474 := (Real.log Gram657ProofSharing.c473)

noncomputable def Gram657ProofSharing.c475 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram657ProofSharing.c256 Gram657ProofSharing.c474)

noncomputable def Gram657ProofSharing.c476 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 202323242) (nat_lit 400000) (nat_lit 40934704253390564) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c477 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40934704253390564))

noncomputable def Gram657ProofSharing.c478 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram657ProofSharing.c15 Gram657ProofSharing.c477 Gram657ProofSharing.c263)

noncomputable def Gram657ProofSharing.c479 := (Real.log Gram657ProofSharing.c478)

noncomputable def Gram657ProofSharing.c480 := (nat_lit 9396524577467904872467784172877634499272196776290517034919565595174648838775638214900423494883227779402443709239857974379283082339131665107951437724337162163835523251937514168858697205104018172361498654565813144910464099485028695923196257063402561229005125868310039206656840683731758676071004507661616123189004562881778801826538400389950288691200)

noncomputable def Gram657ProofSharing.c481 := (nat_lit 347680043363598914879149230488695400160025419887662155458085063518607600697685326915485181810898509682239175898625818835991305602925508560383958304252690498251682332780053072697660446970538663088905512129975337869339913167766189930501037280631766983486345255284362919950248815086122682209971791220401526385936466020972181179039147851887484600320)

noncomputable def Gram657ProofSharing.c482 := (nat_lit 66169511872367740675725569823412529767317973103777179513749283479499725003229394987563636836917589782219769548099278993728626897782289019801407312717384562267559648156534501889065082816740950679283480298902441330498764342925525607341475212405563005249945221972465663685096153757335134078192115599370949736856404725087161130950013747200)

noncomputable def Gram657ProofSharing.c483 := (BSN.artanhP (nat_lit 19963184253390564))

noncomputable def Gram657ProofSharing.c484 := (BSN.artanhQ (nat_lit 61906224253390564))

noncomputable def Gram657ProofSharing.c485 := (@BSN.binarySplit_of_base10 Gram657ProofSharing.c483 Gram657ProofSharing.c484 (nat_lit 0) (nat_lit 10) Gram657ProofSharing.c481 Gram657ProofSharing.c480 Gram657ProofSharing.c482 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c486 := (BSN.log_dyadic_bound (nat_lit 19963184253390564) (nat_lit 61906224253390564) (nat_lit 11) (nat_lit 10) Gram657ProofSharing.c480 (nat_lit 17179869184) (nat_lit 6600000000) Gram657ProofSharing.c481 Gram657ProofSharing.c482 (nat_lit 11490117979) (nat_lit 81869408506781128) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram657ProofSharing.c485 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c487 := (BSN.log_rat_reduce_isNear (nat_lit 40934704253390564) (nat_lit 160000000000) (nat_lit 17) (nat_lit 81869408506781128) (nat_lit 41943040000000000) (nat_lit 11490117979) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram657ProofSharing.c486 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c488 := (@Enclosure.Real.IsNear.recentre' Gram657ProofSharing.c479 Bool.false (nat_lit 7707609635819236884865875968) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56080241016892519) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram657ProofSharing.c487 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c489 := (BSN.isNear_log_sfrac (nat_lit 40934704253390564) (nat_lit 160000000000) (nat_lit 56080241016892519) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram657ProofSharing.c488)

noncomputable def Gram657ProofSharing.c490 := (@Enclosure.Real.IsNear.mulLit_ff Gram657ProofSharing.c256 Gram657ProofSharing.c474 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56080241016892519) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56080241016892519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram657ProofSharing.c261 Gram657ProofSharing.c489 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c491 := (@Enclosure.Real.IsNear.of_eq (Gram657ProofSharing.c471 : ℂ).re Gram657ProofSharing.c475 Bool.false (nat_lit 56080241016892519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram657ProofSharing.c476 Gram657ProofSharing.c490)

noncomputable def Gram657ProofSharing.c492 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 202323242))

noncomputable def Gram657ProofSharing.c493 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram657ProofSharing.c15 Gram657ProofSharing.c492 Gram657ProofSharing.c279)

noncomputable def Gram657ProofSharing.c494 := (Real.arctan Gram657ProofSharing.c493)

noncomputable def Gram657ProofSharing.c495 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 202323242) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c496 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram657ProofSharing.c15 Gram657ProofSharing.c279 Gram657ProofSharing.c492)

noncomputable def Gram657ProofSharing.c497 := (Real.arctan Gram657ProofSharing.c496)

noncomputable def Gram657ProofSharing.c498 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram657ProofSharing.c283 Gram657ProofSharing.c497)

noncomputable def Gram657ProofSharing.c499 := (BSN.arctan_recip (nat_lit 202323242) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c500 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 202323242)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c501 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 202323242)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c502 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 202323242) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8491297) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram657ProofSharing.c500 Gram657ProofSharing.c501 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c503 := (@Enclosure.Real.IsNear.subLit_ff_p Gram657ProofSharing.c283 Gram657ProofSharing.c497 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8491297) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187029719294717204627456) (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c288 Gram657ProofSharing.c502 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c504 := (@Enclosure.Real.IsNear.of_eq Gram657ProofSharing.c494 Gram657ProofSharing.c498 Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c499 Gram657ProofSharing.c503)

noncomputable def Gram657ProofSharing.c505 := (@Enclosure.Real.IsNear.of_eq (Gram657ProofSharing.c471 : ℂ).im Gram657ProofSharing.c494 Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c495 Gram657ProofSharing.c504)

noncomputable def Gram657ProofSharing.c506 := (@Enclosure.Complex.IsNear.of_parts Gram657ProofSharing.c471 Bool.false (nat_lit 56080241016892519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c491 Gram657ProofSharing.c505)

noncomputable def Gram657ProofSharing.c507 := (@Enclosure.Complex.IsNear.of_eq Gram657ProofSharing.c458 Gram657ProofSharing.c471 Bool.false (nat_lit 56080241016892519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c472 Gram657ProofSharing.c506)

noncomputable def Gram657ProofSharing.c508 := (@Enclosure.Complex.IsNear.re_isNear Gram657ProofSharing.c458 Bool.false (nat_lit 56080241016892519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c507)

noncomputable def Gram657ProofSharing.c509 := (@Enclosure.Complex.IsNear.im_isNear Gram657ProofSharing.c457 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 202323242) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c469)

noncomputable def Gram657ProofSharing.c510 := (@Enclosure.Complex.IsNear.im_isNear Gram657ProofSharing.c458 Bool.false (nat_lit 56080241016892519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884001476183459) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram657ProofSharing.c507)

noncomputable def Gram657ProofSharing.c511 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram657ProofSharing.c242 Gram657ProofSharing.c112 Gram657ProofSharing.c333)

noncomputable def Gram657ProofSharing.c512 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram657ProofSharing.c330 Gram657ProofSharing.c511)

noncomputable def Gram657ProofSharing.c513 := (nat_lit 3826499069948783838323543079713441)

noncomputable def Gram657ProofSharing.c514 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram657ProofSharing.c242 Gram657ProofSharing.c112 Gram657ProofSharing.c347)

noncomputable def Gram657ProofSharing.c515 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram657ProofSharing.c344 Gram657ProofSharing.c514)

noncomputable def Gram657ProofSharing.c516 := (@Inv.inv.{0} Complex Complex.instInv Gram657ProofSharing.c115)

noncomputable def Gram657ProofSharing.c517 := (BSN.zpow_one_sub_two_mul Gram657ProofSharing.c112 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c518 := (Enclosure.Complex.inv_re_eq_mul Gram657ProofSharing.c115)

noncomputable def Gram657ProofSharing.c519 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c115 : ℂ).re (Gram657ProofSharing.c115 : ℂ).re)

noncomputable def Gram657ProofSharing.c520 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c115 : ℂ).im (Gram657ProofSharing.c115 : ℂ).im)

noncomputable def Gram657ProofSharing.c521 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram657ProofSharing.c519 Gram657ProofSharing.c520)

noncomputable def Gram657ProofSharing.c522 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram657ProofSharing.c115)

noncomputable def Gram657ProofSharing.c523 := (@Enclosure.Real.IsNear.mulLit_ff (Gram657ProofSharing.c115 : ℂ).re (Gram657ProofSharing.c115 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c128 Gram657ProofSharing.c128 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c524 := (@Enclosure.Real.IsNear.mulLit_ff (Gram657ProofSharing.c115 : ℂ).im (Gram657ProofSharing.c115 : ℂ).im (nat_lit 202323242) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 202323242) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 10233673563347641) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c131 Gram657ProofSharing.c131 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c525 := (@Enclosure.Real.IsNear.addLit_ff Gram657ProofSharing.c519 Gram657ProofSharing.c520 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 10233673563347641) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 163738817013562256) (nat_lit 10233676063347641) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c523 Gram657ProofSharing.c524 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c526 := (@Neg.neg.{0} Real Real.instNeg (Gram657ProofSharing.c115 : ℂ).im)

noncomputable def Gram657ProofSharing.c527 := (Enclosure.Complex.inv_im_eq_mul Gram657ProofSharing.c115)

noncomputable def Gram657ProofSharing.c528 := (@Enclosure.Real.IsNear.neg (Gram657ProofSharing.c115 : ℂ).im Bool.false (nat_lit 202323242) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c131)

noncomputable def Gram657ProofSharing.c529 := (nat_lit 9903520314283042199192993792000000000)

noncomputable def Gram657ProofSharing.c530 := (nat_lit 49517601571415210995964968960000000000)

noncomputable def Gram657ProofSharing.c531 := (nat_lit 495176015714152109959649689600000000000000)

noncomputable def Gram657ProofSharing.c532 := (nat_lit 2475880078570760549798248448000000000000000)

noncomputable def Gram657ProofSharing.c533 := (@Inv.inv.{0} Complex Complex.instInv Gram657ProofSharing.c113)

noncomputable def Gram657ProofSharing.c534 := (BSN.zpow_one_sub_two_mul Gram657ProofSharing.c112 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c535 := (Enclosure.Complex.inv_re_eq_mul Gram657ProofSharing.c113)

noncomputable def Gram657ProofSharing.c536 := (@Enclosure.Complex.IsNear.re_isNear Gram657ProofSharing.c113 Bool.true (nat_lit 30701018190042923) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1035254247740936050086061) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp3_cert._proof_6)

noncomputable def Gram657ProofSharing.c537 := (nat_lit 1071753713846946158129074230670723854628006495721)

noncomputable def Gram657ProofSharing.c538 := (nat_lit 64000000000000000000000000000000)

noncomputable def Gram657ProofSharing.c539 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c113 : ℂ).re (Gram657ProofSharing.c113 : ℂ).re)

noncomputable def Gram657ProofSharing.c540 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram657ProofSharing.c113 : ℂ).im (Gram657ProofSharing.c113 : ℂ).im)

noncomputable def Gram657ProofSharing.c541 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram657ProofSharing.c539 Gram657ProofSharing.c540)

noncomputable def Gram657ProofSharing.c542 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram657ProofSharing.c113)

noncomputable def Gram657ProofSharing.c543 := (nat_lit 942552517905346435707540582383929)

noncomputable def Gram657ProofSharing.c544 := (nat_lit 1071751357465651394762984961819267894805506495721)

noncomputable def Gram657ProofSharing.c545 := (nat_lit 27436895074481821648104300305170530678476966290457600000000000000000000)

noncomputable def Gram657ProofSharing.c546 := (@Enclosure.Real.IsNear.mulLit_tt (Gram657ProofSharing.c113 : ℂ).re (Gram657ProofSharing.c113 : ℂ).re (nat_lit 30701018190042923) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) (nat_lit 30701018190042923) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c543 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c536 Gram657ProofSharing.c536 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c547 := (@Enclosure.Complex.IsNear.im_isNear Gram657ProofSharing.c113 Bool.true (nat_lit 30701018190042923) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1035254247740936050086061) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp3_cert._proof_6)

noncomputable def Gram657ProofSharing.c548 := (@Enclosure.Real.IsNear.mulLit_tt (Gram657ProofSharing.c113 : ℂ).im (Gram657ProofSharing.c113 : ℂ).im (nat_lit 1035254247740936050086061) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 1035254247740936050086061) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c544 Gram657ProofSharing.c538 (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c547 Gram657ProofSharing.c547 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c549 := (@Enclosure.Real.IsNear.addLit_ff Gram657ProofSharing.c539 Gram657ProofSharing.c540 Gram657ProofSharing.c543 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c544 Gram657ProofSharing.c538 (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c545 Gram657ProofSharing.c537 Gram657ProofSharing.c538 (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c546 Gram657ProofSharing.c548 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram657ProofSharing.c550 := (@Neg.neg.{0} Real Real.instNeg (Gram657ProofSharing.c113 : ℂ).im)

noncomputable def Gram657ProofSharing.c551 := (Enclosure.Complex.inv_im_eq_mul Gram657ProofSharing.c113)

noncomputable def Gram657ProofSharing.c552 := (@Enclosure.Real.IsNear.neg (Gram657ProofSharing.c113 : ℂ).im Bool.true (nat_lit 1035254247740936050086061) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram657ProofSharing.c547)

noncomputable def Gram657ProofSharing.c553 := (BSN.logSumC Gram657ProofSharing.c107 (nat_lit 0))

noncomputable def Gram657ProofSharing.c554 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram657ProofSharing.c144)


