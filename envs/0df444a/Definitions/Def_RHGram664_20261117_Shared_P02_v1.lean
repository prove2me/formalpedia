-- Prove2me | Definitions.Def_RHGram664_20261117_Shared_P02_v1
-- name    : RHGram664_20261117_Shared_P02_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T23:12:59.014847+00:00
-- url     : https://prove2.me/theorems/28853a62-3700-468c-8da4-147a3eb018ea
-- title:
--   Gram 664 ordinary shared terms, part 2
-- statement:
--   Exact shared expressions and complete ordinary auxiliary proofs for the endpoint certificate of Gram point 664. No additional axioms or custom proof generators. Imports the already published analytic and numerical support modules.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; Apache-2.0. Ordinary proof export and exact sharing by Desenvolvimento RH. Full expanded strict AXLE and cumulative prefixes: 7942d1dd-16d9-4b48-9f9c-f9b4d27f195a.

import Definitions.Def_RHGram664_20261117_Shared_P01_v1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def Gram664ProofSharing.c225 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram664ProofSharing.c15 Gram664ProofSharing.c39 Gram664ProofSharing.c6)

noncomputable def Gram664ProofSharing.c226 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram664ProofSharing.c225 (Real.log Real.pi))

noncomputable def Gram664ProofSharing.c227 := (nat_lit 33052764583430235536205705426279085539184346851)

noncomputable def Gram664ProofSharing.c228 := (nat_lit 4939103297233586219182467062047882865333)

noncomputable def Gram664ProofSharing.c229 := (nat_lit 1191324462172037767912286810098971003373279)

noncomputable def Gram664ProofSharing.c230 := (nat_lit 1485528047142456329878949068800000000000)

noncomputable def Gram664ProofSharing.c231 := (nat_lit 654164730065802647662401888758567988631)

noncomputable def Gram664ProofSharing.c232 := (nat_lit 8704265901225330057884467200000000000000000000)

noncomputable def Gram664ProofSharing.c233 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram664ProofSharing.c28 Gram664ProofSharing.c30 Gram664ProofSharing.c42)

noncomputable def Gram664ProofSharing.c234 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram664ProofSharing.c47 Gram664ProofSharing.c233)

noncomputable def Gram664ProofSharing.c235 := (Complex.log Gram664ProofSharing.c47)

noncomputable def Gram664ProofSharing.c236 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c234 Gram664ProofSharing.c235)

noncomputable def Gram664ProofSharing.c237 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram664ProofSharing.c236 Gram664ProofSharing.c47)

noncomputable def Gram664ProofSharing.c238 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c233 ↑Gram664ProofSharing.c8)

noncomputable def Gram664ProofSharing.c239 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram664ProofSharing.c237 Gram664ProofSharing.c238)

noncomputable def Gram664ProofSharing.c240 := (@DivInvMonoid.toZPow.{0} Complex Complex.instDivInvMonoid)

noncomputable def Gram664ProofSharing.c241 := (@ZPow.toPow.{0} Complex Gram664ProofSharing.c240)

noncomputable def Gram664ProofSharing.c242 := (@instHPow.{0, 0} Complex Int Gram664ProofSharing.c241)

noncomputable def Gram664ProofSharing.c243 := (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))

noncomputable def Gram664ProofSharing.c244 := (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))

noncomputable def Gram664ProofSharing.c245 := (nat_lit 118925281775753681150070404626721)

noncomputable def Gram664ProofSharing.c246 := (nat_lit 4456584141427368989636847206400000000000)

noncomputable def Gram664ProofSharing.c247 := (nat_lit 2022253375846271999637834680860815653149)

noncomputable def Gram664ProofSharing.c248 := (BSN.w_sub_half_zero_mk Gram664ProofSharing.c39 Bool.false (nat_lit 102026442) (nat_lit 100000) Gram664ProofSharing.c56 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c249 := (Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram664ProofSharing.c250 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram664ProofSharing.c251 := (@Enclosure.Complex.IsNear.mk Gram664ProofSharing.c249 Gram664ProofSharing.c59 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204052884) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c250 Gram664ProofSharing.c61)

noncomputable def Gram664ProofSharing.c252 := (@Enclosure.Complex.IsNear.of_eq Gram664ProofSharing.c234 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204052884) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204052884) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c248 Gram664ProofSharing.c251)

noncomputable def Gram664ProofSharing.c253 := (@Enclosure.Complex.IsNear.re_isNear Gram664ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204052884) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c252)

noncomputable def Gram664ProofSharing.c254 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204052884) (nat_lit 400000) })

noncomputable def Gram664ProofSharing.c255 := (@congrArg.{1, 1} Complex Complex Gram664ProofSharing.c47 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204052884) (nat_lit 400000) } Complex.log Gram664ProofSharing.c57)

noncomputable def Gram664ProofSharing.c256 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram664ProofSharing.c257 := (Enclosure.sfrac Bool.false (nat_lit 41637589468717456) (nat_lit 160000000000))

noncomputable def Gram664ProofSharing.c258 := (Real.log Gram664ProofSharing.c257)

noncomputable def Gram664ProofSharing.c259 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram664ProofSharing.c256 Gram664ProofSharing.c258)

noncomputable def Gram664ProofSharing.c260 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 204052884) (nat_lit 400000) (nat_lit 41637589468717456) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c261 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram664ProofSharing.c262 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41637589468717456))

noncomputable def Gram664ProofSharing.c263 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 160000000000))

noncomputable def Gram664ProofSharing.c264 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram664ProofSharing.c15 Gram664ProofSharing.c262 Gram664ProofSharing.c263)

noncomputable def Gram664ProofSharing.c265 := (Real.log Gram664ProofSharing.c264)

noncomputable def Gram664ProofSharing.c266 := (nat_lit 11776912638389593756332854359202626864848612386658118467692275508172260095567361554676331329697704670941884905942110403221606514993388217278097899997877672673583977835082693601991982632567773360942518104118408290210452254940975741429419023858103932523610346900967514154931623071958592627331157033644056612359435074508642971036680129845166027571200)

noncomputable def Gram664ProofSharing.c267 := (nat_lit 458050347149051657417863201909055611110461378212361364408557113898363670794712658547512314775658050708679040963350028100816525373483257549616274828255056275048858687440262362718761922539423065698625738737293624527394060055312997807488637208402452015198770405361132684793176917241571093764119766504930406265134056921244802440721085017121693368320)

noncomputable def Gram664ProofSharing.c268 := (nat_lit 132196307910134962041330501281110540850767263689588686053927591990016426847620137400468112770496069914838362820029689344501021235090069450916965455071319914316106295501134655083734277652582133453113161107881202051399286507897598566905011710162968529140281207746907150478847006427141223881291034718545428103826079669930086365960287027200)

noncomputable def Gram664ProofSharing.c269 := (BSN.artanhP (nat_lit 20666069468717456))

noncomputable def Gram664ProofSharing.c270 := (BSN.artanhQ (nat_lit 62609109468717456))

noncomputable def Gram664ProofSharing.c271 := (@BSN.binarySplit_of_base10 Gram664ProofSharing.c269 Gram664ProofSharing.c270 (nat_lit 0) (nat_lit 10) Gram664ProofSharing.c267 Gram664ProofSharing.c266 Gram664ProofSharing.c268 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c272 := (BSN.log_dyadic_bound (nat_lit 20666069468717456) (nat_lit 62609109468717456) (nat_lit 11) (nat_lit 10) Gram664ProofSharing.c266 (nat_lit 17179869184) (nat_lit 6800000000) Gram664ProofSharing.c267 Gram664ProofSharing.c268 (nat_lit 11782607559) (nat_lit 83275178937434912) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram664ProofSharing.c271 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c273 := (BSN.log_rat_reduce_isNear (nat_lit 41637589468717456) (nat_lit 160000000000) (nat_lit 17) (nat_lit 83275178937434912) (nat_lit 41943040000000000) (nat_lit 11782607559) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6800000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram664ProofSharing.c272 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c274 := (@Enclosure.Real.IsNear.recentre' Gram664ProofSharing.c265 Bool.false (nat_lit 7718147683527218907901329408) (nat_lit 618970019642690137449562112) (nat_lit 1000115600000000) (nat_lit 6800000000000000000000000) (nat_lit 56156915405352039) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Gram664ProofSharing.c273 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c275 := (BSN.isNear_log_sfrac (nat_lit 41637589468717456) (nat_lit 160000000000) (nat_lit 56156915405352039) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Bool.false Gram664ProofSharing.c274)

noncomputable def Gram664ProofSharing.c276 := (@Enclosure.Real.IsNear.mulLit_ff Gram664ProofSharing.c256 Gram664ProofSharing.c258 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56156915405352039) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) (nat_lit 56156915405352039) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram664ProofSharing.c261 Gram664ProofSharing.c275 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c277 := (@Enclosure.Real.IsNear.of_eq (Gram664ProofSharing.c254 : ℂ).re Gram664ProofSharing.c259 Bool.false (nat_lit 56156915405352039) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram664ProofSharing.c260 Gram664ProofSharing.c276)

noncomputable def Gram664ProofSharing.c278 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 204052884))

noncomputable def Gram664ProofSharing.c279 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 100000))

noncomputable def Gram664ProofSharing.c280 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram664ProofSharing.c15 Gram664ProofSharing.c278 Gram664ProofSharing.c279)

noncomputable def Gram664ProofSharing.c281 := (Real.arctan Gram664ProofSharing.c280)

noncomputable def Gram664ProofSharing.c282 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 204052884) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c283 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram664ProofSharing.c256 Real.pi)

noncomputable def Gram664ProofSharing.c284 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram664ProofSharing.c15 Gram664ProofSharing.c279 Gram664ProofSharing.c278)

noncomputable def Gram664ProofSharing.c285 := (Real.arctan Gram664ProofSharing.c284)

noncomputable def Gram664ProofSharing.c286 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram664ProofSharing.c283 Gram664ProofSharing.c285)

noncomputable def Gram664ProofSharing.c287 := (BSN.arctan_recip (nat_lit 204052884) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c288 := (@Enclosure.Real.IsNear.mulLit_ff Gram664ProofSharing.c256 Real.pi (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 226375608064910080) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) Gram664ProofSharing.c261 BSN.pi_near_15 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c289 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 204052884)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c290 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 204052884)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c291 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 204052884) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6800000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8419321) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram664ProofSharing.c289 Gram664ProofSharing.c290 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c292 := (@Enclosure.Real.IsNear.subLit_ff_p Gram664ProofSharing.c283 Gram664ProofSharing.c285 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8419321) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6800000000) (nat_lit 15187070238180564656979968) (nat_lit 884003834693027) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c288 Gram664ProofSharing.c291 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c293 := (@Enclosure.Real.IsNear.of_eq Gram664ProofSharing.c281 Gram664ProofSharing.c286 Bool.false (nat_lit 884003834693027) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c287 Gram664ProofSharing.c292)

noncomputable def Gram664ProofSharing.c294 := (@Enclosure.Real.IsNear.of_eq (Gram664ProofSharing.c254 : ℂ).im Gram664ProofSharing.c281 Bool.false (nat_lit 884003834693027) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c282 Gram664ProofSharing.c293)

noncomputable def Gram664ProofSharing.c295 := (@Enclosure.Complex.IsNear.of_parts Gram664ProofSharing.c254 Bool.false (nat_lit 56156915405352039) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884003834693027) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c277 Gram664ProofSharing.c294)

noncomputable def Gram664ProofSharing.c296 := (@Enclosure.Complex.IsNear.of_eq Gram664ProofSharing.c235 Gram664ProofSharing.c254 Bool.false (nat_lit 56156915405352039) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884003834693027) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c255 Gram664ProofSharing.c295)

noncomputable def Gram664ProofSharing.c297 := (@Enclosure.Complex.IsNear.re_isNear Gram664ProofSharing.c235 Bool.false (nat_lit 56156915405352039) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884003834693027) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c296)

noncomputable def Gram664ProofSharing.c298 := (@Enclosure.Complex.IsNear.im_isNear Gram664ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204052884) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c252)

noncomputable def Gram664ProofSharing.c299 := (@Enclosure.Complex.IsNear.im_isNear Gram664ProofSharing.c235 Bool.false (nat_lit 56156915405352039) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884003834693027) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c296)

noncomputable def Gram664ProofSharing.c300 := (↑Gram664ProofSharing.c8)

noncomputable def Gram664ProofSharing.c301 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c233 : ℂ).re (Gram664ProofSharing.c300 : ℂ).re)

noncomputable def Gram664ProofSharing.c302 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c233 : ℂ).im (Gram664ProofSharing.c300 : ℂ).im)

noncomputable def Gram664ProofSharing.c303 := (Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram664ProofSharing.c304 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram664ProofSharing.c305 := (@Enclosure.Complex.IsNear.mk Gram664ProofSharing.c256 Gram664ProofSharing.c303 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c261 Gram664ProofSharing.c304)

noncomputable def Gram664ProofSharing.c306 := (@Enclosure.Complex.IsNear.of_eq Gram664ProofSharing.c233 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) BSN.half_c_mk Gram664ProofSharing.c305)

noncomputable def Gram664ProofSharing.c307 := (@Enclosure.Complex.IsNear.re_isNear Gram664ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c306)

noncomputable def Gram664ProofSharing.c308 := (Complex.ofReal_re Gram664ProofSharing.c8)

noncomputable def Gram664ProofSharing.c309 := (@Enclosure.Real.IsNear.of_eq (Gram664ProofSharing.c300 : ℂ).re Gram664ProofSharing.c8 Bool.false (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) Gram664ProofSharing.c308 Zeta.Certificates.Gram.gp10_cert._proof_1)

noncomputable def Gram664ProofSharing.c310 := (@Enclosure.Real.IsNear.mulLit_ff (Gram664ProofSharing.c233 : ℂ).re (Gram664ProofSharing.c300 : ℂ).re (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram664ProofSharing.c307 Gram664ProofSharing.c309 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c311 := (@Enclosure.Complex.IsNear.im_isNear Gram664ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c306)

noncomputable def Gram664ProofSharing.c312 := (Complex.ofReal_im Gram664ProofSharing.c8)

noncomputable def Gram664ProofSharing.c313 := (@Eq.trans.{1} Real (Gram664ProofSharing.c300 : ℂ).im Gram664ProofSharing.c147 Gram664ProofSharing.c303 Gram664ProofSharing.c312 Enclosure.sfrac_zero_eq)

noncomputable def Gram664ProofSharing.c314 := (@Enclosure.Real.IsNear.of_eq (Gram664ProofSharing.c300 : ℂ).im Gram664ProofSharing.c303 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c313 Gram664ProofSharing.c304)

noncomputable def Gram664ProofSharing.c315 := (@Enclosure.Real.IsNear.mulLit_ff (Gram664ProofSharing.c233 : ℂ).im (Gram664ProofSharing.c300 : ℂ).im (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c311 Gram664ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c316 := (@Enclosure.Real.IsNear.subLit_ff_p Gram664ProofSharing.c301 Gram664ProofSharing.c302 (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram664ProofSharing.c310 Gram664ProofSharing.c315 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c317 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c233 : ℂ).re (Gram664ProofSharing.c300 : ℂ).im)

noncomputable def Gram664ProofSharing.c318 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c233 : ℂ).im (Gram664ProofSharing.c300 : ℂ).re)

noncomputable def Gram664ProofSharing.c319 := (@Enclosure.Real.IsNear.mulLit_ff (Gram664ProofSharing.c233 : ℂ).re (Gram664ProofSharing.c300 : ℂ).im (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c307 Gram664ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c320 := (@Enclosure.Real.IsNear.mulLit_ff (Gram664ProofSharing.c233 : ℂ).im (Gram664ProofSharing.c300 : ℂ).re (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c311 Gram664ProofSharing.c309 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c321 := (@Enclosure.Real.IsNear.addLit_ff Gram664ProofSharing.c317 Gram664ProofSharing.c318 (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c319 Gram664ProofSharing.c320 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c322 := (@Enclosure.Complex.IsNear.mul Gram664ProofSharing.c233 Gram664ProofSharing.c300 Bool.false (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c316 Gram664ProofSharing.c321)

noncomputable def Gram664ProofSharing.c323 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram664ProofSharing.c32 (nat_lit 2))

noncomputable def Gram664ProofSharing.c324 := (bernoulli Gram664ProofSharing.c323)

noncomputable def Gram664ProofSharing.c325 := (@Rat.cast.{0} Complex Complex.instRatCast Gram664ProofSharing.c324)

noncomputable def Gram664ProofSharing.c326 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2))

noncomputable def Gram664ProofSharing.c327 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c42 Gram664ProofSharing.c326)

noncomputable def Gram664ProofSharing.c328 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram664ProofSharing.c327 Gram664ProofSharing.c30)

noncomputable def Gram664ProofSharing.c329 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c327 Gram664ProofSharing.c328)

noncomputable def Gram664ProofSharing.c330 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram664ProofSharing.c28 Gram664ProofSharing.c325 Gram664ProofSharing.c329)

noncomputable def Gram664ProofSharing.c331 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 2))

noncomputable def Gram664ProofSharing.c332 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram664ProofSharing.c244 Gram664ProofSharing.c331)

noncomputable def Gram664ProofSharing.c333 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram664ProofSharing.c243 Gram664ProofSharing.c332)

noncomputable def Gram664ProofSharing.c334 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram664ProofSharing.c242 Gram664ProofSharing.c47 Gram664ProofSharing.c333)

noncomputable def Gram664ProofSharing.c335 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c330 Gram664ProofSharing.c334)

noncomputable def Gram664ProofSharing.c336 := (nat_lit 495176015714152109959649689600000000000)

noncomputable def Gram664ProofSharing.c337 := (nat_lit 259028914321541627628060815653149)

noncomputable def Gram664ProofSharing.c338 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram664ProofSharing.c32 (nat_lit 1))

noncomputable def Gram664ProofSharing.c339 := (bernoulli Gram664ProofSharing.c338)

noncomputable def Gram664ProofSharing.c340 := (@Rat.cast.{0} Complex Complex.instRatCast Gram664ProofSharing.c339)

noncomputable def Gram664ProofSharing.c341 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 1))

noncomputable def Gram664ProofSharing.c342 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c42 Gram664ProofSharing.c341)

noncomputable def Gram664ProofSharing.c343 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram664ProofSharing.c342 Gram664ProofSharing.c30)

noncomputable def Gram664ProofSharing.c344 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c342 Gram664ProofSharing.c343)

noncomputable def Gram664ProofSharing.c345 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram664ProofSharing.c28 Gram664ProofSharing.c340 Gram664ProofSharing.c344)

noncomputable def Gram664ProofSharing.c346 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 1))

noncomputable def Gram664ProofSharing.c347 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram664ProofSharing.c244 Gram664ProofSharing.c346)

noncomputable def Gram664ProofSharing.c348 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram664ProofSharing.c243 Gram664ProofSharing.c347)

noncomputable def Gram664ProofSharing.c349 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram664ProofSharing.c242 Gram664ProofSharing.c47 Gram664ProofSharing.c348)

noncomputable def Gram664ProofSharing.c350 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c345 Gram664ProofSharing.c349)

noncomputable def Gram664ProofSharing.c351 := (@Enclosure.Complex.IsNear.mk Gram664ProofSharing.c303 Gram664ProofSharing.c303 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c304 Gram664ProofSharing.c304)

noncomputable def Gram664ProofSharing.c352 := (BSN.stirling_coeff_mk (nat_lit 1) (nat_lit 1) (nat_lit 6) Bool.false BSN.bern_real_1 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c353 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram664ProofSharing.c354 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram664ProofSharing.c355 := (@Enclosure.Complex.IsNear.mk Gram664ProofSharing.c353 Gram664ProofSharing.c303 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c354 Gram664ProofSharing.c304)

noncomputable def Gram664ProofSharing.c356 := (@Enclosure.Complex.IsNear.of_eq Gram664ProofSharing.c345 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c352 Gram664ProofSharing.c355)

noncomputable def Gram664ProofSharing.c357 := (@Enclosure.Complex.IsNear.re_isNear Gram664ProofSharing.c345 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c356)

noncomputable def Gram664ProofSharing.c358 := (@Inv.inv.{0} Complex Complex.instInv Gram664ProofSharing.c50)

noncomputable def Gram664ProofSharing.c359 := (BSN.zpow_one_sub_two_mul Gram664ProofSharing.c47 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c360 := (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)

noncomputable def Gram664ProofSharing.c361 := (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring)

noncomputable def Gram664ProofSharing.c362 := (@MonoidWithZeroHom.{0, 0} Complex Real Gram664ProofSharing.c360 Gram664ProofSharing.c361)

noncomputable def Gram664ProofSharing.c363 := (@MonoidWithZeroHom.funLike.{0, 0} Complex Real Gram664ProofSharing.c360 Gram664ProofSharing.c361)

noncomputable def Gram664ProofSharing.c364 := (Enclosure.Complex.inv_re_eq_mul Gram664ProofSharing.c50)

noncomputable def Gram664ProofSharing.c365 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c50 : ℂ).re (Gram664ProofSharing.c50 : ℂ).re)

noncomputable def Gram664ProofSharing.c366 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c50 : ℂ).im (Gram664ProofSharing.c50 : ℂ).im)

noncomputable def Gram664ProofSharing.c367 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram664ProofSharing.c365 Gram664ProofSharing.c366)

noncomputable def Gram664ProofSharing.c368 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram664ProofSharing.c50)

noncomputable def Gram664ProofSharing.c369 := (@Enclosure.Real.IsNear.mulLit_ff (Gram664ProofSharing.c50 : ℂ).re (Gram664ProofSharing.c50 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c65 Gram664ProofSharing.c65 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c370 := (@Enclosure.Real.IsNear.mulLit_ff (Gram664ProofSharing.c50 : ℂ).im (Gram664ProofSharing.c50 : ℂ).im (nat_lit 204052884) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 204052884) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 2602348716794841) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c68 Gram664ProofSharing.c68 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c371 := (@Enclosure.Real.IsNear.addLit_ff Gram664ProofSharing.c365 Gram664ProofSharing.c366 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 2602348716794841) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) (nat_lit 41637589468717456) (nat_lit 2602349341794841) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c369 Gram664ProofSharing.c370 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c372 := (@Neg.neg.{0} Real Real.instNeg (Gram664ProofSharing.c50 : ℂ).im)

noncomputable def Gram664ProofSharing.c373 := (Enclosure.Complex.inv_im_eq_mul Gram664ProofSharing.c50)

noncomputable def Gram664ProofSharing.c374 := (@Enclosure.Real.IsNear.neg (Gram664ProofSharing.c50 : ℂ).im Bool.false (nat_lit 204052884) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c68)

noncomputable def Gram664ProofSharing.c375 := (@Enclosure.Complex.IsNear.im_isNear Gram664ProofSharing.c345 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c356)

noncomputable def Gram664ProofSharing.c376 := (nat_lit 12379400392853802748991242240000000000)

noncomputable def Gram664ProofSharing.c377 := (BSN.stirling_coeff_mk (nat_lit 2) (nat_lit 1) (nat_lit 30) Bool.true BSN.bern_real_2 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c378 := (Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram664ProofSharing.c379 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram664ProofSharing.c380 := (@Enclosure.Complex.IsNear.mk Gram664ProofSharing.c378 Gram664ProofSharing.c303 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c379 Gram664ProofSharing.c304)

noncomputable def Gram664ProofSharing.c381 := (@Enclosure.Complex.IsNear.of_eq Gram664ProofSharing.c330 { re := Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c377 Gram664ProofSharing.c380)

noncomputable def Gram664ProofSharing.c382 := (@Enclosure.Complex.IsNear.re_isNear Gram664ProofSharing.c330 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c381)

noncomputable def Gram664ProofSharing.c383 := (nat_lit 2331260228893874648652547340878341)

noncomputable def Gram664ProofSharing.c384 := (nat_lit 309485009821345068724781056000000000000000)

noncomputable def Gram664ProofSharing.c385 := (@Inv.inv.{0} Complex Complex.instInv Gram664ProofSharing.c48)

noncomputable def Gram664ProofSharing.c386 := (BSN.zpow_one_sub_two_mul Gram664ProofSharing.c47 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c387 := (Enclosure.Complex.inv_re_eq_mul Gram664ProofSharing.c48)

noncomputable def Gram664ProofSharing.c388 := (@Enclosure.Complex.IsNear.re_isNear Gram664ProofSharing.c48 Bool.true (nat_lit 7807045525384523) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 132754094559132260592861) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp10_cert._proof_2)

noncomputable def Gram664ProofSharing.c389 := (nat_lit 17623687715939926816547438410930982898829165321)

noncomputable def Gram664ProofSharing.c390 := (nat_lit 1000000000000000000000000000000)

noncomputable def Gram664ProofSharing.c391 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c48 : ℂ).re (Gram664ProofSharing.c48 : ℂ).re)

noncomputable def Gram664ProofSharing.c392 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c48 : ℂ).im (Gram664ProofSharing.c48 : ℂ).im)

noncomputable def Gram664ProofSharing.c393 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram664ProofSharing.c391 Gram664ProofSharing.c392)

noncomputable def Gram664ProofSharing.c394 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram664ProofSharing.c48)

noncomputable def Gram664ProofSharing.c395 := (nat_lit 60949959835426502757967007937529)

noncomputable def Gram664ProofSharing.c396 := (nat_lit 17623649622215029674983214681551021943204165321)

noncomputable def Gram664ProofSharing.c397 := (nat_lit 28197900345503882906475901457489572638126664513600000000000000000000)

noncomputable def Gram664ProofSharing.c398 := (@Enclosure.Real.IsNear.mulLit_tt (Gram664ProofSharing.c48 : ℂ).re (Gram664ProofSharing.c48 : ℂ).re (nat_lit 7807045525384523) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 7807045525384523) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c395 (nat_lit 1600000000000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c388 Gram664ProofSharing.c388 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c399 := (@Enclosure.Complex.IsNear.im_isNear Gram664ProofSharing.c48 Bool.true (nat_lit 7807045525384523) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 132754094559132260592861) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp10_cert._proof_2)

noncomputable def Gram664ProofSharing.c400 := (@Enclosure.Real.IsNear.mulLit_tt (Gram664ProofSharing.c48 : ℂ).im (Gram664ProofSharing.c48 : ℂ).im (nat_lit 132754094559132260592861) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 132754094559132260592861) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c396 Gram664ProofSharing.c390 (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c399 Gram664ProofSharing.c399 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c401 := (@Enclosure.Real.IsNear.addLit_ff Gram664ProofSharing.c391 Gram664ProofSharing.c392 Gram664ProofSharing.c395 (nat_lit 1600000000000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c396 Gram664ProofSharing.c390 (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c397 Gram664ProofSharing.c389 Gram664ProofSharing.c390 (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c398 Gram664ProofSharing.c400 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c402 := (@Neg.neg.{0} Real Real.instNeg (Gram664ProofSharing.c48 : ℂ).im)

noncomputable def Gram664ProofSharing.c403 := (Enclosure.Complex.inv_im_eq_mul Gram664ProofSharing.c48)

noncomputable def Gram664ProofSharing.c404 := (@Enclosure.Real.IsNear.neg (Gram664ProofSharing.c48 : ℂ).im Bool.true (nat_lit 132754094559132260592861) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c399)

noncomputable def Gram664ProofSharing.c405 := (@Enclosure.Complex.IsNear.im_isNear Gram664ProofSharing.c330 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c381)

noncomputable def Gram664ProofSharing.c406 := (BSN.logSumC Gram664ProofSharing.c39 (nat_lit 0))

noncomputable def Gram664ProofSharing.c407 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram664ProofSharing.c106)

noncomputable def Gram664ProofSharing.c408 := (@Monoid.toNPow.{0} Real Real.instMonoid)

noncomputable def Gram664ProofSharing.c409 := (@NPow.toPow.{0} Real Gram664ProofSharing.c408)

noncomputable def Gram664ProofSharing.c410 := (@instHPow.{0, 0} Real Nat Gram664ProofSharing.c409)

noncomputable def Gram664ProofSharing.c411 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram664ProofSharing.c410 Gram664ProofSharing.c7 (nat_lit 4))

noncomputable def Gram664ProofSharing.c412 := (@Inv.inv.{0} Real Real.instInv Gram664ProofSharing.c411)

noncomputable def Gram664ProofSharing.c413 := (nat_lit 611446774371975769155682509262542103857872115376664175900625)

noncomputable def Gram664ProofSharing.c414 := (nat_lit 392318858461667547739736838950479151006397215279002157056)

noncomputable def Gram664ProofSharing.c415 := (nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047)

noncomputable def Gram664ProofSharing.c416 := (nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram664ProofSharing.c417 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram664ProofSharing.c410 Gram664ProofSharing.c7 (nat_lit 3))

noncomputable def Gram664ProofSharing.c418 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram664ProofSharing.c417 Gram664ProofSharing.c7)

noncomputable def Gram664ProofSharing.c419 := (BSN.pow_succ_r Gram664ProofSharing.c7 (nat_lit 3) (nat_lit 4) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c420 := (nat_lit 691463075802508163054686763366652189853178875)

noncomputable def Gram664ProofSharing.c421 := (nat_lit 2787593149816327892691964784081045188247552)

noncomputable def Gram664ProofSharing.c422 := (nat_lit 2184744797947834540264818678394244808492865883128339)

noncomputable def Gram664ProofSharing.c423 := (nat_lit 9223372036854775808000000000000000000000000000000000000000000000)

noncomputable def Gram664ProofSharing.c424 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram664ProofSharing.c410 Gram664ProofSharing.c7 (nat_lit 2))

noncomputable def Gram664ProofSharing.c425 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram664ProofSharing.c424 Gram664ProofSharing.c7)

noncomputable def Gram664ProofSharing.c426 := (BSN.pow_succ_r Gram664ProofSharing.c7 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c427 := (nat_lit 1073741824000000000000000000000000000000)

noncomputable def Gram664ProofSharing.c428 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram664ProofSharing.c410 Gram664ProofSharing.c7 (nat_lit 1))

noncomputable def Gram664ProofSharing.c429 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram664ProofSharing.c428 Gram664ProofSharing.c7)

noncomputable def Gram664ProofSharing.c430 := (BSN.pow_succ_r Gram664ProofSharing.c7 (nat_lit 1) (nat_lit 2) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c431 := (BSN.pow_one_r Gram664ProofSharing.c7)

noncomputable def Gram664ProofSharing.c432 := (@Enclosure.Real.IsNear.of_eq Gram664ProofSharing.c7 Gram664ProofSharing.c10 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) BSN.two_pi_eq Gram664ProofSharing.c13)

noncomputable def Gram664ProofSharing.c433 := (@Enclosure.Real.IsNear.of_eq Gram664ProofSharing.c428 Gram664ProofSharing.c7 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram664ProofSharing.c431 Gram664ProofSharing.c432)

noncomputable def Gram664ProofSharing.c434 := (@Enclosure.Real.IsNear.mulLit_ff Gram664ProofSharing.c428 Gram664ProofSharing.c7 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram664ProofSharing.c427 Gram664ProofSharing.c433 Gram664ProofSharing.c432 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c435 := (@Enclosure.Real.IsNear.of_eq Gram664ProofSharing.c424 Gram664ProofSharing.c429 Bool.false (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram664ProofSharing.c427 Gram664ProofSharing.c430 Gram664ProofSharing.c434)

noncomputable def Gram664ProofSharing.c436 := (@Enclosure.Real.IsNear.mulLit_ff Gram664ProofSharing.c424 Gram664ProofSharing.c7 (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram664ProofSharing.c427 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram664ProofSharing.c420 Gram664ProofSharing.c421 Gram664ProofSharing.c422 Gram664ProofSharing.c423 Gram664ProofSharing.c435 Gram664ProofSharing.c432 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c437 := (@Enclosure.Real.IsNear.of_eq Gram664ProofSharing.c417 Gram664ProofSharing.c425 Bool.false Gram664ProofSharing.c420 Gram664ProofSharing.c421 Gram664ProofSharing.c422 Gram664ProofSharing.c423 Gram664ProofSharing.c426 Gram664ProofSharing.c436)

noncomputable def Gram664ProofSharing.c438 := (@Enclosure.Real.IsNear.mulLit_ff Gram664ProofSharing.c417 Gram664ProofSharing.c7 Gram664ProofSharing.c420 Gram664ProofSharing.c421 Gram664ProofSharing.c422 Gram664ProofSharing.c423 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram664ProofSharing.c413 Gram664ProofSharing.c414 Gram664ProofSharing.c415 Gram664ProofSharing.c416 Gram664ProofSharing.c437 Gram664ProofSharing.c432 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c439 := (@Enclosure.Real.IsNear.of_eq Gram664ProofSharing.c411 Gram664ProofSharing.c418 Bool.false Gram664ProofSharing.c413 Gram664ProofSharing.c414 Gram664ProofSharing.c415 Gram664ProofSharing.c416 Gram664ProofSharing.c419 Gram664ProofSharing.c438)

noncomputable def Gram664ProofSharing.c440 := (@Enclosure.Real.IsNear.inv_image Gram664ProofSharing.c411 Gram664ProofSharing.c413 Gram664ProofSharing.c414 Gram664ProofSharing.c415 Gram664ProofSharing.c416 (nat_lit 5511507) (nat_lit 5511508) (nat_lit 8589934592) Gram664ProofSharing.c439 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c441 := (@Enclosure.Real.IsNear.recentre' Gram664ProofSharing.c412 Bool.false (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) Gram664ProofSharing.c440 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c442 := (nat_lit 22124138910779071789454747655684077697)

noncomputable def Gram664ProofSharing.c443 := (nat_lit 792281625142643375935439503360000000000000)

noncomputable def Gram664ProofSharing.c444 := (nat_lit 32898757773192161031664603632893922944713)

noncomputable def Gram664ProofSharing.c445 := (nat_lit 210449806678514646732851118080000000000000000000)

noncomputable def Gram664ProofSharing.c446 := (nat_lit 2773902497081511883387320599056)

noncomputable def Gram664ProofSharing.c447 := (riemannSiegelThetaApproximant (nat_lit 2) (nat_lit 0) Gram664ProofSharing.c107)

noncomputable def Gram664ProofSharing.c448 := (nat_lit 1652713374517353252284131126465947655684077697)

noncomputable def Gram664ProofSharing.c449 := (nat_lit 32898618034520526497939173019751517824713)

noncomputable def Gram664ProofSharing.c450 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram664ProofSharing.c112)

noncomputable def Gram664ProofSharing.c451 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram664ProofSharing.c15 Gram664ProofSharing.c107 Gram664ProofSharing.c6)

noncomputable def Gram664ProofSharing.c452 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram664ProofSharing.c451 (Real.log Real.pi))

noncomputable def Gram664ProofSharing.c453 := (nat_lit 2115377007429997467838160434164295687684077697)

noncomputable def Gram664ProofSharing.c454 := (nat_lit 7902565507714386078629605019751517824713)

noncomputable def Gram664ProofSharing.c455 := (nat_lit 571835758664676004849132734361680174580771)

noncomputable def Gram664ProofSharing.c456 := (nat_lit 713053462628379038341895553024000000000)

noncomputable def Gram664ProofSharing.c457 := (nat_lit 8896640590023780880090504602664769470411)

noncomputable def Gram664ProofSharing.c458 := (nat_lit 118378016256664488787228753920000000000000000000)

noncomputable def Gram664ProofSharing.c459 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram664ProofSharing.c112 Gram664ProofSharing.c233)

noncomputable def Gram664ProofSharing.c460 := (Complex.log Gram664ProofSharing.c112)

noncomputable def Gram664ProofSharing.c461 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c459 Gram664ProofSharing.c460)

noncomputable def Gram664ProofSharing.c462 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram664ProofSharing.c461 Gram664ProofSharing.c112)

noncomputable def Gram664ProofSharing.c463 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram664ProofSharing.c462 Gram664ProofSharing.c238)

noncomputable def Gram664ProofSharing.c464 := (nat_lit 57084131894450675922716369419229)

noncomputable def Gram664ProofSharing.c465 := (nat_lit 129424212246534877179938707448315922303)

noncomputable def Gram664ProofSharing.c466 := (BSN.w_sub_half_zero_mk Gram664ProofSharing.c107 Bool.false (nat_lit 102026445) (nat_lit 100000) Gram664ProofSharing.c121 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c467 := (@Enclosure.Complex.IsNear.mk Gram664ProofSharing.c249 Gram664ProofSharing.c123 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204052890) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c250 Gram664ProofSharing.c124)

noncomputable def Gram664ProofSharing.c468 := (@Enclosure.Complex.IsNear.of_eq Gram664ProofSharing.c459 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204052890) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204052890) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c466 Gram664ProofSharing.c467)

noncomputable def Gram664ProofSharing.c469 := (@Enclosure.Complex.IsNear.re_isNear Gram664ProofSharing.c459 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204052890) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c468)

noncomputable def Gram664ProofSharing.c470 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204052890) (nat_lit 400000) })

noncomputable def Gram664ProofSharing.c471 := (@congrArg.{1, 1} Complex Complex Gram664ProofSharing.c112 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204052890) (nat_lit 400000) } Complex.log Gram664ProofSharing.c122)

noncomputable def Gram664ProofSharing.c472 := (Enclosure.sfrac Bool.false (nat_lit 41637591917352100) (nat_lit 160000000000))

noncomputable def Gram664ProofSharing.c473 := (Real.log Gram664ProofSharing.c472)

noncomputable def Gram664ProofSharing.c474 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram664ProofSharing.c256 Gram664ProofSharing.c473)

noncomputable def Gram664ProofSharing.c475 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 204052890) (nat_lit 400000) (nat_lit 41637591917352100) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c476 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41637591917352100))

noncomputable def Gram664ProofSharing.c477 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram664ProofSharing.c15 Gram664ProofSharing.c476 Gram664ProofSharing.c263)

noncomputable def Gram664ProofSharing.c478 := (Real.log Gram664ProofSharing.c477)

noncomputable def Gram664ProofSharing.c479 := (nat_lit 11776921850265387797271936437426171601552795415212586439517957022964551816629291116036341287852818661138707470439091180807258513582684469620734138848391122663443491024212012141482868585245948131140482706855343794113562116094495450465909277348256821506827834953697033518353302006973010322223617984314239905750000000000000000000000000000000000000000)

noncomputable def Gram664ProofSharing.c480 := (nat_lit 458050783380652424968158068263128492396188177013572166044305479225641005813020743539727649431539634386589381330208397045638139808963038436101282975815427120707147566257197659734348830697928839575267555161777575748630590141376912910020008687130139060645176014145317447581504535328261340148857367078718593200000000000000000000000000000000000000000)

noncomputable def Gram664ProofSharing.c481 := (nat_lit 132196621178049027514116461259311239882237507708819759123041636303698034040324744318555842207322571645847275701697039803945000301062277509098161061815436592201745151406864566926430968943341944815321091510021450397175376369637042401882808583742139514796661026985385437941982086205492562300678090750000000000000000000000000000000000000000)

noncomputable def Gram664ProofSharing.c482 := (BSN.artanhP (nat_lit 20666071917352100))

noncomputable def Gram664ProofSharing.c483 := (BSN.artanhQ (nat_lit 62609111917352100))

noncomputable def Gram664ProofSharing.c484 := (@BSN.binarySplit_of_base10 Gram664ProofSharing.c482 Gram664ProofSharing.c483 (nat_lit 0) (nat_lit 10) Gram664ProofSharing.c480 Gram664ProofSharing.c479 Gram664ProofSharing.c481 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c485 := (BSN.log_dyadic_bound (nat_lit 20666071917352100) (nat_lit 62609111917352100) (nat_lit 11) (nat_lit 10) Gram664ProofSharing.c479 (nat_lit 17179869184) (nat_lit 6800000000) Gram664ProofSharing.c480 Gram664ProofSharing.c481 (nat_lit 11782608569) (nat_lit 83275183834704200) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram664ProofSharing.c484 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c486 := (BSN.log_rat_reduce_isNear (nat_lit 41637591917352100) (nat_lit 160000000000) (nat_lit 17) (nat_lit 83275183834704200) (nat_lit 41943040000000000) (nat_lit 11782608569) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6800000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram664ProofSharing.c485 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c487 := (@Enclosure.Real.IsNear.recentre' Gram664ProofSharing.c478 Bool.false (nat_lit 7718147719916303897054937088) (nat_lit 618970019642690137449562112) (nat_lit 1000115600000000) (nat_lit 6800000000000000000000000) (nat_lit 56156915670117479) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Gram664ProofSharing.c486 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c488 := (BSN.isNear_log_sfrac (nat_lit 41637591917352100) (nat_lit 160000000000) (nat_lit 56156915670117479) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Bool.false Gram664ProofSharing.c487)

noncomputable def Gram664ProofSharing.c489 := (@Enclosure.Real.IsNear.mulLit_ff Gram664ProofSharing.c256 Gram664ProofSharing.c473 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56156915670117479) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) (nat_lit 56156915670117479) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram664ProofSharing.c261 Gram664ProofSharing.c488 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c490 := (@Enclosure.Real.IsNear.of_eq (Gram664ProofSharing.c470 : ℂ).re Gram664ProofSharing.c474 Bool.false (nat_lit 56156915670117479) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram664ProofSharing.c475 Gram664ProofSharing.c489)

noncomputable def Gram664ProofSharing.c491 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 204052890))

noncomputable def Gram664ProofSharing.c492 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram664ProofSharing.c15 Gram664ProofSharing.c491 Gram664ProofSharing.c279)

noncomputable def Gram664ProofSharing.c493 := (Real.arctan Gram664ProofSharing.c492)

noncomputable def Gram664ProofSharing.c494 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 204052890) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c495 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram664ProofSharing.c15 Gram664ProofSharing.c279 Gram664ProofSharing.c491)

noncomputable def Gram664ProofSharing.c496 := (Real.arctan Gram664ProofSharing.c495)

noncomputable def Gram664ProofSharing.c497 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram664ProofSharing.c283 Gram664ProofSharing.c496)

noncomputable def Gram664ProofSharing.c498 := (BSN.arctan_recip (nat_lit 204052890) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c499 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 204052890)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c500 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 204052890)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c501 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 204052890) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6800000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8419320) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram664ProofSharing.c499 Gram664ProofSharing.c500 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c502 := (@Enclosure.Real.IsNear.subLit_ff_p Gram664ProofSharing.c283 Gram664ProofSharing.c496 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8419320) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6800000000) (nat_lit 15187070238743514610401280) (nat_lit 884003834725795) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c288 Gram664ProofSharing.c501 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c503 := (@Enclosure.Real.IsNear.of_eq Gram664ProofSharing.c493 Gram664ProofSharing.c497 Bool.false (nat_lit 884003834725795) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c498 Gram664ProofSharing.c502)

noncomputable def Gram664ProofSharing.c504 := (@Enclosure.Real.IsNear.of_eq (Gram664ProofSharing.c470 : ℂ).im Gram664ProofSharing.c493 Bool.false (nat_lit 884003834725795) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c494 Gram664ProofSharing.c503)

noncomputable def Gram664ProofSharing.c505 := (@Enclosure.Complex.IsNear.of_parts Gram664ProofSharing.c470 Bool.false (nat_lit 56156915670117479) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884003834725795) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c490 Gram664ProofSharing.c504)

noncomputable def Gram664ProofSharing.c506 := (@Enclosure.Complex.IsNear.of_eq Gram664ProofSharing.c460 Gram664ProofSharing.c470 Bool.false (nat_lit 56156915670117479) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884003834725795) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c471 Gram664ProofSharing.c505)

noncomputable def Gram664ProofSharing.c507 := (@Enclosure.Complex.IsNear.re_isNear Gram664ProofSharing.c460 Bool.false (nat_lit 56156915670117479) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884003834725795) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c506)

noncomputable def Gram664ProofSharing.c508 := (@Enclosure.Complex.IsNear.im_isNear Gram664ProofSharing.c459 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204052890) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c468)

noncomputable def Gram664ProofSharing.c509 := (@Enclosure.Complex.IsNear.im_isNear Gram664ProofSharing.c460 Bool.false (nat_lit 56156915670117479) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884003834725795) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram664ProofSharing.c506)

noncomputable def Gram664ProofSharing.c510 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram664ProofSharing.c242 Gram664ProofSharing.c112 Gram664ProofSharing.c333)

noncomputable def Gram664ProofSharing.c511 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c330 Gram664ProofSharing.c510)

noncomputable def Gram664ProofSharing.c512 := (nat_lit 16577849054349365188600315922303)

noncomputable def Gram664ProofSharing.c513 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram664ProofSharing.c242 Gram664ProofSharing.c112 Gram664ProofSharing.c348)

noncomputable def Gram664ProofSharing.c514 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram664ProofSharing.c345 Gram664ProofSharing.c513)

noncomputable def Gram664ProofSharing.c515 := (@Inv.inv.{0} Complex Complex.instInv Gram664ProofSharing.c115)

noncomputable def Gram664ProofSharing.c516 := (BSN.zpow_one_sub_two_mul Gram664ProofSharing.c112 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c517 := (Enclosure.Complex.inv_re_eq_mul Gram664ProofSharing.c115)

noncomputable def Gram664ProofSharing.c518 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c115 : ℂ).re (Gram664ProofSharing.c115 : ℂ).re)

noncomputable def Gram664ProofSharing.c519 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c115 : ℂ).im (Gram664ProofSharing.c115 : ℂ).im)

noncomputable def Gram664ProofSharing.c520 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram664ProofSharing.c518 Gram664ProofSharing.c519)

noncomputable def Gram664ProofSharing.c521 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram664ProofSharing.c115)

noncomputable def Gram664ProofSharing.c522 := (@Enclosure.Real.IsNear.mulLit_ff (Gram664ProofSharing.c115 : ℂ).re (Gram664ProofSharing.c115 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c128 Gram664ProofSharing.c128 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c523 := (@Enclosure.Real.IsNear.mulLit_ff (Gram664ProofSharing.c115 : ℂ).im (Gram664ProofSharing.c115 : ℂ).im (nat_lit 204052890) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 204052890) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 416375819173521) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c131 Gram664ProofSharing.c131 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c524 := (@Enclosure.Real.IsNear.addLit_ff Gram664ProofSharing.c518 Gram664ProofSharing.c519 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 416375819173521) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) (nat_lit 6662014706776336) (nat_lit 416375919173521) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c522 Gram664ProofSharing.c523 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c525 := (@Neg.neg.{0} Real Real.instNeg (Gram664ProofSharing.c115 : ℂ).im)

noncomputable def Gram664ProofSharing.c526 := (Enclosure.Complex.inv_im_eq_mul Gram664ProofSharing.c115)

noncomputable def Gram664ProofSharing.c527 := (@Enclosure.Real.IsNear.neg (Gram664ProofSharing.c115 : ℂ).im Bool.false (nat_lit 204052890) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c131)

noncomputable def Gram664ProofSharing.c528 := (nat_lit 1980704062856608439838598758400000000)

noncomputable def Gram664ProofSharing.c529 := (nat_lit 149200641489144286697402843300727)

noncomputable def Gram664ProofSharing.c530 := (nat_lit 19807040628566084398385987584000000000000)

noncomputable def Gram664ProofSharing.c531 := (@Inv.inv.{0} Complex Complex.instInv Gram664ProofSharing.c113)

noncomputable def Gram664ProofSharing.c532 := (BSN.zpow_one_sub_two_mul Gram664ProofSharing.c112 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c533 := (Enclosure.Complex.inv_re_eq_mul Gram664ProofSharing.c113)

noncomputable def Gram664ProofSharing.c534 := (@Enclosure.Complex.IsNear.re_isNear Gram664ProofSharing.c113 Bool.true (nat_lit 1249127357520563) (nat_lit 6400000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 8496262801260737152569) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp10_cert._proof_6)

noncomputable def Gram664ProofSharing.c535 := (nat_lit 72186637620002478971931091931051486883299761)

noncomputable def Gram664ProofSharing.c536 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c113 : ℂ).re (Gram664ProofSharing.c113 : ℂ).re)

noncomputable def Gram664ProofSharing.c537 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram664ProofSharing.c113 : ℂ).im (Gram664ProofSharing.c113 : ℂ).im)

noncomputable def Gram664ProofSharing.c538 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram664ProofSharing.c536 Gram664ProofSharing.c537)

noncomputable def Gram664ProofSharing.c539 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram664ProofSharing.c113)

noncomputable def Gram664ProofSharing.c540 := (nat_lit 1560319155306304417954967836969)

noncomputable def Gram664ProofSharing.c541 := (nat_lit 72186481588086948341489296434267789983299761)

noncomputable def Gram664ProofSharing.c542 := (nat_lit 2956764676915301538690297525495868902739958210560000000000000000)

noncomputable def Gram664ProofSharing.c543 := (@Enclosure.Real.IsNear.mulLit_tt (Gram664ProofSharing.c113 : ℂ).re (Gram664ProofSharing.c113 : ℂ).re (nat_lit 1249127357520563) (nat_lit 6400000000) (nat_lit 0) (nat_lit 1) (nat_lit 1249127357520563) (nat_lit 6400000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c540 (nat_lit 40960000000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c534 Gram664ProofSharing.c534 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c544 := (@Enclosure.Complex.IsNear.im_isNear Gram664ProofSharing.c113 Bool.true (nat_lit 1249127357520563) (nat_lit 6400000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 8496262801260737152569) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp10_cert._proof_6)

noncomputable def Gram664ProofSharing.c545 := (@Enclosure.Real.IsNear.mulLit_tt (Gram664ProofSharing.c113 : ℂ).im (Gram664ProofSharing.c113 : ℂ).im (nat_lit 8496262801260737152569) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 8496262801260737152569) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c541 (nat_lit 4096000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c544 Gram664ProofSharing.c544 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c546 := (@Enclosure.Real.IsNear.addLit_ff Gram664ProofSharing.c536 Gram664ProofSharing.c537 Gram664ProofSharing.c540 (nat_lit 40960000000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c541 (nat_lit 4096000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c542 Gram664ProofSharing.c535 (nat_lit 4096000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c543 Gram664ProofSharing.c545 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram664ProofSharing.c547 := (@Neg.neg.{0} Real Real.instNeg (Gram664ProofSharing.c113 : ℂ).im)

noncomputable def Gram664ProofSharing.c548 := (Enclosure.Complex.inv_im_eq_mul Gram664ProofSharing.c113)

noncomputable def Gram664ProofSharing.c549 := (@Enclosure.Real.IsNear.neg (Gram664ProofSharing.c113 : ℂ).im Bool.true (nat_lit 8496262801260737152569) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) Gram664ProofSharing.c544)

noncomputable def Gram664ProofSharing.c550 := (BSN.logSumC Gram664ProofSharing.c107 (nat_lit 0))

noncomputable def Gram664ProofSharing.c551 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram664ProofSharing.c144)


